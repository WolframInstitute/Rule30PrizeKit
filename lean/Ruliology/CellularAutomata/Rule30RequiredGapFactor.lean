module

public import Ruliology.CellularAutomata.Rule30Certificates.RequiredGapFactor

/-!
The compulsory (12, 10, 9) factor for finite-left Rule 30 columns, including cyclic and rotated words.
-/

@[expose] public section

-- Keep independent kernel checks sequential so their peak allocations do not overlap.
set_option Elab.async false

open Ruliology.CellularAutomata.Rule30RequiredGapLogic Ruliology.CellularAutomata.Rule30Certificates.RequiredGapFactor


section
namespace Ruliology.CellularAutomata.Rule30RequiredGapFactor
open Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond
private theorem data_for (i j:Fin 6) (h:(F i.val).testBit j.val=true) :
    ((B i.val).testBit j.val=true → color i=color j) ∧
    ∀ {q k l:Nat}, k∈dest i.val q → l∈dest j.val q →
    (F k).testBit l=true ∧ ((B k).testBit l=true→(B i.val).testBit j.val=true) :=by
  have row:=pair_data i.val i.isLt
  simp only [rowCheck,Bool.and_eq_true] at row
  have z:=List.all_eq_true.mp row.2 j.val (List.mem_range.mpr j.isLt)
  simp only [pairCheck,h,Bool.not_true,Bool.false_or,Bool.and_eq_true] at z
  refine ⟨fun hb=>?_,?_⟩
  · have eq:=z.1;rw [hb] at eq;exact beq_iff_eq.mp eq
  · intro q k l hk hl
    have legal:q∈alphabet:=by
      by_cases a9:q=9;·simp [alphabet,a9]
      by_cases a10:q=10;·simp [alphabet,a10]
      by_cases a11:q=11;·simp [alphabet,a11]
      by_cases a12:q=12;·simp [alphabet,a12]
      by_cases a13:q=13;·simp [alphabet,a13]
      by_cases a14:q=14;·simp [alphabet,a14]
      by_cases a15:q=15;·simp [alphabet,a15]
      by_cases a16:q=16;·simp [alphabet,a16]
      simp [dest,a9,a10,a11,a12,a13,a14,a15,a16] at hk
    have d:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp z.2 q legal) k hk) l hl
    rw [Bool.and_eq_true] at d
    refine ⟨d.1,fun hb=>?_⟩
    have s:=d.2;simpa only [hb,Bool.not_true,Bool.false_or] using s

theorem safe : MixedNoDiamond edge color :=by
  apply safe_of_squares
  intro a _
  refine ⟨{F:=fun u v=>(F u.val).testBit v.val=true
           B:=fun u v=>¬(F u.val).testBit v.val=true ∨ (B u.val).testBit v.val=true
           diagF:=?_,diagB:=?_,forward:=?_,backward:=?_,agree:=?_}⟩
  · intro u _;have z:=pair_data u.val u.isLt;simp only [rowCheck,Bool.and_eq_true] at z;exact z.1.1
  · intro u _;right;have z:=pair_data u.val u.isLt;simp only [rowCheck,Bool.and_eq_true] at z;exact z.1.2
  · intro u v i j q _ _ _ _ a b f;exact ((data_for u v f).2 a b).1
  · intro u v i j q _ _ _ _ a b h
    by_cases f:(F u.val).testBit v.val=true
    · obtain ⟨g,s⟩:=(data_for u v f).2 a b
      exact Or.inr (s (h.resolve_left (fun ng=>ng g)))
    · exact Or.inl f
  · intro u v _ _ f b;exact (data_for u v f).1 (b.resolve_left (fun ng=>ng f))
end Ruliology.CellularAutomata.Rule30RequiredGapFactor

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapFactor
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30ResetMixtures Rule30Realization Rule30StripCertificates
structure Coverage : Prop where
  warmStep : ∀i h,i<7→h<3→Physical (warm i h) h (fun q=>warm (i+1) (next h q))
  upperStep : ∀i h,i<4→h<3→Physical (upper i h) h (fun q=>upper i (next h q))
  groupStep : ∀i h,i<6→h<3→Physical (group i h) h (out i h)
theorem apply_at {x j s q src dst} (drive:Fitted x j s q) (n:Nat)
    (good:Supported (state q n) (q n)) (go:Physical src (state q n) dst) (h:src.testBit (samples x j s 19 q n)=true) :
    (dst (q n)).testBit (samples x j s 19 q (n+1))=true :=by
  have fit:Driven x j (s+stamp q n) (driver (q n)):=by
    intro i hi;rw [driver_length] at hi
    rw [Nat.add_assoc,drive,clock_at q n i (by omega)]
    cases i with
    | zero=>rfl
    | succ t=>simp [driver,List.getD_eq_getElem?_getD,show t<q n by omega]
  have hit:=go x j (q n) good (s+stamp q n) h fit
  simpa only [atSet,samples,stamp,driver_length,Nat.add_assoc] using hit
theorem settled (c:Coverage) {x j s q} (drive:Fitted x j s q) (allowed:∀n,Supported (state q n) (q n))
    (i:Nat) (idx:i<4) (n:Nat) (atN:(upper i (state q n)).testBit (samples x j s 19 q n)=true) (k:Nat) (hk:n≤k) :
    (upper i (state q k)).testBit (samples x j s 19 q k)=true :=by
  obtain ⟨u,rfl⟩:=Nat.exists_eq_add_of_le hk
  induction u with
  |zero=>exact atN
  |succ u ih=>
    have step:=apply_at drive (n+u) (allowed _) (c.upperStep i _ idx (state_bound q _)) (ih (by omega))
    rw [show n+(u+1)=(n+u)+1 by omega]
    exact step
theorem hot_stream (c:Coverage) {x lo j s q p} (black:x lo=true) (left:∀i,i<lo→x i=false)
    (drive:Fitted x j s q) (allowed:∀n,Supported (state q n) (q n)) (pos:0<p) (per:∀n,q (n+p)=q n) :
    (∀n,¬(upper 1 (state q n)).testBit (samples x j s 19 q n)=true) ∧
    ∀n,∃i:Fin 6,(group i.val (state q (7+n))).testBit (samples x j s 19 q (7+n))=true :=by
  let z:=samples x j s 19 q
  have range (n:Nat):9≤q n ∧ q n≤16:=legal_range (allowed n)
  have size (n:Nat):z n<2^19:=(Rule30FiniteStrips.enc_encRow (x:=x) 19 _ j).1
  have below (k:Nat) (hk:k≤3) : ∀n,¬(upper (4-k) (state q n)).testBit (z n)=true :=by
    induction k with
    |zero=>
      intro n;change ¬(upper 4 (state q n)).testBit (z n)=true
      rw [(level_data _ (state_bound q n)).2.2.1];simp
    |succ k ih=>
      let i:=4-(k+1)
      have lo:1≤i:=by dsimp [i];omega
      have hi:i≤3:=by dsimp [i];omega
      have after:i+1=4-k:=by dsimp [i];omega
      intro n here
      have stays (t:Nat) (ht:n≤t) : pulseColor (z t)=bandColor i:=by
        apply uniform (state_bound q t) lo hi (size t) (settled c drive allowed i (by omega) n here t ht)
        rw [after];exact ih (by omega) t
      exact no_sample_period (W:=19) (by decide) black left range drive pos per n
        (fun t ht=>(stays (t+p) (by omega)).trans (stays t ht).symm)
  have missing:∀n,¬(upper 1 (state q n)).testBit (z n)=true:=below 3 (by decide)
  refine ⟨missing,?_⟩
  have warmup (n:Nat) (hn:n≤7):(warm n (state q n)).testBit (z n)=true:=by
    induction n with
    |zero=>
      rw [(level_data _ (state_bound q 0)).1,Rule30FastImage.testBit_fullSet]
      exact decide_eq_true (size 0)
    |succ n ih=>exact apply_at drive n (allowed _) (c.warmStep n _ (by omega) (state_bound q n)) (ih (by omega))
  have seven: (upper 0 (state q 7)).testBit (z 7)=true:=by rw [←(level_data _ (state_bound q 7)).2.1];exact warmup _ (by decide)
  intro n;exact hot (state_bound q _) (settled c drive allowed 0 (by decide) 7 seven (7+n) (by omega)) (missing _)
end Ruliology.CellularAutomata.Rule30RequiredGapFactor

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapFactor
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30ResetMixtures Rule30Realization Rule30StripCertificates

theorem no_avoiding (c:Coverage) {x:Int→Bool} {lo j:Int} {s p:Nat} {q:Nat→Nat}
    (black:x lo=true) (left:∀i,i<lo→x i=false) (range:∀n,9≤q n ∧ q n≤16) (pos:0<p)
    (per:∀n,q (n+p)=q n) (avoid:∀n,¬(q n=12 ∧ q (n+1)=10 ∧ q (n+2)=9)) : ¬Fitted x j s q :=by
  classical
  intro drive
  have allowed:=supported_state range avoid
  let z:=samples x j s 19 q
  obtain ⟨no,selected⟩:=hot_stream c black left drive allowed pos per
  let v:=fun n=>(selected n).choose
  have member (n:Nat) : (group (v n).val (state q (7+n))).testBit (z (7+n))=true:=(selected n).choose_spec
  have colorAt (n:Nat):color (v n)=pulseColor (z (7+n)):=
    (group_color (v n) (state_bound q _) (Rule30FiniteStrips.enc_encRow (x:=x) 19 _ j).1 (member n)).symm
  have path (n:Nat):edge (v n) (q (7+n)) (v (n+1)) :=by
    apply child_of_out _ _ (state q (7+n)) _ (z (7+n+1)) (range_alphabet (range _)) (state_bound q (7+n+1))
    · exact apply_at drive (7+n) (allowed _) (c.groupStep (v n).val _ (v n).isLt (state_bound q _)) (member n)
    · exact no (7+n+1)
    · have y:=member (n+1)
      rw [show 7+(n+1)=(7+n)+1 by omega] at y
      exact y
  have period (n:Nat) (_:0≤n):q (7+(n+p))=q (7+n):=by rw [←Nat.add_assoc,per]
  have cover (n:Nat):v (0+n*p)∈List.finRange 6:=by simp
  obtain ⟨S,d,_,hd,_,periodic⟩:=Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond.output_bound color safe v (fun n=>q (7+n)) path pos period _ cover
  apply no_sample_period (W:=19) (by decide) black left range drive (Nat.mul_pos hd pos) (label_mul q p per d) (7+S)
  intro n hn;obtain ⟨u,rfl⟩:=Nat.exists_eq_add_of_le (show 7≤n by omega)
  have same:=periodic u (by omega);simpa only [colorAt,Nat.add_assoc] using same

theorem recurrent_factor (c:Coverage) {x:Int→Bool} {lo j:Int} {s p:Nat} {q:Nat→Nat}
    (black:x lo=true) (left:∀i,i<lo→x i=false) (range:∀n,9≤q n ∧ q n≤16) (pos:0<p)
    (per:∀n,q (n+p)=q n) (fit:Fitted x j s q) (N:Nat) :
    ∃n,N≤n ∧ q n=12 ∧ q (n+1)=10 ∧ q (n+2)=9 :=by
  classical
  have exists0:∃n,q n=12 ∧ q (n+1)=10 ∧ q (n+2)=9:=by
    apply Classical.byContradiction;intro no
    exact no_avoiding c black left range pos per (fun n match_=>no ⟨n,match_⟩) fit
  obtain ⟨n,a,b,d⟩:=exists0
  have lower:N≤N*p:=by simpa using Nat.mul_le_mul_left N pos
  have shift:=label_mul q p per N
  refine ⟨n+N*p,by omega,(shift n).trans a,?_,?_⟩
  · rw [show n+N*p+1=n+1+N*p by omega,shift,b]
  · rw [show n+N*p+2=n+2+N*p by omega,shift,d]
end Ruliology.CellularAutomata.Rule30RequiredGapFactor

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapFactor
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30Realization Rule30ResetMixtures
def HasCyclicTriple (qs:List Nat) := ∃i,i<qs.length ∧ letters qs i=12 ∧ letters qs (i+1)=10 ∧ letters qs (i+2)=9
private theorem letter_mem (qs:List Nat) (ne:qs≠[]) (n:Nat): letters qs n∈qs :=by
  have h:n%qs.length<qs.length:=Nat.mod_lt _ (List.length_pos_iff.mpr ne)
  simp [letters,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,List.getElem_mem]
private theorem triple_avoids {qs:List Nat} (ne:qs≠[]) (avoids:¬HasCyclicTriple qs) (n:Nat) :
    ¬(letters qs n=12 ∧ letters qs (n+1)=10 ∧ letters qs (n+2)=9) :=by
  rintro ⟨a,b,d⟩
  apply avoids
  have eq (k:Nat) : letters qs (n%qs.length+k)=letters qs (n+k):=by
    simp only [letters,Nat.mod_add_mod]
  exact ⟨n%qs.length,Nat.mod_lt _ (List.length_pos_iff.mpr ne),by simpa only [Nat.add_zero] using (eq 0).trans (by simpa using a),(eq 1).trans b,(eq 2).trans d⟩
private theorem exclude_literal (c:Coverage) {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (range:∀q,q∈qs→9≤q ∧ q≤16)
    (avoid:¬HasCyclicTriple qs) (s:Nat) : ¬Fitted x j s (letters qs) :=
  no_avoiding c black left (fun n=>range _ (letter_mem qs ne n)) (List.length_pos_iff.mpr ne)
    (letters_period qs) (triple_avoids ne avoid)

theorem literal_factor (c:Coverage) {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (range:∀q,q∈qs→9≤q ∧ q≤16)
    (fit:Rule30FiniteStrips.EventuallyWord x j (blocks qs)) : HasCyclicTriple qs :=by
  apply Classical.byContradiction;intro avoid
  exact literal_gap_word qs ne (exclude_literal c black left ne range avoid) fit

theorem rotation_factor (c:Coverage) {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (range:∀q,q∈qs→9≤q ∧ q≤16) (s d:Nat)
    (fit:∀t,evol x (s+t) j=(blocks qs).getD ((d+t)%(blocks qs).length) false) : HasCyclicTriple qs :=by
  apply Classical.byContradiction;intro avoid
  exact shifted_literal qs ne (exclude_literal c black left ne range avoid) s d fit
end Ruliology.CellularAutomata.Rule30RequiredGapFactor

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapFactor
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30Realization Rule30ResetMixtures
theorem sparse_rotation (c:Coverage) {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (sparse:∀q,q∈qs→9≤q) (s d:Nat)
    (fit:∀t,evol x (s+t) j=(blocks qs).getD ((d+t)%(blocks qs).length) false) :
    (∀q,q∈qs→q≤16) ∧ HasCyclicTriple qs :=by
  have limit (q:Nat) (hq:q∈qs):q≤16:=by
    apply Nat.le_of_not_gt;intro big
    exact Ruliology.CellularAutomata.Rule30RequiredGapLogic.GapFiniteFamily.long_gap_all_sites black left qs sparse ⟨q,hq,big⟩ j s d fit
  exact ⟨limit,rotation_factor c black left ne (fun q h=>⟨sparse q h,limit q h⟩) s d fit⟩
theorem sparse_word (c:Coverage) {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (sparse:∀q,q∈qs→9≤q)
    (fit:Rule30FiniteStrips.EventuallyWord x j (blocks qs)) :
    (∀q,q∈qs→q≤16) ∧ HasCyclicTriple qs :=by
  obtain ⟨s,h⟩:=fit
  apply sparse_rotation c black left ne sparse s 0
  intro t;rw [h (s+t) (by omega),show s+t-s=t by omega,Nat.zero_add]
end Ruliology.CellularAutomata.Rule30RequiredGapFactor

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapFactor
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30ResetMixtures Rule30Realization
def noTripleTest (qs:List Nat) := (List.range qs.length).all (fun i=>
    !(letters qs i==12 && letters qs (i+1)==10 && letters qs (i+2)==9))
theorem noTripleTest_sound {qs:List Nat} (ok:noTripleTest qs=true) : ¬HasCyclicTriple qs :=by
  rintro ⟨i,hi,a,b,c⟩
  have z:=List.all_eq_true.mp ok i (List.mem_range.mpr hi)
  simp [a,b,c] at z
theorem no_old_clock (c:Coverage) {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (old:qs=[9,9,10,12] ∨ qs=[9,12,10,12]) (s d:Nat) :
    ¬∀t,evol x (s+t) j=(blocks qs).getD ((d+t)%(blocks qs).length) false :=by
  have missing:noTripleTest qs=true:=by rcases old with rfl|rfl <;> decide +kernel
  have nonempty:qs≠[]:=by rcases old with rfl|rfl <;> decide
  have sparse:∀q,q∈qs→9≤q:=by
    intro q h;rcases old with rfl|rfl <;> simp at h <;> omega
  intro fit
  exact noTripleTest_sound missing (sparse_rotation c black left nonempty sparse s d fit).2
end Ruliology.CellularAutomata.Rule30RequiredGapFactor

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapFactor
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30Realization Rule30ResetMixtures
theorem certifiedCoverage : Coverage := ⟨wAll,uAll,vAll⟩
theorem mandatory_factor {x:Int→Bool} {lo j:Int} {s p:Nat} {q:Nat→Nat}
    (black:x lo=true) (left:∀i,i<lo→x i=false) (range:∀n,9≤q n ∧ q n≤16) (pos:0<p)
    (per:∀n,q (n+p)=q n) (fit:Fitted x j s q) (N:Nat) :
    ∃n,N≤n ∧ q n=12 ∧ q (n+1)=10 ∧ q (n+2)=9 :=
  recurrent_factor certifiedCoverage black left range pos per fit N
theorem mandatory_cyclic_factor {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (range:∀q,q∈qs→9≤q ∧ q≤16)
    (fit:Rule30FiniteStrips.EventuallyWord x j (blocks qs)) : HasCyclicTriple qs :=
  literal_factor certifiedCoverage black left ne range fit
theorem mandatory_rotated_factor {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (range:∀q,q∈qs→9≤q ∧ q≤16) (s d:Nat)
    (fit:∀t,evol x (s+t) j=(blocks qs).getD ((d+t)%(blocks qs).length) false) : HasCyclicTriple qs :=
  rotation_factor certifiedCoverage black left ne range s d fit
theorem sparse_cyclic_factor {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (sparse:∀q,q∈qs→9≤q)
    (fit:Rule30FiniteStrips.EventuallyWord x j (blocks qs)) : (∀q,q∈qs→q≤16) ∧ HasCyclicTriple qs :=
  sparse_word certifiedCoverage black left ne sparse fit
theorem sparse_rotated_factor {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (ne:qs≠[]) (sparse:∀q,q∈qs→9≤q) (s d:Nat)
    (fit:∀t,evol x (s+t) j=(blocks qs).getD ((d+t)%(blocks qs).length) false) : (∀q,q∈qs→q≤16) ∧ HasCyclicTriple qs :=
  sparse_rotation certifiedCoverage black left ne sparse s d fit
theorem no_residue_44_47 {x:Int→Bool} {lo j:Int} (black:x lo=true)
    (left:∀i,i<lo→x i=false) {qs:List Nat} (old:qs=[9,9,10,12] ∨ qs=[9,12,10,12]) (s d:Nat) :
    ¬∀t,evol x (s+t) j=(blocks qs).getD ((d+t)%(blocks qs).length) false :=
  no_old_clock certifiedCoverage black left old s d
end Ruliology.CellularAutomata.Rule30RequiredGapFactor

end
