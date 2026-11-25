module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# Eastern realizability of Rule 30 strip histories

For an arbitrary pair of temporal columns, three local tests characterize infinite
extensions through the next eastern update. With one further updated cell the
observation language has minimal forbidden words of unbounded length. A concrete
eight-white clock admits every sampled binary stream in a free strip, while both
return paths in the coding construction violate a three-tick extension test.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30EasternRealizability

open Ruliology.CellularAutomata Rule30Jen

def update (L C R : Nat → Bool) : Prop := ∀ t, C (t+1)=rule (L t) (C t) (R t)
def required (L C : Nat → Bool) (t : Nat) := xor (L t) (C (t+1))

private theorem solve (l c r n : Bool) :
    n=rule l c r ↔ (c || r)=xor l n := by
  cases l <;> cases c <;> cases r <;> cases n <;> decide

/-- Observing a black cell forces its next value and releases its right neighbor.
A white cell uniquely determines its right neighbor. -/
theorem one_column (L C : Nat → Bool) :
    (∃ R, update L C R) ↔ ∀ t, C t=true → required L C t=true := by
  constructor
  · rintro ⟨R,h⟩ t hc
    have e := (solve ..).mp (h t)
    simpa only [required,hc,Bool.true_or] using e.symm
  · intro h
    refine ⟨required L C,fun t => (solve ..).mpr ?_⟩
    cases e : C t
    · rfl
    · simpa only [required,Bool.true_or] using (h t e).symm

/-- All the required conditions are bounded windows. The second condition applies
within a run of whites; the third spans a single black between two whites. -/
def legal (L C : Nat → Bool) : Prop :=
  (∀ t, C t=true → required L C t=true) ∧
  (∀ t, C t=false → C (t+1)=false → required L C t=true → required L C (t+1)=true) ∧
  (∀ t, C t=false → C (t+1)=true → C (t+2)=false →
    required L C t=true → required L C (t+2)=false)

private def forced (C b : Nat → Bool) : Nat → Bool
  | 0 => if C 0 then false else b 0
  | t+1 => if C (t+1) then !C t && b t else b (t+1)

private theorem forced_white {C b : Nat → Bool} {t : Nat} (h : C t=false) : forced C b t=b t := by
  cases t <;> simp [forced,h]

private theorem on_white {L C R : Nat → Bool} (u : update L C R) {t : Nat} (h : C t=false) :
    R t=required L C t := by simpa only [required,h,Bool.false_or] using (solve ..).mp (u t)

private theorem after_one {L C R : Nat → Bool} (u : update L C R) {t : Nat} (h : C t=true) :
    C (t+1)= !L t := by rw [u t,h];cases L t <;> rfl

/-- Two eastern updates extend forever iff the explicit three temporal tests hold.
No hypothesis on the widths or periods of the traces is needed. -/
theorem two_columns (L C : Nat → Bool) :
    (∃ R Z, update L C R ∧ update C R Z) ↔ legal L C := by
  constructor
  · rintro ⟨R,Z,u,v⟩
    refine ⟨(one_column L C).mp ⟨R,u⟩,?_,?_⟩
    · intro t c0 c1 b
      rw [←on_white u c1]
      rw [←on_white u c0] at b
      simpa only [c0,Bool.not_false] using after_one v b
    · intro t c0 c1 c2 b
      rw [←on_white u c2]
      rw [←on_white u c0] at b
      have r1 : R (t+1)=true := by simpa only [c0,Bool.not_false] using after_one v b
      simpa only [c1,Bool.not_true] using after_one v r1
  · rintro ⟨black,both,one⟩
    let b := required L C
    let R := forced C b
    have hR : update L C R := by
      intro t
      apply (solve ..).mpr
      cases h : C t
      · exact forced_white h
      · simpa only [required,Bool.true_or] using (black t h).symm
    refine ⟨R,required C R,hR,?_⟩
    · intro t
      apply (solve ..).mpr
      cases h : R t
      · rfl
      · have next : R (t+1)= !C t := by
          cases old : C t with
          | false =>
            have h1 : b t=true := (forced_white old).symm.trans h
            cases nxt : C (t+1) with
            | false => exact (forced_white nxt).trans (both t old nxt h1)
            | true => simp [R,forced,old,nxt,h1]
          | true =>
            cases nxt : C (t+1) with
            | true => simp [R,forced,old,nxt]
            | false =>
              cases t with
              | zero => simp [R,forced,old] at h
              | succ t =>
                have hw : (!C t && b t)=true := by simpa only [R,forced,old,ite_true] using h
                simp only [Bool.and_eq_true] at hw
                obtain ⟨c,hb⟩ := hw
                have c0 : C t=false := by cases e : C t <;> simp_all
                exact (forced_white nxt).trans (one t c0 old nxt hb)
        rw [required,next]
        cases C t <;> rfl

open Ruliology.CellularAutomata.Rule30StripCertificates
inductive Letter where | zero | one | black deriving DecidableEq, Repr
open Letter

/-- The black letter records a black center. At a white center the letter records its eastern bit. -/
def matchAt (a : Letter) (r : Nat) : Bool :=
  match a with | zero => !r.testBit 0 | one => r.testBit 0 | black => true

def drive (a : Letter) := decide (a=black)

def step (S : List Nat) (a : Letter) : List Nat := [0,1,2,3].filter (fun y =>
  S.any (fun r => matchAt a r && (stripStep 2 (drive a) false r == y || stripStep 2 (drive a) true r == y)))

def run (S : List Nat) (w : List Letter) := w.foldl step S
def full : List Nat := [0,1,2,3]

/-- A run consists of genuine width-two updates with a common chosen boundary bit per tick. -/
inductive Path : Nat → List Letter → Nat → Prop
  | nil (r : Nat) : Path r [] r
  | cons {r v : Nat} {a : Letter} {w : List Letter} (b : Bool)
      (ok : matchAt a r=true) (tail : Path (stripStep 2 (drive a) b r) w v) : Path r (a::w) v

private theorem step_mem {S : List Nat} {a : Letter} {v : Nat} :
    v∈step S a ↔ ∃ r∈S, ∃ b, matchAt a r=true ∧ stripStep 2 (drive a) b r=v := by
  simp only [step,List.mem_filter,List.any_eq_true,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨_,r,hr,ok,b0|b1⟩
    · exact ⟨r,hr,false,ok,b0⟩
    · exact ⟨r,hr,true,ok,b1⟩
  · rintro ⟨r,hr,b,ok,rfl⟩
    have h := stripStep_lt 2 (drive a) b r
    refine ⟨by simp only [List.mem_cons,List.not_mem_nil,or_false];omega, r,hr,ok,?_⟩
    cases b <;> simp

theorem accepts_iff (w : List Letter) (S : List Nat) (v : Nat) :
    v∈run S w ↔ ∃ r∈S, Path r w v := by
  induction w generalizing S with
  | nil =>
    exact ⟨fun h => ⟨v,h,.nil _⟩,by rintro ⟨r,hr,h⟩;cases h;exact hr⟩
  | cons a w ih =>
    change v∈run (step S a) w ↔ _
    rw [ih]
    constructor
    · rintro ⟨u,hu,path⟩
      obtain ⟨r,hr,b,ok,rfl⟩ := step_mem.mp hu
      exact ⟨r,hr,.cons b ok path⟩
    · rintro ⟨r,hr,h⟩
      cases h with
      | cons b ok path => exact ⟨_,step_mem.mpr ⟨r,hr,b,ok,rfl⟩,path⟩

def Loop : Nat → List Letter
  | 0 => []
  | n+1 => [zero,black,zero,black] ++ Loop n

private theorem pump (n : Nat) : run [1,2,3] (Loop n)=[1,2,3] ∧ run full (Loop n)=full := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih

/-- 122(0202)^n00 is impossible. Removing either end gives a realizable word.
Here 0 and 1 are the two white mask readings and 2 denotes a black center. -/
theorem unbounded_minimal_obstructions (n : Nat) :
    run full ([one,black,black]++Loop n++[zero,zero])=[] ∧
    3∈run full ([one,black,black]++Loop n++[zero]) ∧
    0∈run full ([black,black]++Loop n++[zero,zero]) := by
  simp only [run,List.foldl_append]
  change run (run [1,2,3] (Loop n)) [zero,zero]=[] ∧
    3∈run (run [1,2,3] (Loop n)) [zero] ∧
    0∈run (run full (Loop n)) [zero,zero]
  rw [(pump n).1,(pump n).2]
  decide +kernel

/-- A word is feasible when two eastern cells can be updated for its entire duration. -/
def Feasible (w : List Letter) : Prop := ∃ r, r < 4 ∧ ∃ v, Path r w v

private theorem feasible_iff (w : List Letter) : Feasible w ↔ ∃ v, v ∈ run full w := by
  have mem : ∀ r : Nat, r ∈ full ↔ r < 4 := by
    intro r
    simp only [full,List.mem_cons,List.not_mem_nil,or_false]
    omega
  constructor
  · rintro ⟨r,hr,v,h⟩
    exact ⟨v,(accepts_iff ..).mpr ⟨r,(mem r).mpr hr,h⟩⟩
  · rintro ⟨v,h⟩
    obtain ⟨r,hr,hp⟩ := (accepts_iff ..).mp h
    exact ⟨r,(mem r).mp hr,v,hp⟩

private theorem split_path {u v : List Letter} {r z : Nat} (start : r < 4) (h : Path r (u++v) z) :
    ∃ m, m < 4 ∧ Path r u m ∧ Path m v z := by
  induction u generalizing r with
  | nil => exact ⟨r,start,.nil _,h⟩
  | cons a u ih =>
    cases h with
    | cons b ha path =>
      obtain ⟨m,hm,hp,hq⟩ := ih (stripStep_lt ..) path
      exact ⟨m,hm,.cons b ha hp,hq⟩

private theorem infix_feasible {p u q : List Letter} (h : Feasible (p++u++q)) : Feasible u := by
  obtain ⟨r,hr,v,path⟩ := h
  obtain ⟨m,_,head,_⟩ := split_path (u:=p++u) hr path
  obtain ⟨j,hj,_,mid⟩ := split_path (u:=p) hr head
  exact ⟨j,hj,m,mid⟩

private theorem loop_length (n : Nat) : (Loop n).length=4*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Loop,List.length_append,List.length_cons,List.length_nil,ih];omega

/-- For every finite memory bound there is an impossible strip word all of whose
contiguous subwords up to that length are feasible. -/
theorem no_finite_window_bound (L : Nat) :
    ∃ w : List Letter, ¬ Feasible w ∧
      ∀ (p u q : List Letter), p++u++q=w → u.length≤L → Feasible u := by
  let mid := [black,black]++Loop L++[zero]
  have len : mid.length=4*L+3 := by simp [mid,loop_length]
  obtain ⟨bad,leftOK,rightOK⟩ := unbounded_minimal_obstructions L
  have lp : Feasible (one::mid) := (feasible_iff _).mpr ⟨3,leftOK⟩
  have rp : Feasible (mid++[zero]) := (feasible_iff _).mpr ⟨0,by
    simpa only [mid,List.append_assoc,List.cons_append,List.nil_append] using rightOK⟩
  refine ⟨one::(mid++[zero]),?_,?_⟩
  · intro h
    obtain ⟨v,hv⟩ := (feasible_iff _).mp h
    have he : one::(mid++[zero])=[one,black,black]++Loop L++[zero,zero] := by simp [mid,List.append_assoc]
    rw [he,bad] at hv
    simp at hv
  · intro p u q eq le
    cases p with
    | cons a p =>
      have tail := (List.cons.inj eq).2
      exact infix_feasible (tail ▸ rp)
    | nil =>
      cases q with
      | nil =>
        have e := congrArg List.length eq
        simp [len] at e
        omega
      | cons b q =>
        let s := (b::q).dropLast
        let z := (b::q).getLast (by simp)
        have hq : b::q=s++[z] := (List.dropLast_concat_getLast (show b::q ≠ [] by simp)).symm
        change u++(b::q)=one::(mid++[zero]) at eq
        rw [hq] at eq
        have e : (u++s)++[z]=(one::mid)++[zero] := by simpa only [List.append_assoc,List.cons_append] using eq
        have front := congrArg List.dropLast e
        simp only [List.dropLast_concat] at front
        exact infix_feasible (p:=[]) (q:=s) (by simpa only [List.nil_append,front] using lp)


namespace Switch
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30StripCertificates

/-- The driver starts at phase one of `000000001`. -/
def driver (t : Nat) : Bool := t % 9 == 7

def startRow : Nat := 0x1ad47316

def controlA : Nat := 0x825c14235a1d950cc43874231fc060434108d4
def controlB : Nat := 0x505000008880000080060000080800c08215040900000

/-- External bits are packed with the first tick in bit zero. -/
def control (choice : Bool) (t : Nat) : Bool :=
  if choice then
    if t < 153 then controlA.testBit t else controlB.testBit (t - 153)
  else
    if t < 180 then controlB.testBit t else controlA.testBit (t - 180)

def before (choice : Bool) : Nat → Nat
  | 0 => startRow
  | t + 1 => stripStep 32 (driver t) (control choice t) (before choice t)

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem close (choice : Bool) : before choice 333 = startRow := by
  cases choice <;> decide +kernel

theorem distinguish (choice : Bool) :
    (driver 127 || (before choice 127).testBit 0) = choice := by
  cases choice <;> decide +kernel

/-- The row and exterior are defined for every requested infinite binary stream. -/
def row (bits : Nat → Bool) (t : Nat) : Nat := before (bits (t / 333)) (t % 333)
def exterior (bits : Nat → Bool) (t : Nat) : Bool := control (bits (t / 333)) (t % 333)

theorem arbitrary_masked_stream (bits : Nat → Bool) :
    row bits 0 = startRow ∧
    (∀ t, row bits (t + 1) = stripStep 32 (driver t) (exterior bits t) (row bits t)) ∧
    (∀ n, (driver (333 * n + 127) || (row bits (333 * n + 127)).testBit 0) = bits n) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro t
    have hp : driver t = driver (t % 333) := by
      unfold driver
      have h : t % 333 % 9 = t % 9 := Nat.mod_mod_of_dvd _ (by decide)
      rw [h]
    have bound := Nat.mod_lt t (by decide : 0 < 333)
    unfold row exterior
    rw [hp]
    by_cases h : t % 333 = 332
    · have hzero : (t + 1) % 333 = 0 := by omega
      rw [hzero, before, h]
      exact (close (bits (t / 333))).symm
    · have hmod : (t + 1) % 333 = t % 333 + 1 := by omega
      have hdiv : (t + 1) / 333 = t / 333 := by omega
      rw [hmod, hdiv, before]
  · intro n
    have hmod : (333*n+127) % 333 = 127 := by omega
    have hdiv : (333*n+127) / 333 = n := by omega
    have hphase : driver (333*n+127) = driver 127 := by
      unfold driver
      have h : (333*n+127) % 9 = 127 % 9 := by omega
      rw [h]
    simpa only [row, hmod, hdiv, hphase] using distinguish (bits n)

open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30Jen

/-- A forbidden three-time pattern in columns i-1 and i. -/
theorem forced_black (u : Nat → Int → Bool)
    (step : ∀ t i, u (t+1) i = rule (u t (i-1)) (u t i) (u t (i+1)))
    (t : Nat) (i : Int) (l0 : u t (i-1) = true) (c0 : u t i = false)
    (l1 : u (t+1) (i-1) = false) (c1 : u (t+1) i = false) :
    u (t+2) i = true := by
  have r0 : u t (i+1) = true := by
    have h := step t i
    rw [c1, l0, c0] at h
    cases q : u t (i+1)
    · simp [q, rule] at h
    · rfl
  have r1 : u (t+1) (i+1) = true := by
    rw [step t (i+1), show i+1-1=i by omega, c0, r0]
    simp [rule]
  rw [show t+2=t+1+1 by omega, step (t+1) i, l1, c1, r1]
  rfl

/-- At tick 2 of A and tick 20 of B, the first two rows show the same
local defect. The next prescribed row has white at cell 32. -/
def defectTime (choice : Bool) : Nat := if choice then 2 else 20

private theorem witness (choice : Bool) :
    let t := defectTime choice
    (before choice t).testBit 30 = true ∧ (before choice t).testBit 31 = false ∧
    (before choice (t+1)).testBit 30 = false ∧ (before choice (t+1)).testBit 31 = false ∧
    (before choice (t+2)).testBit 31 = false := by
  cases choice <;> decide +kernel

/-- Neither order in the 333-tick switch can be a restriction of a genuine
Rule 30 trajectory, even if every cell initially beyond column 32 can vary.
The contradiction uses only three successive times and only the last two
prescribed columns. -/
theorem no_east_extension (choice : Bool) (u : Nat → Int → Bool)
    (step : ∀ t i, u (t+1) i = rule (u t (i-1)) (u t i) (u t (i+1))) :
    ¬ (∀ t, t ≤ defectTime choice + 2 → ∀ j : Nat, 30 ≤ j → j < 32 →
        u t (1 + (j : Int)) = (before choice t).testBit j) := by
  intro h
  let t := defectTime choice
  obtain ⟨a,b,c,d,e⟩ := witness choice
  have left0 : u t (32 - 1) = true := (h t (by dsimp [t]; omega) 30 (by decide) (by decide)).trans a
  have center0 : u t 32 = false := (h t (by dsimp [t]; omega) 31 (by decide) (by decide)).trans b
  have left1 : u (t+1) (32 - 1) = false := (h (t+1) (by dsimp [t]; omega) 30 (by decide) (by decide)).trans c
  have center1 : u (t+1) 32 = false := (h (t+1) (by dsimp [t]; omega) 31 (by decide) (by decide)).trans d
  have center2 : u (t+2) 32 = false := (h (t+2) (by dsimp [t]; omega) 31 (by decide) (by decide)).trans e
  have f := forced_black u step t 32 left0 center0 left1 center1
  simp [center2] at f
end Switch

/-- Every infinite bit sequence is read from a free strip at the stated ticks.
Neither choice for its first return block extends through the next eastern update. -/
theorem programmable_without_extension (bits : Nat → Bool) :
    Switch.row bits 0=Switch.startRow ∧
    (∀ t, Switch.row bits (t+1)=Ruliology.CellularAutomata.Rule30StripCertificates.stripStep
      32 (Switch.driver t) (Switch.exterior bits t) (Switch.row bits t)) ∧
    (∀ n, (Switch.driver (333*n+127) || (Switch.row bits (333*n+127)).testBit 0)=bits n) ∧
    ∀ u : Nat → Int → Bool,
      (∀ t i, u (t+1) i=Ruliology.CellularAutomata.Rule30Jen.rule (u t (i-1)) (u t i) (u t (i+1))) →
      ¬ (∀ t, t≤Switch.defectTime (bits 0)+2 → ∀ j : Nat, 30≤j → j<32 →
        u t (1+(j:Int))=(Switch.row bits t).testBit j) := by
  obtain ⟨init,step,readout⟩ := Switch.arbitrary_masked_stream bits
  refine ⟨init,step,readout,fun u laws eq => Switch.no_east_extension (bits 0) u laws ?_⟩
  intro t ht j lo hi
  have small : t<333 := by
    unfold Switch.defectTime at ht
    split at ht <;> omega
  simpa only [Switch.row,Nat.div_eq_of_lt small,Nat.mod_eq_of_lt small] using eq t ht j lo hi

end Ruliology.CellularAutomata.Rule30EasternRealizability
