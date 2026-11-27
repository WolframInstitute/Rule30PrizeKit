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

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

def oneColStepOk (p q : Bool × Bool) : Bool := (!p.2) || xor p.1 q.2
def pairAlphabet : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

def oneColFrom (p : Bool × Bool) : Nat → List (List (Bool × Bool))
  | 0 => [[p]]
  | k + 1 => (pairAlphabet.filter (oneColStepOk p)).flatMap (fun q => (oneColFrom q k).map (p :: ·))

def OneColLegalWords (n : Nat) : List (List (Bool × Bool)) :=
  match n with
  | 0 => [[]]
  | k + 1 => pairAlphabet.flatMap (fun p => oneColFrom p k)

theorem oneColLegal_count_eq (n : Nat) :
    (OneColLegalWords (n + 1)).length = 4 * 3 ^ n := by
  cases n with
  | zero => rfl
  | succ k =>
    have hinv : ∀ m,
        (oneColFrom (false, false) (m + 1)).length = 4 * 3 ^ m ∧
        (oneColFrom (true, false) (m + 1)).length = 4 * 3 ^ m ∧
        (oneColFrom (false, true) (m + 1)).length + (oneColFrom (true, true) (m + 1)).length = 4 * 3 ^ m := by
      intro m; induction m with
      | zero => decide
      | succ m ih =>
        rcases ih with ⟨hff, htf, hsum⟩
        have step_ff : (oneColFrom (false, false) (m + 1 + 1)).length =
            (oneColFrom (false, false) (m + 1)).length + (oneColFrom (false, true) (m + 1)).length +
            (oneColFrom (true, false) (m + 1)).length + (oneColFrom (true, true) (m + 1)).length := by
          rw [oneColFrom]; simp [pairAlphabet, oneColStepOk]; omega
        have step_tf : (oneColFrom (true, false) (m + 1 + 1)).length =
            (oneColFrom (false, false) (m + 1)).length + (oneColFrom (false, true) (m + 1)).length +
            (oneColFrom (true, false) (m + 1)).length + (oneColFrom (true, true) (m + 1)).length := by
          rw [oneColFrom]; simp [pairAlphabet, oneColStepOk]; omega
        have step_ft : (oneColFrom (false, true) (m + 1 + 1)).length =
            (oneColFrom (false, true) (m + 1)).length + (oneColFrom (true, true) (m + 1)).length := by
          rw [oneColFrom]; simp [pairAlphabet, oneColStepOk]
        have step_tt : (oneColFrom (true, true) (m + 1 + 1)).length =
            (oneColFrom (false, false) (m + 1)).length + (oneColFrom (true, false) (m + 1)).length := by
          rw [oneColFrom]; simp [pairAlphabet, oneColStepOk]
        rw [step_ff, step_tf, step_ft, step_tt, Nat.pow_succ]
        omega
    obtain ⟨h1, h2, h3⟩ := hinv k
    have htot : (OneColLegalWords (k + 1 + 1)).length =
        (oneColFrom (false, false) (k + 1)).length + (oneColFrom (false, true) (k + 1)).length +
        (oneColFrom (true, false) (k + 1)).length + (oneColFrom (true, true) (k + 1)).length := by
      rw [OneColLegalWords]; simp [pairAlphabet]; omega
    rw [htot, Nat.pow_succ]; omega

def pairEnc (l c : Bool) : Nat := (if l then 1 else 0) + (if c then 2 else 0)
def pairDecL (x : Nat) : Bool := x % 2 == 1
def pairDecC (x : Nat) : Bool := (x / 2) % 2 == 1

def sft32Win : List (Nat × Nat × Nat) := [(0, (0, 0)), (0, (0, 1)), (0, (0, 2)), (0, (0, 3)), (0, (1, 0)), (0, (1, 1)), (0, (1, 2)), (0, (1, 3)), (0, (2, 2)), (0, (2, 3)), (0, (3, 0)), (0, (3, 1)), (1, (0, 2)), (1, (0, 3)), (1, (1, 0)), (1, (1, 1)), (1, (2, 2)), (1, (2, 3)), (1, (3, 0)), (1, (3, 1)), (2, (2, 2)), (2, (2, 3)), (2, (3, 0)), (2, (3, 1)), (3, (0, 0)), (3, (0, 1)), (3, (0, 2)), (3, (0, 3)), (3, (1, 0)), (3, (1, 1)), (3, (1, 2)), (3, (1, 3))]
def sft32Next : List (List Nat) := [[0, 1, 2, 3], [4, 5, 6, 7], [32, 32, 8, 9], [10, 11, 32, 32], [32, 32, 12, 13], [14, 15, 32, 32], [32, 32, 16, 17], [18, 19, 32, 32], [32, 32, 20, 21], [22, 23, 32, 32], [24, 25, 32, 32], [32, 32, 30, 31], [32, 32, 8, 9], [10, 11, 32, 32], [32, 32, 12, 13], [14, 15, 32, 32], [32, 32, 20, 21], [22, 23, 32, 32], [24, 25, 26, 27], [28, 29, 30, 31], [32, 32, 20, 21], [22, 23, 32, 32], [24, 25, 26, 27], [28, 29, 30, 31], [0, 1, 2, 3], [4, 5, 6, 7], [32, 32, 8, 9], [10, 11, 32, 32], [32, 32, 12, 13], [14, 15, 32, 32], [32, 32, 16, 17], [18, 19, 32, 32]]
def sft32Wt : List Nat := [213, 140, 92, 92, 73, 48, 92, 140, 92, 140, 140, 92, 92, 92, 73, 48, 92, 140, 213, 140, 92, 140, 213, 140, 213, 140, 92, 92, 73, 48, 92, 140]

def sft32FindInit (a b c : Nat) : Option Nat :=
  (List.range 32).find? (fun q => sft32Win.getD q (9, 9, 9) == (a, (b, c)))

def sft32Step (q d : Nat) : Option Nat :=
  let v := (sft32Next.getD q []).getD d 32
  if v < 32 then some v else none

def sft32Run : Nat → List Nat → Option Nat
  | q, [] => some q
  | q, d :: ds => match sft32Step q d with | some q' => sft32Run q' ds | none => none

def sft32Accepts : List Nat → Bool
  | a :: b :: c :: rest => match sft32FindInit a b c with | some q => (sft32Run q rest).isSome | none => false
  | _ => false

def sft32From (q : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => ([0, 1, 2, 3].filterMap (fun d => (sft32Step q d).map (fun q' => (d, q')))).flatMap
      (fun dq => (sft32From dq.2 n).map (dq.1 :: ·))

def sft32Words (n : Nat) : List (List Nat) :=
  (List.range 32).flatMap (fun q =>
    let (a, bc) := sft32Win.getD q (0, 0, 0)
    (sft32From q n).map (fun rest => a :: bc.1 :: bc.2 :: rest))

def legal3Code (a b c : Nat) : Bool :=
  let l0 := pairDecL a; let c0 := pairDecC a
  let l1 := pairDecL b; let c1 := pairDecC b
  let c2 := pairDecC c
  ((!c0) || xor l0 c1) && ((!c1) || xor l1 c2) &&
  (!(c0 == false && c1 == false && xor l0 c1 == true) || (xor l1 c2 == true))

def legal4Code (a b c d : Nat) : Bool :=
  legal3Code a b c && legal3Code b c d &&
  (!(pairDecC a == false && pairDecC b == true && pairDecC c == false && xor (pairDecL a) (pairDecC b) == true) ||
    (xor (pairDecL c) (pairDecC d) == false))

private theorem sft32_sound_tables :
    (List.range 4).all (fun a => (List.range 4).all (fun b => (List.range 4).all (fun c =>
      if legal3Code a b c then
        match sft32FindInit a b c with
        | some q => q < 32 && (sft32Win.getD q (9, 9, 9) == (a, (b, c)))
        | none => false
      else true))) &&
    (List.range 32).all (fun q =>
      let (a, bc) := sft32Win.getD q (9, 9, 9)
      (List.range 4).all (fun d =>
        if legal4Code a bc.1 bc.2 d then
          match sft32Step q d with
          | some q' => q' < 32 && (sft32Win.getD q' (9, 9, 9) == (bc.1, (bc.2, d)))
          | none => false
        else true)) = true := by decide +kernel

theorem twoColLegal_prefix_in_sft32 (L C : Nat → Bool)
    (h2 : ∃ R Z, update L C R ∧ update C R Z) (n : Nat) :
    sft32Accepts ((List.range (n + 3)).map (fun t => pairEnc (L t) (C t))) = true := by
  have hleg := (two_columns L C).mp h2
  let sym := fun t => pairEnc (L t) (C t)
  have hsym_lt : ∀ t, sym t < 4 := by intro t; dsimp [sym, pairEnc]; cases L t <;> cases C t <;> decide
  have hdec : ∀ t, pairDecL (sym t) = L t ∧ pairDecC (sym t) = C t := by
    intro t; dsimp [sym, pairEnc, pairDecL, pairDecC]; cases L t <;> cases C t <;> decide
  have hl3 : ∀ t, legal3Code (sym t) (sym (t + 1)) (sym (t + 2)) = true := by
    intro t; unfold legal3Code
    rw [(hdec t).1, (hdec t).2, (hdec (t + 1)).1, (hdec (t + 1)).2, (hdec (t + 2)).2]
    have h1 := hleg.1 t; have h2' := hleg.1 (t + 1); have h3' := hleg.2.1 t
    dsimp [required] at h1 h2' h3'
    cases hC0 : C t <;> cases hC1 : C (t + 1) <;> cases hL0 : L t <;> cases hL1 : L (t + 1) <;> cases hC2 : C (t + 2) <;> simp_all
  have hl4 : ∀ t, legal4Code (sym t) (sym (t + 1)) (sym (t + 2)) (sym (t + 3)) = true := by
    intro t; unfold legal4Code
    rw [hl3 t, hl3 (t + 1), Bool.true_and, Bool.true_and]
    rw [(hdec t).1, (hdec t).2, (hdec (t + 1)).2, (hdec (t + 2)).1, (hdec (t + 2)).2, (hdec (t + 3)).2]
    have h4' := hleg.2.2 t; dsimp [required] at h4'
    cases hC0 : C t <;> cases hC1 : C (t + 1) <;> cases hC2 : C (t + 2) <;> cases hL0 : L t <;> cases hL2 : L (t + 2) <;> cases hC3 : C (t + 3) <;> simp_all
  have htab := sft32_sound_tables; simp only [Bool.and_eq_true] at htab
  have hinit_row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp htab.1 (sym 0) (List.mem_range.mpr (hsym_lt 0))) (sym 1) (List.mem_range.mpr (hsym_lt 1))) (sym 2) (List.mem_range.mpr (hsym_lt 2))
  simp only [hl3 0, ↓reduceIte] at hinit_row
  cases hfi : sft32FindInit (sym 0) (sym 1) (sym 2) with
  | none => rw [hfi] at hinit_row; simp at hinit_row
  | some q0 =>
    rw [hfi] at hinit_row; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hinit_row
    have hwalk : ∀ m t q, q < 32 → sft32Win.getD q (9, 9, 9) = (sym t, (sym (t + 1), sym (t + 2))) →
        ∃ q', q' < 32 ∧ sft32Run q ((List.range m).map (fun k => sym (t + 3 + k))) = some q' := by
      intro m; induction m with
      | zero => intro t q hq _; exact ⟨q, hq, rfl⟩
      | succ m ih =>
        intro t q hq hwin
        have hq_row := List.all_eq_true.mp htab.2 q (List.mem_range.mpr hq)
        rw [hwin] at hq_row
        have hd_row := List.all_eq_true.mp hq_row (sym (t + 3)) (List.mem_range.mpr (hsym_lt (t + 3)))
        simp only [hl4 t, ↓reduceIte] at hd_row
        cases hst : sft32Step q (sym (t + 3)) with
        | none => rw [hst] at hd_row; simp at hd_row
        | some q1 =>
          rw [hst] at hd_row; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd_row
          have hr_eq : (List.range (m + 1)).map (fun k => sym (t + 3 + k)) =
              sym (t + 3) :: (List.range m).map (fun k => sym (t + 1 + 3 + k)) := by
            rw [List.range_succ_eq_map, List.map_cons, List.map_map]; congr 1
            apply List.map_congr_left; intro k _; simp only [Function.comp_apply]; congr 1; omega
          rw [hr_eq, sft32Run, hst]
          exact ih (t + 1) q1 hd_row.1 hd_row.2
    have hsplit : (List.range (n + 3)).map sym = sym 0 :: sym 1 :: sym 2 :: (List.range n).map (fun k => sym (0 + 3 + k)) := by
      have h3 : List.range (n + 3) = 0 :: 1 :: 2 :: (List.range n).map (fun k => 3 + k) := by
        induction n with
        | zero => rfl
        | succ n ihn => rw [show n + 1 + 3 = (n + 3) + 1 by omega, List.range_succ, ihn, List.range_succ, List.map_append]; simp [Nat.add_comm 3 n]
      simp [h3, List.map_map, Function.comp_def]
    obtain ⟨q', _, hrun⟩ := hwalk n 0 q0 hinit_row.1 hinit_row.2
    change sft32Accepts ((List.range (n + 3)).map sym) = true
    rw [hsplit]; simp [sft32Accepts, hfi, hrun]

private theorem sft32_wt_ok :
    ((List.range 32).map (fun q => sft32Wt.getD q 0)).sum == 3719 &&
    (List.range 32).all (fun q =>
      let wq := sft32Wt.getD q 0
      let ok := [0, 1, 2, 3].all (fun d => match sft32Step q d with | some q' => decide (q' < 32) | none => true)
      let s := ([0, 1, 2, 3].map (fun d => match sft32Step q d with | some q' => sft32Wt.getD q' 0 | none => 0)).sum
      decide (1 ≤ wq) && ok && decide (23 * s ≤ 58 * wq)) = true := by decide +kernel

theorem twoColLegal_wordCount_le_58_23 (n : Nat) :
    (sft32Words n).length * 23 ^ n ≤ 3719 * 58 ^ n := by
  have htab := sft32_wt_ok; simp only [Bool.and_eq_true, beq_iff_eq] at htab
  have hfrom : ∀ m q, q < 32 → (sft32From q m).length * 23 ^ m ≤ (sft32Wt.getD q 0) * 58 ^ m := by
    intro m; induction m with
    | zero => intro q hq; simp [sft32From]; have h := List.all_eq_true.mp htab.2 q (List.mem_range.mpr hq); simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1
    | succ m ih =>
      intro q hq
      have h := List.all_eq_true.mp htab.2 q (List.mem_range.mpr hq)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have hd : ∀ d ∈ ([0, 1, 2, 3] : List Nat),
          (match sft32Step q d with | some q' => (sft32From q' m).length | none => 0) * 23 ^ m ≤
          (match sft32Step q d with | some q' => sft32Wt.getD q' 0 | none => 0) * 58 ^ m := by
        intro d hd_mem
        have hok_d := List.all_eq_true.mp h.1.2 d hd_mem
        cases hst : sft32Step q d with
        | none => simp
        | some q' => rw [hst] at hok_d; exact ih q' (decide_eq_true_eq.mp hok_d)
      have hexp : (sft32From q (m + 1)).length =
          (match sft32Step q 0 with | some q' => (sft32From q' m).length | none => 0) +
          (match sft32Step q 1 with | some q' => (sft32From q' m).length | none => 0) +
          (match sft32Step q 2 with | some q' => (sft32From q' m).length | none => 0) +
          (match sft32Step q 3 with | some q' => (sft32From q' m).length | none => 0) := by
        rw [sft32From]; simp only [List.filterMap_cons, List.filterMap_nil]
        cases sft32Step q 0 <;> cases sft32Step q 1 <;> cases sft32Step q 2 <;> cases sft32Step q 3 <;> simp <;> omega
      have h0 := hd 0 (by simp); have h1 := hd 1 (by simp); have h2 := hd 2 (by simp); have h3 := hd 3 (by simp)
      have hsum_w : ([0, 1, 2, 3].map (fun d => match sft32Step q d with | some q' => sft32Wt.getD q' 0 | none => 0)).sum =
          (match sft32Step q 0 with | some q' => sft32Wt.getD q' 0 | none => 0) +
          (match sft32Step q 1 with | some q' => sft32Wt.getD q' 0 | none => 0) +
          (match sft32Step q 2 with | some q' => sft32Wt.getD q' 0 | none => 0) +
          (match sft32Step q 3 with | some q' => sft32Wt.getD q' 0 | none => 0) := by simp; omega
      have hw2 := h.2; rw [hsum_w] at hw2
      rw [hexp, Nat.pow_succ, Nat.pow_succ]
      have hpf4 : ∀ {A0 A1 A2 A3 W0 W1 W2 W3 Wq pm qm : Nat},
          A0 * qm ≤ W0 * pm → A1 * qm ≤ W1 * pm → A2 * qm ≤ W2 * pm → A3 * qm ≤ W3 * pm →
          23 * (W0 + W1 + W2 + W3) ≤ 58 * Wq → (A0 + A1 + A2 + A3) * (qm * 23) ≤ Wq * (pm * 58) := by
        intro A0 A1 A2 A3 W0 W1 W2 W3 Wq pm qm g0 g1 g2 g3 gw
        have gsum : (A0 + A1 + A2 + A3) * qm ≤ (W0 + W1 + W2 + W3) * pm := by
          repeat rw [Nat.add_mul]
          exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add g0 g1) g2) g3
        calc (A0 + A1 + A2 + A3) * (qm * 23) = 23 * ((A0 + A1 + A2 + A3) * qm) := by rw [← Nat.mul_assoc, Nat.mul_comm _ 23]
          _ ≤ 23 * ((W0 + W1 + W2 + W3) * pm) := Nat.mul_le_mul_left 23 gsum
          _ = (23 * (W0 + W1 + W2 + W3)) * pm := by rw [← Nat.mul_assoc]
          _ ≤ (58 * Wq) * pm := Nat.mul_le_mul_right pm gw
          _ = Wq * (pm * 58) := by rw [Nat.mul_comm 58 Wq, Nat.mul_assoc, Nat.mul_comm pm 58]
      exact hpf4 h0 h1 h2 h3 hw2
  have hsum_all : ∀ k, k ≤ 32 → ((List.range k).flatMap (fun q =>
      let (a, bc) := sft32Win.getD q (0, 0, 0)
      (sft32From q n).map (fun rest => a :: bc.1 :: bc.2 :: rest))).length * 23 ^ n ≤
      ((List.range k).map (fun q => sft32Wt.getD q 0)).sum * 58 ^ n := by
    intro k; induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hcur := hfrom n k (by omega)
      rw [List.range_succ, List.flatMap_append, List.length_append, List.map_append, List.sum_append]
      simp only [List.flatMap_singleton, List.length_map, List.map_singleton, List.sum_singleton]
      rw [Nat.add_mul, Nat.add_mul]
      exact Nat.add_le_add hprev hcur
  have h32 := hsum_all 32 (Nat.le_refl 32)
  unfold sft32Words
  rwa [htab.1] at h32

def erLoopL (bs : List Bool) (t : Nat) : Bool :=
  if t % 4 = 3 then bs.getD (t / 4) false else false
def erLoopC (bs : List Bool) (t : Nat) : Bool :=
  if t % 4 = 3 then bs.getD (t / 4) false else false

theorem twoColLegal_realizable_lower_bound (bs1 bs2 : List Bool) (hlen : bs1.length = bs2.length) :
    (∃ R Z, update (erLoopL bs1) (erLoopC bs1) R ∧ update (erLoopC bs1) R Z) ∧
    ((∀ t < 4 * bs1.length, erLoopL bs1 t = erLoopL bs2 t) → bs1 = bs2) := by
  refine ⟨(two_columns _ _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t hc
    dsimp [erLoopC] at hc
    have hm3 : t % 4 = 3 := by by_cases h : t % 4 = 3; exact h; simp [h] at hc
    simp only [hm3, ↓reduceIte] at hc
    have hm0 : (t + 1) % 4 ≠ 3 := by omega
    unfold required erLoopL erLoopC; simp only [hm3, hm0, ↓reduceIte]; rw [hc]; rfl
  · intro t hc0 hc1 hreq
    unfold required at hreq; rw [hc1, Bool.xor_false] at hreq; dsimp [erLoopL] at hreq
    have hm3 : t % 4 = 3 := by by_cases h : t % 4 = 3; exact h; simp [h] at hreq
    simp only [hm3, ↓reduceIte] at hreq
    dsimp [erLoopC] at hc0; simp only [hm3, ↓reduceIte] at hc0; rw [hreq] at hc0; cases hc0
  · intro t _ hc1 _ _
    dsimp [erLoopC] at hc1
    have hm1 : (t + 1) % 4 = 3 := by by_cases h : (t + 1) % 4 = 3; exact h; simp [h] at hc1
    have hm2 : (t + 2) % 4 ≠ 3 := by omega
    have hm3 : (t + 2 + 1) % 4 ≠ 3 := by omega
    unfold required erLoopL erLoopC; simp only [hm2, hm3, ↓reduceIte]; rfl
  · intro heq
    apply List.ext_getElem hlen
    intro i hi1 hi2
    have h4 := heq (4 * i + 3) (by omega)
    have hd1 : (4 * i + 3) % 4 = 3 ∧ (4 * i + 3) / 4 = i := by omega
    simp only [erLoopL, hd1.1, ↓reduceIte, hd1.2, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, Option.getD_some] at h4
    exact h4

def lucas : Nat → Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

def altSftNext : Nat → List (Bool × Bool × Nat)
  | 0 => [(false, false, 2), (false, true, 3)]
  | 1 => [(false, false, 2), (false, true, 3), (true, false, 4)]
  | 2 => [(true, false, 0)]
  | 3 => [(true, false, 1)]
  | _ => [(false, false, 2), (false, true, 3)]

def altSftFrom (st : Nat) : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (altSftNext st).flatMap (fun item =>
      (altSftFrom item.2.2 k).map (fun rest => item.1 :: item.2.1 :: rest))

def AltTwoColWords : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false, false], [false, true], [true, false]]
  | k + 2 =>
    ((altSftFrom 0 k).map ([false, false, true, false] ++ ·)) ++
    ((altSftFrom 1 k).map ([false, true, true, false] ++ ·)) ++
    ((altSftFrom 2 k).map ([true, false, false, false] ++ ·)) ++
    ((altSftFrom 3 k).map ([true, false, false, true] ++ ·)) ++
    ((altSftFrom 4 k).map ([true, false, true, false] ++ ·))

private def altSum (r : Nat) : Nat :=
  (altSftFrom 0 r).length + (altSftFrom 1 r).length + (altSftFrom 2 r).length + (altSftFrom 3 r).length + (altSftFrom 4 r).length

private def lucasTarget (r : Nat) : Nat :=
  if (r + 2) % 2 = 1 then 2 * lucas (r + 2) + 1 else 2 * lucas (r + 2) - 1

theorem altCol_twoColLegal_exact_lucas (m : Nat) :
    (AltTwoColWords (m + 1)).length =
      if (m + 1) % 2 = 1 then 2 * lucas (m + 1) + 1 else 2 * lucas (m + 1) - 1 := by
  cases m with
  | zero => rfl
  | succ k =>
    have hs_step : ∀ u,
        (altSftFrom 0 (u + 1)).length = (altSftFrom 2 u).length + (altSftFrom 3 u).length ∧
        (altSftFrom 1 (u + 1)).length = (altSftFrom 2 u).length + (altSftFrom 3 u).length + (altSftFrom 4 u).length ∧
        (altSftFrom 2 (u + 1)).length = (altSftFrom 0 u).length ∧
        (altSftFrom 3 (u + 1)).length = (altSftFrom 1 u).length ∧
        (altSftFrom 4 (u + 1)).length = (altSftFrom 2 u).length + (altSftFrom 3 u).length := by
      intro u; refine ⟨by rw [altSftFrom]; simp [altSftNext], by rw [altSftFrom]; simp [altSftNext]; omega, by rw [altSftFrom]; simp [altSftNext], by rw [altSftFrom]; simp [altSftNext], by rw [altSftFrom]; simp [altSftNext]⟩
    have hrec_sum : ∀ r, altSum (r + 3) = 2 * altSum (r + 1) + altSum r := by
      intro r
      have s0 := hs_step r; have s1 := hs_step (r + 1); have s2 := hs_step (r + 1 + 1)
      unfold altSum
      rw [show r + 3 = r + 1 + 1 + 1 by omega]
      omega
    have hluc_pos : ∀ n, 1 ≤ lucas n := by
      intro n; induction n using Nat.strongRecOn with
      | ind n ih =>
        rcases n with _ | _ | n'
        · decide
        · decide
        · have a := ih (n' + 1) (by omega); have b := ih n' (by omega); simp only [lucas]; omega
    have hrec_tgt : ∀ r, lucasTarget (r + 3) = 2 * lucasTarget (r + 1) + lucasTarget r := by
      intro r
      have hl1 : lucas (r + 4) = lucas (r + 1 + 2) + lucas (r + 2) := rfl
      have hl2 : lucas (r + 3 + 2) = lucas (r + 4) + lucas (r + 1 + 2) := rfl
      have hp2 := hluc_pos (r + 2); have hp3 := hluc_pos (r + 1 + 2); have hp5 := hluc_pos (r + 3 + 2)
      unfold lucasTarget
      by_cases hpar : (r + 2) % 2 = 1
      · have p3 : (r + 1 + 2) % 2 ≠ 1 := by omega
        have p5 : (r + 3 + 2) % 2 ≠ 1 := by omega
        simp only [hpar, p3, p5, ↓reduceIte]; omega
      · have p3 : (r + 1 + 2) % 2 = 1 := by omega
        have p5 : (r + 3 + 2) % 2 = 1 := by omega
        simp only [hpar, p3, p5, ↓reduceIte]; omega
    have heq_triple : ∀ r, altSum r = lucasTarget r ∧ altSum (r + 1) = lucasTarget (r + 1) ∧ altSum (r + 2) = lucasTarget (r + 2) := by
      intro r; induction r with
      | zero => decide
      | succ r ih =>
        refine ⟨ih.2.1, ih.2.2, ?_⟩
        rw [show r + 1 + 2 = r + 3 by omega, hrec_sum r, hrec_tgt r, ih.1, ih.2.1]
    have htot : (AltTwoColWords (k + 2)).length = altSum k := by
      rw [AltTwoColWords]; unfold altSum; simp; omega
    rw [htot, (heq_triple k).1]; rfl

end Ruliology.CellularAutomata.Rule30EasternRealizability
