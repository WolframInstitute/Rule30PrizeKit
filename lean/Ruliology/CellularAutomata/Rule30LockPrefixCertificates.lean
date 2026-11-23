module

public import Ruliology.CellularAutomata.Rule30Certificates.LockRing728
public import Ruliology.CellularAutomata.Rule30Blocks
public import Ruliology.CellularAutomata.Rule30WhiteEnd

/-!
# Finite right-prefix certificates for the width-30 seven-phase lock

Troy Lowry with OpenAI Codex found the single-seed age-364 construction, proved
that its first 80 positive cells force phase 6 at tick 95, and proved the sharp
seven-site moving-edge disagreement (WolframInstitute/Rule30PrizeKit, PR #378).
His construction and the maintainer's question on that PR motivated this work.
The 728-cell periodic ring and its inverse recurrence below are adapted from
Lowry's source. The lock and its seven-phase evolution are from kit PR #227.
The compactness proof follows the kit's Rule30ResetCompactness.

Here a finite branching certificate is equivalent to entry for every infinite
completion. Its largest leaf time gives a deadline for the actual singleton
centre. The exclusion of eventual period two assumes arbitrarily late
occurrences of certified right prefixes at black-centre ages.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30LockPrefixCertificates

set_option Elab.async false

/-! ## Compactness and the finite-cone test -/

namespace PrefixBits
abbrev enc (k : Nat) (f : Nat → Bool) := Rule30WhiteEnd.enc f k
theorem enc_lt (k : Nat) (f : Nat → Bool) : enc k f < 2^k :=
  Rule30WhiteEnd.enc_lt f k
theorem testBit_enc (k : Nat) (f : Nat → Bool) (j : Nat) :
    (enc k f).testBit j = (decide (j<k) && f j) :=
  Rule30WhiteEnd.enc_testBit f k j
end PrefixBits

open Rule30SidewaysLocks PrefixBits

private def Often (P : Nat → Prop) := ∀ bound, ∃ i, bound ≤ i ∧ P i

private theorem split_often {P : Nat → Prop} (h : Often P) (f : Nat → Bool) :
    ∃ b, Often (fun i => P i ∧ f i = b) := by
  classical
  by_cases ht : Often (fun i => P i ∧ f i = true)
  · exact ⟨true, ht⟩
  · simp only [Often, Classical.not_forall, not_exists, not_and] at ht
    obtain ⟨u, hu⟩ := ht
    refine ⟨false, fun bound => ?_⟩
    obtain ⟨i, hi, pi⟩ := h (max bound u)
    exact ⟨i, by omega, pi, Bool.eq_false_iff.mpr (hu i (by omega) pi)⟩

private structure Pool where
  pred : Nat → Prop
  often : Often pred

private noncomputable def pools (bits : Nat → Nat → Bool) : Nat → Pool
  | 0 => ⟨fun _ => True, fun n => ⟨n, Nat.le_refl _, trivial⟩⟩
  | n+1 =>
    let p := pools bits n
    let pick := split_often p.often (fun i => bits i n)
    ⟨_, pick.choose_spec⟩

private theorem limit_prefix (bits : Nat → Nat → Bool) :
    ∃ x : Nat → Bool, ∀ n, Often (fun i => ∀ j, j < n → bits i j = x j) := by
  let x := fun n => (split_often (pools bits n).often (fun i => bits i n)).choose
  have matchBits (n i) (h : (pools bits n).pred i) : ∀ j, j < n → bits i j = x j := by
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      change (pools bits n).pred i ∧ bits i n = x n at h
      intro j hj
      by_cases eq : j = n
      · exact eq ▸ h.2
      · exact ih h.1 j (by omega)
  exact ⟨x, fun n bound => by
    obtain ⟨i,hi,h⟩ := (pools bits n).often bound
    exact ⟨i,hi,matchBits n i h⟩⟩

def HasPrefix (m c : Nat) (R : Nat → Bool) : Prop :=
  ∀ i, i < m → R (i+1) = c.testBit i

def Locked (R : Nat → Bool) (j : Nat) : Prop :=
  ∃ k : Fin 7, winW 30 R (1+2*j) ∈ cls 30 lock7Codes k.val

private theorem window_congr (R S : Nat → Bool) (W t : Nat)
    (same : ∀ i, i < W+t → R (i+1) = S (i+1)) :
    winW W R t = winW W S t := by
  let q := enc (W+t) (fun i => S (i+1))
  have digits (i : Nat) (hi : i < W+t) : S (i+1) = q.testBit i := by
    simp [q, testBit_enc, hi]
  exact (winW_prefix (R:=R) (W:=W) (c:=q) (t0:=t)
    (fun i hi => (same i hi).trans (digits i hi))).trans (winW_prefix (R:=S) digits).symm

theorem locked_later {R : Nat → Bool} {j J : Nat} (le : j ≤ J) (hit : Locked R j) : Locked R J := by
  obtain ⟨k, hk⟩ := hit
  have future := lock_forever lock7_ok (by decide) R (t0:=1+2*j) (by omega) k.isLt hk (J-j)
  exact ⟨⟨(k.val + (J-j))%7, by omega⟩,
    by simpa only [show 1+2*j+2*(J-j) = 1+2*J by omega] using future⟩

/-- The phase at the common deadline is allowed to depend on the completion. -/
theorem uniform_lock_iff (m c : Nat) :
    (∀ R, HasPrefix m c R → ∃ j, Locked R j) ↔
    ∃ J, ∀ R, HasPrefix m c R → Locked R J := by
  constructor
  · intro each
    classical
    apply Classical.byContradiction
    intro bad
    simp only [not_exists, Classical.not_forall] at bad
    let rows := fun j => (bad j).choose
    have avoid (j : Nat) : HasPrefix m c (rows j) ∧ ¬Locked (rows j) j := ⟨(bad j).choose_spec.choose, (bad j).choose_spec.choose_spec⟩
    obtain ⟨R, often⟩ := limit_prefix rows
    have pref : HasPrefix m c R := by
      obtain ⟨s, _, agree⟩ := often (m+1) 0
      intro i hi
      exact (agree (i+1) (by omega)).symm.trans ((avoid s).1 i hi)
    obtain ⟨j, hit⟩ := each R pref
    obtain ⟨s, hs, agree⟩ := often (30+(1+2*j)+1) j
    have same : winW 30 R (1+2*j) = winW 30 (rows s) (1+2*j) :=
      window_congr _ _ _ _ (fun i hi => (agree (i+1) (by omega)).symm)
    obtain ⟨k, hk⟩ := hit
    exact (avoid s).2 (locked_later hs ⟨k, same ▸ hk⟩)
  · rintro ⟨J,h⟩ R hR
    exact ⟨J,h R hR⟩


/-- Site zero is the imposed driver. Positive cells below m are the fixed prefix;
the free suffix is read least-significant-bit first and zero-filled beyond q. -/
def joinBits (m c q : Nat) : Nat → Bool
  | 0 => false
  | i+1 => if i<m then c.testBit i else q.testBit (i-m)

/-- Executable check of the 2^(31+2J-m) assignments of free light-cone bits,
using natural subtraction. Fixed bits are never enumerated. -/
def checkCover (m c J : Nat) : Bool :=
  (List.range (2^(31+2*J-m))).all fun q =>
    decide (∃ k : Fin 7, winW 30 (joinBits m c q) (1+2*J) ∈ cls 30 lock7Codes k.val)

theorem checkCover_spec (m c J : Nat) : checkCover m c J = true ↔
    ∀ R, HasPrefix m c R → Locked R J := by
  simp only [checkCover, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro check R pref
    let q := enc (31+2*J-m) (fun i => R (m+i+1))
    obtain ⟨k,hk⟩ := check q (enc_lt _ _)
    have same : winW 30 R (1+2*J) = winW 30 (joinBits m c q) (1+2*J) := by
      apply window_congr
      intro i hi
      by_cases small : i<m
      · simpa [joinBits,small] using pref i small
      · have hsub : i-m<31+2*J-m := by omega
        simp [joinBits,small,q,testBit_enc,hsub,show m+(i-m)=i by omega]
    exact ⟨k,same.symm ▸ hk⟩
  · intro uniform q _
    exact uniform (joinBits m c q) (fun i hi => by simp [joinBits,hi])


/-! ## A sound calculation with unknown input bits -/

namespace Rule30LockCube

open Rule30StripCertificates Rule30Ether Rule30PeriodTwoCoupled Rule30SidewaysLocks

inductive Tri where | off | on | any deriving DecidableEq

def known : Bool → Tri | false => .off | true => .on

def Fits : Tri → Bool → Prop | .off, b => b=false | .on, b => b=true | .any, _ => True

def tor : Tri → Tri → Tri
  | .on,_ | _,.on => .on
  | .off,.off => .off
  | _,_ => .any

def txor : Tri → Tri → Tri
  | .off, b => b
  | .on,.off => .on
  | .on,.on => .off
  | _,_ => .any

private theorem known_fits (b : Bool) : Fits (known b) b := by cases b <;> rfl
private theorem or_sound {a b x y} (ha : Fits a x) (hb : Fits b y) : Fits (tor a b) (x || y) := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all [Fits,tor]
private theorem xor_sound {a b x y} (ha : Fits a x) (hb : Fits b y) : Fits (txor a b) (xor x y) := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all [Fits,txor]

inductive Matches : List Tri → List Bool → Prop where
  | nil : Matches [] []
  | cons {a b xs ys} (head : Fits a b) (tail : Matches xs ys) : Matches (a::xs) (b::ys)

def line : List Tri → List Tri
  | a::b::c::r => txor a (tor b c) :: line (b::c::r)
  | _ => []

private theorem line_sound : ∀ {u v}, Matches u v → Matches (line u) (lin3 v)
  | [], _, .nil => .nil
  | [_], _, .cons _ .nil => .nil
  | [_,_], _, .cons _ (.cons _ .nil) => .nil
  | _::_::_::_, _, .cons ha (.cons hb (.cons hc tail)) =>
    .cons (xor_sound ha (or_sound hb hc)) (line_sound (.cons hb (.cons hc tail)))

def run : Nat → Nat → List Tri → List Tri
  | _,0,row => row
  | t,n+1,row => run (t+1) n (line (known (altCol t)::row))

private theorem run_sound (n t : Nat) {u v} (h : Matches u v) :
    Matches (run t n u) (Rule30GateTrap.evolve t n v) := by
  induction n generalizing t u v with
  | zero => exact h
  | succ n ih => exact ih (t+1) (line_sound (.cons (known_fits _) h))

def slice (f : Nat → Tri) : Nat → List Tri
  | 0 => []
  | n+1 => f 0 :: slice (fun i => f (i+1)) n

private theorem slice_sound (n : Nat) (f : Nat → Tri) (g : Nat → Bool)
    (h : ∀ i,i<n → Fits (f i) (g i)) : Matches (slice f n) (seg g n) := by
  induction n generalizing f g with
  | zero => exact .nil
  | succ n ih => exact .cons (h 0 (by omega)) (ih _ _ (fun i hi => h (i+1) (by omega)))

def input (m c n : Nat) := slice (fun i => if i<m then known (c.testBit i) else .any) n

theorem driven_sound (R : Nat → Bool) (W t m c : Nat)
    (pref : ∀ i,i<m → R (i+1)=c.testBit i) :
    Matches (run 0 t (input m c (W+t))) (winW W R t) := by
  have eq := Rule30GateTrap.rowOf_evolve R t 0 W
  rw [Nat.zero_add] at eq
  unfold winW
  rw [eq]
  apply run_sound
  apply slice_sound
  intro i _
  by_cases hi : i<m
  · simp only [hi,ite_true,Nat.zero_add,drv_init _ _ _ (Nat.succ_pos i),pref i hi]
    exact known_fits _
  · simp [hi,Fits]

def choices : Tri → List Bool | .off => [false] | .on => [true] | .any => [false,true]

def expand : List Tri → List (List Bool)
  | [] => [[]]
  | a::r => (choices a).flatMap fun b => (expand r).map (b::·)

private theorem enumerated {u v} (fit : Matches u v) : v∈expand u := by
  induction fit with
  | nil => simp [expand]
  | @cons a b xs ys h _ ih =>
    apply List.mem_flatMap.mpr
    refine ⟨b, ?_, List.mem_map.mpr ⟨ys,ih,rfl⟩⟩
    cases a <;> cases b <;> simp_all [choices,Fits]

def check (target : List Bool → Bool) (W t m c : Nat) : Bool :=
  (expand (run 0 t (input m c (W+t)))).all target

theorem check_sound {target : List Bool → Bool} {W t m c : Nat} (checked : check target W t m c=true)
    (R : Nat → Bool) (pref : ∀ i,i<m → R (i+1)=c.testBit i) : target (winW W R t)=true :=
  List.all_eq_true.mp checked _ (enumerated (driven_sound R W t m c pref))

def Forces (P : (Nat → Bool) → Prop) (m c : Nat) : Prop :=
  ∀ R, (∀ i,i<m → R (i+1)=c.testBit i) → P R

theorem split_forces {P m c} (size : c<2^m)
    (low : Forces P (m+1) c) (high : Forces P (m+1) (2^m+c)) : Forces P m c := by
  intro R pref
  have z := Nat.testBit_lt_two_pow size
  cases bit : R (m+1) with
  | false =>
    apply low R
    intro i hi
    by_cases lt : i<m
    · exact pref i lt
    · have eq : i=m := by omega
      simpa [eq,z] using bit
  | true =>
    apply high R
    intro i hi
    by_cases lt : i<m
    · simpa only [Nat.testBit_two_pow_add_gt lt] using pref i lt
    · have eq : i=m := by omega
      simpa [eq,Nat.testBit_two_pow_add_eq,z] using bit

end Rule30LockCube

open Rule30SidewaysLocks

/-! ## Branching certificates -/

inductive Certificate where
  | hit (sample : Nat) (phase : Fin 7)
  | split (zero one : Certificate)
  deriving Repr

def Certificate.deadline : Certificate → Nat
  | .hit j _ => j
  | .split l r => max l.deadline r.deadline

/-- The time and phase written on a leaf of this tree. -/
def Certificate.hasHit (j : Nat) (k : Fin 7) : Certificate → Prop
  | .hit s p => j = s ∧ k = p
  | .split l r => l.hasHit j k ∨ r.hasHit j k

/-- A fully specified cone is evaluated directly. For a partial cone, ternary
evolution overapproximates its outputs. A lock class can contain all of them only
when it has at least as many words as there are fillings of the unknown cells. -/
def checkLeaf (m c j : Nat) (k : Fin 7) : Bool :=
  let tick := 1+2*j
  let words := cls 30 lock7Codes k.val
  if 30+tick ≤ m then
    words.contains (Rule30GateTrap.evolve 0 tick (decodeW (30+tick) c))
  else
    let cube := Rule30LockCube.run 0 tick (Rule30LockCube.input m c (30+tick))
    decide (2^(cube.count .any) ≤ words.length) &&
      (Rule30LockCube.expand cube).all words.contains

private theorem leaf_sound {m c j : Nat} {k : Fin 7} (pass : checkLeaf m c j k = true)
    {R : Nat → Bool} (pref : HasPrefix m c R) :
    winW 30 R (1+2*j) ∈ cls 30 lock7Codes k.val := by
  simp only [checkLeaf] at pass
  split at pass
  · rename_i full
    rw [winW_prefix (c := c) (fun i hi => pref i (by omega))]
    simpa using pass
  · have ok := (Bool.and_eq_true_iff.mp pass).2
    have hit := Rule30LockCube.check_sound (W := 30) (t := 1+2*j) (m := m) (c := c)
      (target := fun w => (cls 30 lock7Codes k.val).contains w) ok R pref
    simpa using hit

def verify : Certificate → Nat → Nat → Bool
  | .hit j k, m, c => checkLeaf m c j k
  | .split l r, m, c => verify l (m+1) c && verify r (m+1) (2^m+c)

/-- Bits above the supplied prefix length are ignored. -/
def accepts (tree : Certificate) (m c : Nat) : Bool := verify tree m (c%2^m)

private theorem prefix_mod (R : Nat → Bool) (m c : Nat) :
    HasPrefix m (c%2^m) R ↔ HasPrefix m c R := by
  constructor <;> intro h i hi <;> simpa [Nat.testBit_mod_two_pow,hi] using h i hi

private theorem verify_hit (tree : Certificate) {m c : Nat} (size : c<2^m)
    (pass : verify tree m c = true) : ∀ R, HasPrefix m c R → ∃ j k, tree.hasHit j k ∧
      j ≤ tree.deadline ∧ winW 30 R (1+2*j) ∈ cls 30 lock7Codes k.val := by
  induction tree generalizing m c with
  | hit j k => exact fun _ h => ⟨j,k,⟨rfl,rfl⟩,Nat.le_refl _,leaf_sound pass h⟩
  | split l r il ir =>
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp pass
    refine Rule30LockCube.split_forces (P := fun R => ∃ j k, (l.split r).hasHit j k ∧
      j ≤ (l.split r).deadline ∧ winW 30 R (1+2*j) ∈ cls 30 lock7Codes k.val) size ?_ ?_
    · intro R h
      obtain ⟨j,k,mark,bound,hit⟩ := il (by rw [Nat.pow_succ]; omega) left R h
      exact ⟨j,k,Or.inl mark,Nat.le_trans bound (Nat.le_max_left _ _),hit⟩
    · intro R h
      obtain ⟨j,k,mark,bound,hit⟩ := ir (by rw [Nat.pow_succ]; omega) right R h
      exact ⟨j,k,Or.inr mark,Nat.le_trans bound (Nat.le_max_right _ _),hit⟩

/-- Each completion actually reaches the time and phase on one of the leaves. -/
theorem accepts_hit {tree : Certificate} {m c : Nat} (pass : accepts tree m c = true)
    {R : Nat → Bool} (pref : HasPrefix m c R) : ∃ j k, tree.hasHit j k ∧
      j ≤ tree.deadline ∧ winW 30 R (1+2*j) ∈ cls 30 lock7Codes k.val :=
  verify_hit tree (m := m) (c := c%2^m) (Nat.mod_lt _ (Nat.two_pow_pos _))
    pass R ((prefix_mod R m c).mpr pref)

theorem accepts_sound {tree : Certificate} {m c : Nat} (pass : accepts tree m c = true)
    {R : Nat → Bool} (pref : HasPrefix m c R) : Locked R tree.deadline := by
  obtain ⟨j,k,_,bound,hit⟩ := accepts_hit pass pref
  exact locked_later bound ⟨k,hit⟩

/-- An accepted single leaf also identifies the phase at its specified time. -/
theorem accepted_phase {j m c : Nat} {k : Fin 7} (pass : accepts (.hit j k) m c = true)
    {R : Nat → Bool} (pref : HasPrefix m c R) :
    winW 30 R (1+2*j) ∈ cls 30 lock7Codes k.val :=
  leaf_sound (m := m) (c := c%2^m) (j := j) (k := k) pass ((prefix_mod R m c).mpr pref)

private theorem complete_at (j n m c : Nat) (enough : 30+(1+2*j) ≤ m+n)
    (all : ∀ R, HasPrefix m c R → Locked R j) :
    ∃ tree, verify tree m c = true ∧ tree.deadline = j := by
  induction n generalizing m c with
  | zero =>
    obtain ⟨k,hit⟩ := all (rh c) (rh_prefix c m)
    have full : 30+(1+2*j) ≤ m := by omega
    rw [winW_prefix (c := c) (rh_prefix c (30+(1+2*j)))] at hit
    exact ⟨.hit j k, by simpa [verify,checkLeaf,full] using hit, rfl⟩
  | succ n ih =>
    obtain ⟨l,pl,dl⟩ := ih (m+1) c (by omega) (fun R h => all R (fun i hi => h i (by omega)))
    obtain ⟨r,pr,dr⟩ := ih (m+1) (2^m+c) (by omega) (fun R h => all R (fun i hi => by
      simpa only [Nat.testBit_two_pow_add_gt hi] using h i (by omega)))
    exact ⟨.split l r, by simp [verify,pl,pr], by simp [Certificate.deadline,dl,dr]⟩

/-- At each proposed deadline the certificates are exact, including when the
successful phase differs from branch to branch. -/
theorem deadline_iff (m c j : Nat) :
    (∀ R, HasPrefix m c R → Locked R j) ↔
    ∃ tree, accepts tree m c = true ∧ tree.deadline ≤ j := by
  constructor
  · intro h
    obtain ⟨tree,pass,bound⟩ := complete_at j (31+2*j-m) m (c%2^m) (by omega)
      (fun R pref => h R ((prefix_mod R m c).mp pref))
    exact ⟨tree,pass,by omega⟩
  · rintro ⟨tree,pass,bound⟩ R pref
    exact locked_later bound (accepts_sound pass pref)

/-- The exhaustive finite-cone check and the branching certificates express the same
fixed-deadline property for every length and prefix code. -/
theorem checkCover_iff_certificate (m c j : Nat) : checkCover m c j = true ↔
    ∃ tree, accepts tree m c = true ∧ tree.deadline ≤ j :=
  (checkCover_spec m c j).trans (deadline_iff m c j)

/-- A finite certificate exists exactly for those prefixes whose every
completion eventually reaches a phase of the seven-lock. -/
theorem eventual_iff (m c : Nat) :
    (∀ R, HasPrefix m c R → ∃ j, Locked R j) ↔ ∃ tree, accepts tree m c = true := by
  rw [uniform_lock_iff]
  constructor
  · rintro ⟨j,h⟩
    obtain ⟨tree,pass,_⟩ := (deadline_iff m c j).mp h
    exact ⟨tree,pass⟩
  · rintro ⟨tree,pass⟩
    exact ⟨tree.deadline,fun _ pref => accepts_sound pass pref⟩

/-! ## A worked example and its one-cell boundary -/

open Rule30SidewaysLocks Rule30GateTrap
set_option maxRecDepth 30000
set_option maxHeartbeats 32000000

/-- The lock's phases 1 and 3 are both kicks, two samples apart.
The trap excludes this after every kick. -/
theorem locked_outside_trap {R : Nat → Bool} {j : Nat} (hit : Locked R j) :
    win R (1+2*j) ∉ trap := by
  intro inside
  obtain ⟨k,hk⟩ := hit
  have hh : winW 30 R (2*j+1) ∈ cls 30 lock7Codes k.val := by
    rwa [Nat.add_comm 1] at hk
  let n := 8-k.val
  have t1 : (k.val+n)%7 = 1 := by dsimp [n]; have := k.isLt; omega
  have t3 : (k.val+(n+2))%7 = 3 := by dsimp [n]; have := k.isLt; omega
  have u1 := u_of_lock (V:=29) lock7_ok (by decide) R k.isLt hh n
  have u3 := u_of_lock (V:=29) lock7_ok (by decide) R k.isLt hh (n+2)
  rw [t1] at u1
  rw [t3] at u3
  change Rule30PeriodTwoSideways.u R (j+(n+2)) = true at u3
  have u1' : Rule30PeriodTwoSideways.u R (j+n) = true := u1
  have u3' : Rule30PeriodTwoSideways.u R (j+n+2) = true := by simpa only [Nat.add_assoc] using u3
  rcases gaps_of_entry R (by omega : (1+2*j)%2=1) inside (j+n) (by omega) u1' with q | q
  · exact Bool.noConfusion (q.2.1.symm.trans u3')
  · exact Bool.noConfusion (q.2.1.symm.trans u3')
def avoidSeed : Nat := 150212610825

theorem avoidSeed_trap_at83 : win (rh avoidSeed) 83 ∈ trap := by
  have eq : winW 16 (rh avoidSeed) 83 = decode entryCode := by
    rw [winW_prefix (rh_prefix avoidSeed 99)]
    decide +kernel
  change winW 16 (rh avoidSeed) 83 ∈ trap
  rw [eq]
  exact entry_mem

theorem avoidSeed_no_lock : ¬ ∃ j, Locked (rh avoidSeed) j := by
  rintro ⟨j,h⟩
  let s := max j 41
  have hj : j ≤ s := Nat.le_max_left _ _
  have ht : 41 ≤ s := Nat.le_max_right _ _
  have t := win_mem_trap (rh avoidSeed) (by decide : 83%2=1) avoidSeed_trap_at83 (s-41)
  have no := locked_outside_trap (locked_later hj h)
  exact no (by simpa only [show 83+2*(s-41)=1+2*s by omega] using t)

/-- A single split on site 30 certifies phase four on the first white tick. -/
def example29 : Certificate := .split (.hit 0 4) (.hit 0 4)

theorem example29_check :
    accepts example29 29 157190921 = true ∧ accepts (.hit 0 4) 29 157190921 = false := by
  decide +kernel

theorem example29_phase {R : Nat → Bool} (pref : HasPrefix 29 157190921 R) :
    winW 30 R 1 ∈ cls 30 lock7Codes 4 := by
  obtain ⟨j,k,mark,_,hit⟩ := accepts_hit example29_check.1 pref
  simp [example29,Certificate.hasHit] at mark
  obtain ⟨rfl,rfl⟩ := mark
  exact hit

theorem sharp_for_eventual_entry :
    (∀ R, HasPrefix 29 157190921 R → Locked R 0) ∧
    (HasPrefix 28 157190921 (rh avoidSeed) ∧ ¬ ∃ j, Locked (rh avoidSeed) j) := by
  refine ⟨fun R h => ⟨4,example29_phase h⟩, ?_, avoidSeed_no_lock⟩
  have bits : ∀ i : Fin 28, avoidSeed.testBit i.val = (157190921 : Nat).testBit i.val := by
    decide +kernel
  exact fun i hi => (rh_prefix avoidSeed 28 i hi).trans (bits ⟨i,hi⟩)

/-- Comparison with Troy Lowry’s age-364 construction in kit PR #378. The root
fixes 77 of his 80 positive cells; every leaf gives his phase 6 at tick 95. -/
def lowry77Tree : Certificate :=
  let h := Certificate.hit 47 6
  let pair := Certificate.split h h
  .split (.split (.split pair h) h) (.split pair (.split pair (.split pair h)))

theorem lowry_77_passes : accepts lowry77Tree 77 248139127718118986536413 = true := by
  decide +kernel

theorem lowry_77_phase {R : Nat → Bool} (pref : HasPrefix 77 248139127718118986536413 R) :
    winW 30 R 95 ∈ cls 30 lock7Codes 6 := by
  obtain ⟨j,k,mark,_,hit⟩ := accepts_hit lowry_77_passes pref
  simp [lowry77Tree,Certificate.hasHit] at mark
  obtain ⟨rfl,rfl⟩ := mark
  exact hit

/-! ## Lowry’s periodic ring and the singleton centre -/

open Rule30SidewaysLocks Rule30PeriodTwoSideways BusyBeaverLifetimes
open Rule30ZeroBoundary (zrow zrow_inv zrow_wall)

open Rule30LockRing728

private theorem near_all (R : Nat → Bool) {s0 k : Nat} (hk : k < 7)
    (entry : winW 30 R (2*s0+1) ∈ cls 30 lock7Codes k) (t : Nat) :
    zrow (Psi R) (2*s0+1+t) 1 = tile (2*(k+1)+t) 1 := by
  rw [Psi_col]
  by_cases h : t % 2 = 0
  · obtain ⟨q,rfl⟩ : ∃ q,t=2*q := ⟨t/2,by omega⟩
    rw [show 2*s0+1+2*q=2*(s0+q)+1 by omega, alt_odd,
        u_of_lock (V:=29) lock7_ok (by decide) R (s0:=s0) hk entry,
        show 2*(k+1)+2*q=2*((k+1)+q) by omega, tile_even]
    rw [show (6+(k+1+q))%7=(k+q)%7 by omega]
  · obtain ⟨q,rfl⟩ : ∃ q,t=2*q+1 := ⟨t/2,by omega⟩
    rw [show 2*s0+1+(2*q+1)=2*(s0+q+1) by omega, alt_even,
        show 2*(k+1)+(2*q+1)=2*(k+1+q)+1 by omega, tile_odd]

theorem all_locked_tile (R : Nat → Bool) {s0 k : Nat} (hk : k < 7)
    (entry : winW 30 R (2*s0+1) ∈ cls 30 lock7Codes k) (d t : Nat) :
    zrow (Psi R) (2*s0+1+t) (d+1) = tile (2*(k+1)+t) (d+1) := by
  have pair : ∀ j, (∀ s, zrow (Psi R) (2*s0+1+s) (j+1) = tile (2*(k+1)+s) (j+1)) ∧
      (∀ s, zrow (Psi R) (2*s0+1+s) (j+2) = tile (2*(k+1)+s) (j+2)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨near_all R hk entry,fun s => ?_⟩
      rw [zrow_inv (Psi R) (2*s0+1+s) 0, zrow_wall]
      simp only [Nat.zero_add,show 2*s0+1+s+1=2*s0+1+(s+1) by omega, near_all R hk entry,
        show 2*(k+1)+(s+1)=2*(k+1)+s+1 by omega,wall_inv]
    | succ j ih =>
      refine ⟨ih.2,fun s => ?_⟩
      rw [zrow_inv (Psi R) (2*s0+1+s) (j+1), show 2*s0+1+s+1=2*s0+1+(s+1) by omega,
          ih.2,ih.2,ih.1, show 2*(k+1)+(s+1)=2*(k+1)+s+1 by omega, tile_inv (2*(k+1)+s) (j+1)]
  exact (pair d).1 t

open Rule30Realization Rule30PeriodTwoSideways Rule30PeriodTwoCoupled Rule30SidewaysLocks
open Rule30ZeroBoundary (zrow)

/-- Finite-time reconstruction with two independent initial left halves, sharing the positive right half. -/
theorem finite_center_cone {x y : Int → Bool} (right : ∀ p, 1 ≤ p → x p = y p)
    {t d : Nat} (trace : ∀ s, s ≤ t+d → evol x s 0 = evol y s 0) :
    evol x t (-(d:Int)) = evol y t (-(d:Int)) := by
  let c := fun s => evol x s 0
  let c' := fun s => evol y s 0
  have rx := realize x c
  have ry := realize x c'
  have X : x = conf x c := unique (fun p hp => (rx.1 p hp).symm) (fun s => (rx.2 s).symm)
  have Y : y = conf x c' := unique (fun p hp => (right p hp).symm.trans (ry.1 p hp).symm) (fun s => (ry.2 s).symm)
  calc
    _ = evol (conf x c) t (-(d:Int)) := congrArg (fun z => evol z t (-(d:Int))) X
    _ = lc x c d t := by rw [evol_conf]; simp [show ¬1 ≤ -(d:Int) by omega]
    _ = lc x c' d t := lc_congr x d t (fun s hs => trace s (by omega))
    _ = evol (conf x c') t (-(d:Int)) := by rw [evol_conf]; simp [show ¬1 ≤ -(d:Int) by omega]
    _ = _ := congrArg (fun z => evol z t (-(d:Int))) Y.symm

theorem seed_restart (A t : Nat) (p : Int) : evol (Rule30Jen.cell A) t p = Rule30Jen.cell (A+t) p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    change Rule30Jen.rule _ _ _ = Rule30Jen.rule _ _ _
    rw [ih,ih,ih]
    rfl

private theorem seed_packed (t : Nat) : Rule30Jen.cell t = BusyBeaverLifetimes.TwoColor.cell 30 1 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Rule30Blocks.cell_succ]
    funext j
    change Rule30Jen.rule (Rule30Jen.cell t (j-1)) (Rule30Jen.cell t j) (Rule30Jen.cell t (j+1)) = _
    rw [ih]
    rfl

private theorem edgeWord_period (B : Nat) (h : 2 ≤ B) : Rule30Blocks.plane B % 1024 = edgeWord B := by
  have low (v : Nat) : Rule30Blocks.F v % 2^10 = Rule30Blocks.F (v%2^10) % 2^10 := by
    simp only [Rule30Blocks.F,Nat.xor_mod_two_pow,Nat.or_mod_two_pow,Nat.shiftLeft_eq,Nat.mod_mul_mod,Nat.mod_mod]
  have next : ∀ q : Fin 4, Rule30Blocks.F (edgeWord q) % 1024 = edgeWord (q.val+1) := by decide +kernel
  obtain ⟨j,rfl⟩ : ∃ j,B=2+j := ⟨B-2,by omega⟩
  induction j with
  | zero => decide +kernel
  | succ j ih =>
    change Rule30Blocks.F (Rule30Blocks.plane (2+j)) % 1024 = edgeWord (2+j+1)
    have low1024 (v : Nat) : Rule30Blocks.F v % 1024 = Rule30Blocks.F (v%1024) % 1024 := by
      simpa only [show (2:Nat)^10=1024 by decide] using low v
    rw [low1024,ih (by omega)]
    have r := next ⟨(2+j)%4,by omega⟩
    simp only [edgeWord,Nat.mod_mod,Nat.mod_add_mod] at r ⊢
    exact r

private theorem true_left_edge_word {B : Nat} (hb : 9 ≤ B) (j : Fin 9) :
    Rule30Jen.cell B ((j.val : Int) - (B:Int)) = (edgeWord B).testBit (j.val+1) := by
  rw [seed_packed,Rule30Blocks.cell_eq _ _ (by omega)]
  rw [show (((j.val : Int) - (B:Int)) + (B:Int) + 1).toNat = j.val + 1 by omega]
  have e := Nat.testBit_mod_two_pow (Rule30Blocks.plane B) 10 (j.val+1)
  have hj := j.isLt
  rw [show 2^10=1024 by decide,edgeWord_period B (by omega)] at e
  simpa [show j.val+1 < 10 by omega] using e.symm

theorem nine_at_entry {B : Nat} (hb : 9 ≤ B) (e : Nat) :
    ∃ j : Fin 9, tile (2*e) (B-j.val) ≠ Rule30Jen.cell B ((j.val:Int)-(B:Int)) := by
  obtain ⟨j,ne⟩ := edge_table ⟨e%7,by omega⟩ ⟨B%728,by omega⟩
  refine ⟨j,?_⟩
  rw [true_left_edge_word hb]
  change tile (2*(e%7)) (728+B%728-j.val) ≠ (edgeWord (B%728)).testBit (j.val+1) at ne
  have hj:=j.isLt
  simpa only [tile,edgeWord,show 2*(e%7)%14 = 2*e%14 by omega,
    show (728+B%728-j.val)%728=(B-j.val)%728 by omega,
    show (B%728)%4=B%4 by omega] using ne

def rightAt (A : Nat) (p : Nat) := Rule30Jen.cell A (p:Int)

theorem actual_forced_cone (A t d : Nat) (hd : 0 < d)
    (trace : ∀ s,s ≤ t+d → Rule30Jen.cell (A+s) 0 = altCol s) :
    zrow (Psi (rightAt A)) t d = Rule30Jen.cell (A+t) (-(d:Int)) := by
  let R := rightAt A
  let y := glue (Psi R) R
  have gy (q : Nat) (p : Int) := evol_glue (Psi R) R (Psi_inX R) (Psi_free R) q p
  have r : ∀ p : Int, 1 ≤ p → Rule30Jen.cell A p = y p := by
    intro p hp
    simp [y,glue,R,rightAt,show ¬p<0 by omega,show p≠0 by omega,Int.toNat_of_nonneg (by omega : 0≤p)]
  have eq := finite_center_cone (x:=Rule30Jen.cell A) (y:=y) (t:=t) (d:=d) r (fun s hs => by
    rw [seed_restart,trace s hs,gy,gluedRun_zero])
  rw [seed_restart,gy] at eq
  simpa [gluedRun,hd,R,show -(d:Int)<0 by omega] using eq.symm

private theorem short_starts : ∀ A E : Fin 9, E.val%2=1 → A.val+E.val<9 →
    ∃ h : Fin (A.val+2*E.val+1), Rule30Jen.cell (A.val+h.val) 0 ≠ altCol h.val := by decide +kernel

/-- With the actual right side at age A driven as if the centre alternated from black, entry
at relative odd time E forces a break in the actual centre by relative A+2E, i.e. absolute 2(A+E). -/
theorem actual_center_break {A s0 k : Nat} (hk : k<7)
    (entry : winW 30 (rightAt A) (2*s0+1) ∈ cls 30 lock7Codes k) :
    ∃ h ≤ A+2*(2*s0+1), Rule30Jen.cell (A+h) 0 ≠ altCol h := by
  let E := 2*s0+1
  let B := A+E
  by_cases hb : 9 ≤ B
  · obtain ⟨j,miss⟩ := nine_at_entry hb (k+1)
    have hj := j.isLt
    have ring := all_locked_tile (rightAt A) hk entry (B-j.val-1) 0
    rw [show B-j.val-1+1=B-j.val by omega,Nat.add_zero,Nat.add_zero] at ring
    simp only [Nat.add_zero] at ring
    by_cases witness : ∃ h : Fin (A+2*E+1), Rule30Jen.cell (A+h.val) 0 ≠ altCol h.val
    · obtain ⟨h,bad⟩ := witness
      exact ⟨h.val,by have := h.isLt;dsimp [E] at *; omega,bad⟩
    · exfalso
      have trace (s : Nat) (hs : s≤E+(B-j.val)) : Rule30Jen.cell (A+s) 0 = altCol s := by
        apply Decidable.byContradiction
        intro ne
        exact witness ⟨⟨s,by dsimp [B,E] at *;omega⟩,ne⟩
      have line := actual_forced_cone A E (B-j.val) (by omega) trace
      apply miss
      rw [←ring]
      rw [show (j.val:Int)-(B:Int) = -((B-j.val:Nat):Int) by omega]
      exact line
  · have hA : A<9 := by dsimp [B,E] at hb; omega
    have hE : E<9 := by dsimp [B] at hb; omega
    obtain ⟨z,bad⟩ := short_starts ⟨A,hA⟩ ⟨E,hE⟩ (by change E%2=1;dsimp [E];omega) (by change A+E<9;dsimp [B] at hb;omega)
    exact ⟨z.val,by have := z.isLt;dsimp [E] at *;omega,bad⟩



/-- A finite test on the positive right prefix alone bounds the first disagreement
with black-first alternation at every singleton age A exhibiting that prefix.
The bound is expressed in absolute physical ticks. -/
theorem actual_break_of_checkCover {m c J A : Nat}
    (checked : checkCover m c J = true) (pref : HasPrefix m c (rightAt A)) :
    ∃ h, A+h ≤ 2*(A+(1+2*J)) ∧ Rule30Jen.cell (A+h) 0 ≠ altCol h := by
  obtain ⟨k, entry⟩ := (checkCover_spec m c J).mp checked (rightAt A) pref
  rw [Nat.add_comm 1 (2*J)] at entry
  obtain ⟨h, bound, differs⟩ := actual_center_break k.isLt entry
  exact ⟨h, by omega, differs⟩

/-- A certificate with maximum sample J gives the absolute deadline 2(A+1+2J)
at every age A where its initial cells occur. -/
theorem centre_bound_of_certificate {tree : Certificate} {m c A : Nat}
    (pass : accepts tree m c = true) (pref : HasPrefix m c (rightAt A)) :
    ∃ h, A+h ≤ 2*(A+1+2*tree.deadline) ∧ Rule30Jen.cell (A+h) 0 ≠ altCol h := by
  have checked := (checkCover_iff_certificate m c tree.deadline).mpr ⟨tree,pass,Nat.le_refl _⟩
  obtain ⟨h,bound,miss⟩ := actual_break_of_checkCover checked pref
  exact ⟨h,by omega,miss⟩

/-- A sufficient recurrence hypothesis for excluding a period-two tail. The
certificate, prefix and deadline may vary with the actual black-centre age. -/
theorem no_period_two_of_cofinal_certificates
    (recurs : ∀ B, ∃ A ≥ B, Rule30Jen.cell A 0 = true ∧
      ∃ (m c : Nat) (tree : Certificate), accepts tree m c = true ∧ HasPrefix m c (rightAt A)) :
    ¬ ∃ T, ∀ t, T ≤ t → Rule30Jen.cell (t+2) 0 = Rule30Jen.cell t 0 := by
  rintro ⟨T,per⟩
  obtain ⟨start,alt⟩ := Rule30PeriodTwo.normalize per
  obtain ⟨A,after,black,m,c,tree,pass,pref⟩ := recurs start
  obtain ⟨h,_,miss⟩ := centre_bound_of_certificate pass pref
  obtain ⟨n,even | odd⟩ : ∃ n, A = start+2*n ∨ A = start+2*n+1 :=
    ⟨(A-start)/2,by omega⟩
  · obtain ⟨q,evenTick | oddTick⟩ : ∃ q, h = 2*q ∨ h = 2*q+1 := ⟨h/2,by omega⟩
    · apply miss
      rw [show A+h = start+2*(n+q) by omega, (alt (n+q)).1]
      simp [altCol,evenTick]
    · apply miss
      rw [show A+h = start+2*(n+q)+1 by omega, (alt (n+q)).2]
      simp [altCol,oddTick,show (2*q+1)%2 = 1 by omega]
  · rw [odd,(alt n).2] at black
    contradiction

end Ruliology.CellularAutomata.Rule30LockPrefixCertificates
