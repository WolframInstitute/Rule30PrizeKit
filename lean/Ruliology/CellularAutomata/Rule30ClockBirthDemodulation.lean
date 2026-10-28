module

public import Ruliology.CellularAutomata.Rule30FiniteDiagonals

/-!
# Detecting a clock birth from two right-diagonal observations

For a nonempty finite older prefix `u` that returns after `P > 0` two-step updates,
the two observations of `u ++ [g,h]` determine whether the penultimate bit changes
after `P` updates. When it changes, the same observations recover both observation
streams of `u`. The whole-prefix return is supplied; `P` need not be the least one.

Lists are ordered from the right white edge toward the left. `singleChange p q`
is the literal scan `x XOR (p OR q)`, updating the two remembered *old* bits as it
moves left. `A` uses white memories; `C` uses memories `true,false`; `T = C ∘ A`.
The anchored word `100 ++ u` alternates between `100` and `111`, so its tail evolves
by `T` every two Rule 30 ticks. The observations `r` and `s` are the last tail bit
before and after the first scan. `Rd_observations` identifies them with the even
and odd values of the official right diagonal `Rd x hi (u.length+2)` for any initial
configuration white to the right of `hi` with this finite prefix. Initial data
farther left is arbitrary.

`masked_demodulation` gives the exact Boolean difference identities. The black
anchor rules out two perpetually black observation streams; this turns the masked
identities into the finite `birth_detector`. `demodulation_of_birth` recovers the
older streams, and `observe_birth_transfer` applies this to two equal observed
histories, allowing different older widths.

`observe_birth_phase_transfer` handles opposite-phase histories:
`r_v(t)=s_w(t)` and `s_v(t)=r_w(t+1)`. The rotated finite detector preserves
the flag, and at a nonzero flag the older streams satisfy the same relation,
including its one-update lag. The singleton-parent base obstruction is explicit.
A zero birth flag does not reconstruct the older streams; general mixed-width
phase separation remains open. These statements concern moving right diagonals
and observation streams, not the fixed physical center or reconstruction of the
whole older state.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ClockBirthDemodulation

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def march (x : Nat → Bool) : Nat → Bool
  | 0 => x 0
  | 1 => xor (x 1) (x 0)
  | j+2 => xor (x (j+2)) (x (j+1) || x j)


def Actual (a : Nat → Nat → Bool) : Prop := ∀ t j, a (t+1) j=march (a t) j

def singleChange (p q : Bool) : List Bool → List Bool
  | [] => []
  | x::xs => xor x (p || q) :: singleChange x p xs
def singleStep (xs : List Bool) := singleChange false false xs

theorem singleChange_length (p q : Bool) (xs : List Bool) :
    (singleChange p q xs).length=xs.length := by
  induction xs generalizing p q with
  | nil => rfl
  | cons x xs ih => simp only [singleChange,List.length_cons];rw [ih]
theorem singleStep_length (xs : List Bool) : (singleStep xs).length=xs.length :=
  singleChange_length false false xs

def iter (xs : List Bool) : Nat → List Bool
  | 0 => xs
  | t+1 => singleStep (iter xs t)
def lastBit (d : Bool) : List Bool → Bool
  | [] => d
  | x::xs => lastBit x xs

abbrev A := singleStep
def C (xs : List Bool) := singleChange true false xs
def T (xs : List Bool) := C (A xs)
def titer (xs : List Bool) : Nat → List Bool
  | 0 => xs
  | t+1 => T (titer xs t)
def r (xs : List Bool) := lastBit false xs
def s (xs : List Bool) := r (A xs)
def trace (xs : List Bool) (t : Nat) := r (iter xs t)
def word0 (xs : List Bool) := [true,false,false] ++ xs
def word1 (xs : List Bool) := [true,true,true] ++ A xs

theorem C_length (xs : List Bool) : (C xs).length=xs.length := singleChange_length _ _ _
theorem T_length (xs : List Bool) : (T xs).length=xs.length := by
  rw [T,C_length,singleStep_length]
theorem titer_length (xs : List Bool) (t : Nat) : (titer xs t).length=xs.length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [titer,T_length,ih]
theorem A_nonempty {xs : List Bool} (h : xs ≠ []) : A xs ≠ [] := by
  intro e
  have := singleStep_length xs
  change (A xs).length=xs.length at this
  rw [e] at this
  exact h (List.eq_nil_of_length_eq_zero this.symm)
theorem T_nonempty {xs : List Bool} (h : xs ≠ []) : T xs ≠ [] := by
  intro e
  have := T_length xs
  rw [e] at this
  exact h (List.eq_nil_of_length_eq_zero this.symm)
theorem titer_nonempty {xs : List Bool} (h : xs ≠ []) (t : Nat) : titer xs t ≠ [] := by
  intro e
  have := titer_length xs t
  rw [e] at this
  exact h (List.eq_nil_of_length_eq_zero this.symm)

theorem change_true (xs : List Bool) : singleChange true true xs=singleChange true false xs := by
  cases xs <;> rfl
theorem section100 (xs : List Bool) : A (word0 xs)=word1 xs := rfl
theorem section111 (xs : List Bool) : A ([true,true,true]++xs)=word0 (C xs) := by
  change true::false::false::singleChange true true xs = true::false::false::singleChange true false xs
  rw [change_true]
theorem sections (xs : List Bool) : A (word1 xs)=word0 (T xs) := section111 (A xs)
theorem iter_even_odd (xs : List Bool) (t : Nat) :
    iter (word0 xs) (2*t)=word0 (titer xs t) ∧
    iter (word0 xs) (2*t+1)=word1 (titer xs t) := by
  induction t with
  | zero => exact ⟨rfl,section100 xs⟩
  | succ t ih =>
      have he : iter (word0 xs) (2*(t+1))=word0 (titer xs (t+1)) := by
        rw [show 2*(t+1)=(2*t+1)+1 by omega,iter,ih.2]
        exact sections (titer xs t)
      refine ⟨he,?_⟩
      rw [iter,he]
      exact section100 (titer xs (t+1))

theorem last_default (xs : List Bool) (h : xs ≠ []) (a b : Bool) : lastBit a xs=lastBit b xs := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons x xs => rfl
theorem r_word0 (xs : List Bool) : r (word0 xs)=r xs := rfl
theorem r_word1 {xs : List Bool} (h : xs ≠ []) : r (word1 xs)=s xs :=
  last_default (A xs) (A_nonempty h) true false
theorem trace_even (xs : List Bool) (t : Nat) : trace (word0 xs) (2*t)=r (titer xs t) := by
  unfold trace
  rw [(iter_even_odd xs t).1,r_word0]
theorem trace_odd {xs : List Bool} (h : xs ≠ []) (t : Nat) : trace (word0 xs) (2*t+1)=s (titer xs t) := by
  unfold trace
  rw [(iter_even_odd xs t).2,r_word1 (titer_nonempty h t)]

def takeBits (x : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n+1 => x 0 :: takeBits (fun j => x (j+1)) n
def rowStep (p q : Bool) (x : Nat → Bool) : Nat → Bool
  | 0 => xor (x 0) (p || q)
  | 1 => xor (x 1) (x 0 || p)
  | j+2 => xor (x (j+2)) (x (j+1) || x j)
theorem row_shift (p q : Bool) (x : Nat → Bool) :
    rowStep (x 0) p (fun j => x (j+1))=(fun j => rowStep p q x (j+1)) := by
  funext j
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl
theorem take_change (p q : Bool) (x : Nat → Bool) (n : Nat) :
    singleChange p q (takeBits x n)=takeBits (rowStep p q x) n := by
  induction n generalizing p q x with
  | zero => rfl
  | succ n ih => simp only [takeBits,singleChange]; rw [ih,row_shift]; rfl
theorem row_white (x : Nat → Bool) : rowStep false false x=march x := by
  funext j
  cases j with
  | zero => simp only [rowStep,march]; cases x 0 <;> rfl
  | succ j => cases j with
    | zero => simp only [rowStep,march]; cases x 0 <;> cases x 1 <;> rfl
    | succ j => rfl
theorem take_white (x : Nat → Bool) (n : Nat) : A (takeBits x n)=takeBits (march x) n := by
  rw [A,singleStep,take_change,row_white]
theorem take_initial (xs : List Bool) : takeBits (fun j => xs.getD j false) xs.length=xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
      change v :: takeBits (fun j => vs.getD j false) vs.length=v::vs
      rw [ih]

def full (xs : List Bool) : Nat → Nat → Bool
  | 0 => fun j => xs.getD j false
  | t+1 => march (full xs t)
theorem full_actual (xs : List Bool) : Actual (full xs) := fun _ _ => rfl
theorem prefix_full (xs : List Bool) (t : Nat) : takeBits (full xs t) xs.length=iter xs t := by
  induction t with
  | zero => exact take_initial xs
  | succ t ih =>
      change takeBits (march (full xs t)) xs.length=A (iter xs t)
      rw [← take_white,ih]

/-- Any constant column beyond depth zero would force its predecessor
white forever, contradicting the black anchor by induction on depth. -/
theorem no_constant_after_black (a : Nat → Nat → Bool) (ha : Actual a)
    (h0 : ∀ t, a t 0=true) (j : Nat) (hj : 0<j) (b : Bool) :
    ¬ ∀ t, a t j=b := by
  induction j generalizing b with
  | zero => omega
  | succ j ih =>
      intro hc
      cases j with
      | zero =>
          have hs := ha 0 1
          change a 1 1=xor (a 0 1) (a 0 0) at hs
          rw [hc 1,hc 0,h0 0] at hs
          cases b <;> contradiction
      | succ j =>
          apply ih (by omega) false
          intro t
          have hs := ha t (j+2)
          change a (t+1) (j+2)=xor (a t (j+2)) (a t (j+1) || a t j) at hs
          rw [hc (t+1),hc t] at hs
          cases hp : a t (j+1) with
          | false => rfl
          | true =>
              rw [hp] at hs
              cases b <;> cases a t j <;> contradiction

theorem last_take (x : Nat → Bool) (n : Nat) (d : Bool) :
    lastBit d (takeBits x (n+1))=x n := by
  induction n generalizing x d with
  | zero => rfl
  | succ n ih =>
      change lastBit (x 0) (takeBits (fun j => x (j+1)) (n+1))=x (n+1)
      exact ih (fun j => x (j+1)) (x 0)

theorem trace_full (xs : List Bool) (hn : 0<xs.length) (t : Nat) :
    trace xs t=full xs t (xs.length-1) := by
  unfold trace r
  rw [← prefix_full]
  cases hlen : xs.length with
  | zero => omega
  | succ n => exact last_take (full xs t) n false

theorem word0_first_black (xs : List Bool) (t : Nat) : full (word0 xs) t 0=true := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

/-- The two CA observation channels of a nonempty finite tail cannot both
be black at every time. No observer injectivity premise is used. -/
theorem not_always_black (xs : List Bool) (hx : xs≠[]) :
    ¬ ∀ t, r (titer xs t)=true ∧ s (titer xs t)=true := by
  intro hc
  have ht : ∀ t, trace (word0 xs) t=true := by
    intro t
    have hr := Nat.mod_lt t (by decide : 0<2)
    by_cases hm : t%2=0
    · have he : t=2*(t/2) := by omega
      rw [he,trace_even]
      exact (hc _).1
    · have he : t=2*(t/2)+1 := by omega
      rw [he,trace_odd hx]
      exact (hc _).2
  have hn : 0<(word0 xs).length := by simp [word0]
  apply no_constant_after_black (full (word0 xs)) (full_actual _) (word0_first_black xs)
    ((word0 xs).length-1) (by simp [word0]) true
  intro t
  rw [← trace_full _ hn]
  exact ht t

def outR (xs : List Bool) (t : Nat) := r (titer xs t)
def outS (xs : List Bool) (t : Nat) := s (titer xs t)
def delta (P : Nat) (a : Nat → Bool) (t : Nat) := xor (a (t+P)) (a t)
def demodR (P : Nat) (xs : List Bool) :=
  delta P (fun t => xor (outR xs t) (outS xs t))
def demodS (P : Nat) (xs : List Bool) :=
  delta P (fun t => xor (outS xs t) (outR xs (t+1)))
def birth (P : Nat) (u : List Bool) (g : Bool) :=
  xor (r (titer (u++[g]) P)) g

def memory (p q : Bool) : List Bool → Bool × Bool
  | [] => (p,q)
  | b::bs => memory b p bs
def force (p q : Bool) (xs : List Bool) :=
  (memory p q xs).1 || (memory p q xs).2
def halfBit (xs : List Bool) (g : Bool) := xor g (force false false xs)
def drive (xs : List Bool) := xor (force false false xs) (force true false (A xs))
def giter (u : List Bool) (g : Bool) : Nat → Bool
  | 0 => g
  | t+1 => xor (giter u g t) (drive (titer u t))

theorem xor_three (a b c : Bool) : xor (xor a b) c=xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem xor_twice (a b : Bool) : xor a (xor a b)=b := by
  cases a <;> cases b <;> rfl
theorem xor_same_right (a b c : Bool) : xor (xor a c) (xor b c)=xor a b := by
  cases a <;> cases b <;> cases c <;> rfl
theorem or_difference (a b c : Bool) :
    xor (a || c) (b || c)=(xor a b && !c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem memory_first (p q : Bool) (xs : List Bool) :
    (memory p q xs).1=lastBit p xs := by
  induction xs generalizing p q with
  | nil => rfl
  | cons b bs ih => exact ih b p

theorem change_append (p q : Bool) (xs ys : List Bool) :
    singleChange p q (xs++ys)=singleChange p q xs ++
      singleChange (memory p q xs).1 (memory p q xs).2 ys := by
  induction xs generalizing p q with
  | nil => rfl
  | cons b bs ih =>
      change xor b (p || q)::singleChange b p (bs++ys) =
        xor b (p || q)::(singleChange b p bs ++
          singleChange (memory b p bs).1 (memory b p bs).2 ys)
      rw [ih]

theorem change_append_one (p q : Bool) (xs : List Bool) (g : Bool) :
    singleChange p q (xs++[g])=singleChange p q xs ++ [xor g (force p q xs)] := by
  rw [change_append]
  rfl

theorem change_append_two (p q : Bool) (xs : List Bool) (g h : Bool) :
    singleChange p q (xs++[g,h])=singleChange p q xs ++
      [xor g (force p q xs),xor h (g || lastBit p xs)] := by
  rw [change_append]
  simp only [singleChange,force,memory_first]

theorem last_append_one (p : Bool) (xs : List Bool) (b : Bool) :
    lastBit p (xs++[b])=b := by
  induction xs generalizing p with
  | nil => rfl
  | cons a xs ih => exact ih a
theorem last_append_two (p : Bool) (xs : List Bool) (a b : Bool) :
    lastBit p (xs++[a,b])=b := by
  induction xs generalizing p with
  | nil => rfl
  | cons c xs ih => exact ih c

theorem A_append_two (u : List Bool) (g h : Bool) :
    A (u++[g,h])=A u++[halfBit u g,xor h (g || r u)] := by
  exact change_append_two false false u g h

theorem T_append_one (u : List Bool) (g : Bool) :
    T (u++[g])=T u++[xor g (drive u)] := by
  change singleChange true false (singleChange false false (u++[g]))=_
  rw [change_append_one,change_append_one]
  simp only [drive,A,singleStep,T,C,xor_three]

theorem T_append_two (u : List Bool) (g h : Bool) (hu : u≠[]) :
    T (u++[g,h])=T u++[xor g (drive u),
      xor (xor h (g || r u)) (halfBit u g || s u)] := by
  change C (A (u++[g,h]))=_
  rw [A_append_two]
  unfold C
  rw [change_append_two]
  have hl : lastBit true (A u)=s u :=
    last_default (A u) (A_nonempty hu) true false
  rw [hl]
  simp only [halfBit,drive,T,C,xor_three]

theorem titer_add (u : List Bool) (a b : Nat) :
    titer u (a+b)=titer (titer u a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg T ih

theorem titer_period (u : List Bool) (P : Nat) (hp : titer u P=u) (t : Nat) :
    titer u (t+P)=titer u t := by
  rw [Nat.add_comm,titer_add,hp]

theorem outR_period (u : List Bool) (P : Nat) (hp : titer u P=u) (t : Nat) :
    outR u (t+P)=outR u t := congrArg r (titer_period u P hp t)
theorem outS_period (u : List Bool) (P : Nat) (hp : titer u P=u) (t : Nat) :
    outS u (t+P)=outS u t := congrArg s (titer_period u P hp t)

theorem titer_append_one (u : List Bool) (g : Bool) (t : Nat) :
    titer (u++[g]) t=titer u t++[giter u g t] := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [titer,ih,T_append_one]
      rfl

theorem titer_append_two (u : List Bool) (g h : Bool) (hu : u≠[]) (t : Nat) :
    ∃ b, titer (u++[g,h]) t=titer u t++[giter u g t,b] := by
  induction t with
  | zero => exact ⟨h,rfl⟩
  | succ t ih =>
      obtain ⟨b,hb⟩ := ih
      rw [titer,hb,T_append_two _ _ _ (titer_nonempty hu t)]
      exact ⟨_,rfl⟩

theorem birth_eq (P : Nat) (u : List Bool) (g : Bool) :
    birth P u g=xor (giter u g P) g := by
  rw [birth,titer_append_one]
  unfold r
  rw [last_append_one]

theorem g_displacement (u : List Bool) (g : Bool) (P : Nat)
    (hp : titer u P=u) (t : Nat) :
    xor (giter u g (t+P)) (giter u g t)=birth P u g := by
  induction t with
  | zero => simpa only [Nat.zero_add,giter] using (birth_eq P u g).symm
  | succ t ih =>
      rw [show t+1+P=(t+P)+1 by omega]
      simp only [giter,titer_period u P hp t,xor_same_right]
      exact ih

theorem half_displacement (u : List Bool) (g : Bool) (P : Nat)
    (hp : titer u P=u) (t : Nat) :
    xor (halfBit (titer u (t+P)) (giter u g (t+P)))
      (halfBit (titer u t) (giter u g t))=birth P u g := by
  rw [titer_period u P hp t]
  simp only [halfBit,xor_same_right]
  exact g_displacement u g P hp t

theorem observation_ors (u : List Bool) (g h : Bool) (hu : u≠[]) (t : Nat) :
    xor (outR (u++[g,h]) t) (outS (u++[g,h]) t)=
      (giter u g t || outR u t) ∧
    xor (outS (u++[g,h]) t) (outR (u++[g,h]) (t+1))=
      (halfBit (titer u t) (giter u g t) || outS u t) := by
  obtain ⟨b,hb⟩ := titer_append_two u g h hu t
  have hr : outR (u++[g,h]) t=b := by
    unfold outR
    rw [hb]
    exact last_append_two false _ _ _
  have hs : outS (u++[g,h]) t=xor b (giter u g t || outR u t) := by
    unfold outS s
    rw [hb,A_append_two]
    exact last_append_two false _ _ _
  have hn : outR (u++[g,h]) (t+1)=xor (xor b (giter u g t || outR u t))
      (halfBit (titer u t) (giter u g t) || outS u t) := by
    unfold outR
    rw [titer,hb,T_append_two _ _ _ (titer_nonempty hu t)]
    exact last_append_two false _ _ _
  constructor
  · rw [hr,hs,xor_twice]
  · rw [hs,hn,xor_twice]

/-- Whole older return makes the appended penultimate displacement constant.
The observed differences are exactly the masked complements of the older outputs. -/
theorem masked_demodulation (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hp : titer u P=u) :
    ∀ t,
      demodR P (u++[g,h]) t=(birth P u g && !(outR u t)) ∧
      demodS P (u++[g,h]) t=(birth P u g && !(outS u t)) := by
  intro t
  constructor
  · dsimp only [demodR,delta]
    rw [(observation_ors u g h hu (t+P)).1,(observation_ors u g h hu t).1]
    rw [outR_period u P hp t,or_difference,g_displacement u g P hp t]
  · dsimp only [demodS,delta]
    rw [(observation_ors u g h hu (t+P)).2,(observation_ors u g h hu t).2]
    rw [outS_period u P hp t,or_difference,half_displacement u g P hp t]

/-- Pure periodicity makes the actual no-all-black witness occur within P. -/
theorem older_white_witness (u : List Bool) (P : Nat)
    (hu : u≠[]) (hP : 0<P) (hp : titer u P=u) :
    ∃ t, t<P ∧ (outR u t=false ∨ outS u t=false) := by
  apply Classical.byContradiction
  intro hn
  have hw : ∀ t, t<P → outR u t=true ∧ outS u t=true := by
    intro t ht
    constructor
    · cases hh : outR u t with
      | false => exact False.elim (hn ⟨t,ht,Or.inl hh⟩)
      | true => rfl
    · cases hh : outS u t with
      | false => exact False.elim (hn ⟨t,ht,Or.inr hh⟩)
      | true => rfl
  have hall : ∀ t, outR u t=true ∧ outS u t=true := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
        by_cases ht : t<P
        · exact hw t ht
        · have hi := ih (t-P) (by omega)
          have he : t=(t-P)+P := by omega
          rw [he,outR_period u P hp (t-P),outS_period u P hp (t-P)]
          exact hi
  exact not_always_black u hu hall

/-- A finite OR of the actual two observations detects the P-displacement.
P is a supplied return, not necessarily the least one. -/
theorem birth_detector (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hP : 0<P) (hp : titer u P=u) :
    birth P u g=(List.range P).any (fun t =>
      demodR P (u++[g,h]) t || demodS P (u++[g,h]) t) := by
  cases hb : birth P u g with
  | false =>
      symm
      apply List.any_eq_false.mpr
      intro t ht
      rw [(masked_demodulation u g h P hu hp t).1,
        (masked_demodulation u g h P hu hp t).2,hb]
      intro hc
      cases hc
  | true =>
      symm
      apply List.any_eq_true.mpr
      obtain ⟨t,ht,hw⟩ := older_white_witness u P hu hP hp
      refine ⟨t,List.mem_range.mpr ht,?_⟩
      rw [(masked_demodulation u g h P hu hp t).1,
        (masked_demodulation u g h P hu hp t).2,hb]
      rcases hw with hw | hw
      · rw [hw]
        rfl
      · rw [hw]
        cases outR u t <;> rfl

theorem demodulation_of_birth (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hp : titer u P=u) (hb : birth P u g=true) (t : Nat) :
    outR u t= !(demodR P (u++[g,h]) t) ∧
    outS u t= !(demodS P (u++[g,h]) t) := by
  have hh := masked_demodulation u g h P hu hp t
  rw [hb] at hh
  constructor
  · rw [hh.1]
    cases outR u t <;> rfl
  · rw [hh.2]
    cases outS u t <;> rfl

/-- Equal observations force equal flags; on a penultimate anti-period they
force equality of the older observations, even at different older widths. -/
theorem observe_birth_transfer (u v : List Bool) (g h g' h' : Bool) (P : Nat)
    (hu : u≠[]) (hv : v≠[]) (hP : 0<P)
    (hpu : titer u P=u) (hpv : titer v P=v)
    (heq : ∀ t, outR (u++[g,h]) t=outR (v++[g',h']) t ∧
      outS (u++[g,h]) t=outS (v++[g',h']) t) :
    birth P u g=birth P v g' ∧
      (birth P u g=true → ∀ t, outR u t=outR v t ∧ outS u t=outS v t) := by
  have hr : demodR P (u++[g,h])=demodR P (v++[g',h']) := by
    funext t
    simp only [demodR,delta,(heq (t+P)).1,(heq (t+P)).2,(heq t).1,(heq t).2]
  have hs : demodS P (u++[g,h])=demodS P (v++[g',h']) := by
    funext t
    simp only [demodS,delta,(heq (t+P)).2,(heq (t+P+1)).1,(heq t).2,(heq (t+1)).1]
  have hb : birth P u g=birth P v g' := by
    rw [birth_detector u g h P hu hP hpu,birth_detector v g' h' P hv hP hpv,hr,hs]
  refine ⟨hb,?_⟩
  intro hbu t
  have hbv : birth P v g'=true := hb.symm.trans hbu
  have h1 := demodulation_of_birth u g h P hu hpu hbu t
  have h2 := demodulation_of_birth v g' h' P hv hpv hbv t
  rw [hr,hs] at h1
  exact ⟨h1.1.trans h2.1.symm,h1.2.trans h2.2.symm⟩

/-- The official right-diagonal array has exactly the scan's white-boundary
recurrence. Only the right edge is constrained. -/
theorem Rd_actual {x : Int → Bool} {hi : Int}
    (hright : ∀ p, hi < p → x p = false) :
    Actual (fun t j => Rule30FiniteDiagonals.Rd x hi j t) := by
  intro t j
  cases j with
  | zero => exact Rule30FiniteDiagonals.Rd_zero_succ hright t
  | succ j =>
      cases j with
      | zero => exact Rule30FiniteDiagonals.Rd_one_succ hright t
      | succ j => exact Rule30FiniteDiagonals.Rd_step j t

/-- Scanning any finite initial right-diagonal prefix gives its exact official
evolution. Cells beyond the prefix need not be white. -/
theorem take_Rd {x : Int → Bool} {hi : Int}
    (hright : ∀ p, hi < p → x p = false) (n t : Nat) :
    takeBits (fun j => Rule30FiniteDiagonals.Rd x hi j t) n =
      iter (takeBits (fun j => x (hi-j)) n) t := by
  induction t with
  | zero => simp only [Rule30FiniteDiagonals.Rd, Rule30Realization.evol,
      Int.ofNat_zero, Int.add_zero, iter]
  | succ t ih =>
      have he : (fun j => Rule30FiniteDiagonals.Rd x hi j (t+1)) =
          march (fun j => Rule30FiniteDiagonals.Rd x hi j t) :=
        funext (Rd_actual hright t)
      rw [he, ← take_white, ih]
      rfl

/-- For an initial `100` followed by a nonempty tail, the two observation
channels are the literal even/odd samples of the same official right diagonal.
The initial configuration farther left is arbitrary. -/
theorem Rd_observations {x : Int → Bool} {hi : Int} (xs : List Bool)
    (hright : ∀ p, hi < p → x p = false)
    (hinit : takeBits (fun j => x (hi-j)) (xs.length+3) = word0 xs)
    (hne : xs ≠ []) (t : Nat) :
    Rule30FiniteDiagonals.Rd x hi (xs.length+2) (2*t) = outR xs t ∧
      Rule30FiniteDiagonals.Rd x hi (xs.length+2) (2*t+1) = outS xs t := by
  have ht (s : Nat) : trace (word0 xs) s =
      Rule30FiniteDiagonals.Rd x hi (xs.length+2) s := by
    have he := take_Rd hright (xs.length+3) s
    rw [hinit] at he
    unfold trace r
    rw [← he]
    exact last_take (fun j => Rule30FiniteDiagonals.Rd x hi j s) (xs.length+2) false
  constructor
  · exact (ht (2*t)).symm.trans (trace_even xs t)
  · exact (ht (2*t+1)).symm.trans (trace_odd hne t)

/-! ### Opposite-phase descent with the one-update lag retained -/

/-- The two difference profiles exchange under a half-step observation shift;
the second exchanged profile is advanced by one whole tail update. -/
theorem phase_demodulation (v w : List Bool) (P : Nat)
    (heq : ∀ t, outR v t=outS w t ∧ outS v t=outR w (t+1)) :
    ∀ t, demodR P v t=demodS P w t ∧
      demodS P v t=demodR P w (t+1) := by
  intro t
  constructor
  · simp only [demodR,demodS,delta,(heq (t+P)).1,(heq (t+P)).2,
      (heq t).1,(heq t).2]
  · simp only [demodR,demodS,delta,(heq (t+P)).2,(heq (t+1+P)).1,
      (heq t).2,(heq (t+1)).1,show t+P+1=t+1+P by omega]

/-- The cyclically shifted pair of demodulators detects exactly the same
birth. The first-channel wrap uses the supplied whole older P-return. -/
theorem birth_detector_opposite (u : List Bool) (g h : Bool) (P : Nat)
    (hu : u≠[]) (hP : 0<P) (hp : titer u P=u) :
    birth P u g=(List.range P).any (fun t =>
      demodS P (u++[g,h]) t || demodR P (u++[g,h]) (t+1)) := by
  cases hb : birth P u g with
  | false =>
      symm
      apply List.any_eq_false.mpr
      intro t ht
      rw [(masked_demodulation u g h P hu hp t).2,
        (masked_demodulation u g h P hu hp (t+1)).1,hb]
      intro hc
      cases hc
  | true =>
      symm
      apply List.any_eq_true.mpr
      obtain ⟨t,ht,hw⟩ := older_white_witness u P hu hP hp
      rcases hw with hr | hs
      · cases t with
        | zero =>
            refine ⟨P-1,List.mem_range.mpr (by omega),?_⟩
            rw [(masked_demodulation u g h P hu hp (P-1)).2,
              (masked_demodulation u g h P hu hp (P-1+1)).1,hb,
              show P-1+1=P by omega]
            have hrP : outR u P=false := by
              have hh := outR_period u P hp 0
              simpa only [Nat.zero_add,hr] using hh
            rw [hrP]
            cases outS u (P-1) <;> rfl
        | succ t =>
            refine ⟨t,List.mem_range.mpr (by omega),?_⟩
            rw [(masked_demodulation u g h P hu hp t).2,
              (masked_demodulation u g h P hu hp (t+1)).1,hb,hr]
            cases outS u t <;> rfl
      · refine ⟨t,List.mem_range.mpr ht,?_⟩
        rw [(masked_demodulation u g h P hu hp t).2,
          (masked_demodulation u g h P hu hp (t+1)).1,hb,hs]
        rfl

/-- Opposite phase forces equal flags. At a nonzero birth it descends to
the older observations, with the essential lag on the second equality. -/
theorem observe_birth_phase_transfer (u z : List Bool) (g h g' h' : Bool) (P : Nat)
    (hu : u≠[]) (hz : z≠[]) (hP : 0<P)
    (hpu : titer u P=u) (hpz : titer z P=z)
    (heq : ∀ t, outR (u++[g,h]) t=outS (z++[g',h']) t ∧
      outS (u++[g,h]) t=outR (z++[g',h']) (t+1)) :
    birth P u g=birth P z g' ∧
      (birth P u g=true → ∀ t,
        outR u t=outS z t ∧ outS u t=outR z (t+1)) := by
  have hd := phase_demodulation (u++[g,h]) (z++[g',h']) P heq
  have hf : demodR P (u++[g,h])=demodS P (z++[g',h']) :=
    funext (fun t => (hd t).1)
  have hg : demodS P (u++[g,h])=(fun t => demodR P (z++[g',h']) (t+1)) :=
    funext (fun t => (hd t).2)
  have hb : birth P u g=birth P z g' := by
    rw [birth_detector u g h P hu hP hpu,
      birth_detector_opposite z g' h' P hz hP hpz,hf,hg]
  refine ⟨hb,?_⟩
  intro hbu t
  have hbz : birth P z g'=true := hb.symm.trans hbu
  have hu0 := demodulation_of_birth u g h P hu hpu hbu t
  have hz0 := demodulation_of_birth z g' h' P hz hpz hbz t
  have hz1 := demodulation_of_birth z g' h' P hz hpz hbz (t+1)
  rw [(hd t).1,(hd t).2] at hu0
  exact ⟨hu0.1.trans hz0.2.symm,hu0.2.trans hz1.1.symm⟩

/-- Two singleton tails cannot have opposite-phase observations: at t=0
their equal half-step values would also have to equal the negated next value. -/
theorem singleton_not_opposite (a b : Bool) :
    ¬ (∀ t, outR [a] t=outS [b] t ∧ outS [a] t=outR [b] (t+1)) := by
  intro h
  have h0 := h 0
  cases a <;> cases b <;> rcases h0 with ⟨h1,h2⟩ <;> cases h1 <;> cases h2

/-- A positive birth cannot support opposite-phase equality when both
older prefixes are singleton tails. This is only a conditional base case. -/
theorem singleton_birth_not_opposite (a b g h g' h' : Bool) (P : Nat)
    (hP : 0<P) (hpa : titer [a] P=[a]) (hpb : titer [b] P=[b])
    (hb : birth P [a] g=true) :
    ¬ (∀ t, outR ([a]++[g,h]) t=outS ([b]++[g',h']) t ∧
      outS ([a]++[g,h]) t=outR ([b]++[g',h']) (t+1)) := by
  intro heq
  have hd := observe_birth_phase_transfer [a] [b] g h g' h' P
    (by simp) (by simp) hP hpa hpb heq
  exact singleton_not_opposite a b (hd.2 hb)


end Ruliology.CellularAutomata.Rule30ClockBirthDemodulation
