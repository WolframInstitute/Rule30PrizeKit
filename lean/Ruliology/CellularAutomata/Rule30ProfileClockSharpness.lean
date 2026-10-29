module
public import Ruliology.CellularAutomata.Rule30ProfileClockEscape

/-! Reverse realization of finite periodic profile diagrams, and an actual
finite-seed witness showing that the period32 escape bound14 is sharp. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ProfileClockSharpness
open Rule30RightProfiles Rule30RightPrefixClock Rule30RightPrefixBound Rule30ProfileGraph
set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

def wordSeed (W : Nat) (p : Int) : Bool :=
  if 0<p then false else W.testBit (-p).toNat
def A (W j t : Nat) : Bool := rightDiag (wordSeed W) (-2+(j:Int)) t

theorem seed_right (W : Nat) : ∀p,0<p → wordSeed W p=false := by
  intro p hp
  exact ite_eq_left hp

theorem seed_initial (W j : Nat) : rightDiag (wordSeed W) (j:Int) 0=W.testBit j := by
  simp [rightDiag,Rule30Realization.evol,wordSeed]

theorem seed_left (W width : Nat) (hW : W<2^width) (p : Int)
    (hp : p< -(width:Int)+1) : wordSeed W p=false := by
  by_cases pos : 0<p
  · exact seed_right W p pos
  · unfold wordSeed
    rw [ite_eq_right pos]
    apply Nat.testBit_lt_two_pow
    have hj : width≤(-p).toNat := by omega
    exact Nat.lt_of_lt_of_le hW (Nat.pow_le_pow_right (by omega) hj)

theorem A_zero0 (W t : Nat) : A W 0 t=false :=
  right_white (wordSeed W) 0 (seed_right W) t _ (by omega)
theorem A_zero1 (W t : Nat) : A W 1 t=false :=
  right_white (wordSeed W) 0 (seed_right W) t _ (by omega)

theorem A_initial (W j : Nat) :
    A W j 0=if j<2 then false else W.testBit (j-2) := by
  by_cases small : j<2
  · rw [ite_eq_left small]
    exact right_white (wordSeed W) 0 (seed_right W) 0 _ (by omega)
  · rw [ite_eq_right small]
    obtain ⟨k,rfl⟩ : ∃k,j=k+2 := ⟨j-2,by omega⟩
    have index : -2+((k+2:Nat):Int)=(k:Int) := by omega
    simpa only [A,index,show k+2-2=k by omega] using seed_initial W k

theorem A_step (W j t : Nat) :
    A W (j+2) (t+1)=xor (A W (j+2) t) (A W (j+1) t || A W j t) := by
  have h := rightDiag_step (wordSeed W) (-2+((j+2:Nat):Int)) t
  simpa only [A,show -2+((j+2:Nat):Int)-1= -2+((j+1:Nat):Int) by omega,
    show -2+((j+2:Nat):Int)-2= -2+(j:Int) by omega] using h

/-- A finite lower-triangular profile diagram is fixed by its first two
profiles, initial values, and literal recurrence. -/
theorem finite_profiles_unique (N : Nat) (B P : Nat → Nat → Bool)
    (zero0 : ∀t,B 0 t=P 0 t) (zero1 : ∀t,B 1 t=P 1 t)
    (initial : ∀j,j≤N → B j 0=P j 0)
    (stepB : ∀j,j+2≤N → ∀t,B (j+2) (t+1)=xor (B (j+2) t) (B (j+1) t || B j t))
    (stepP : ∀j,j+2≤N → ∀t,P (j+2) (t+1)=xor (P (j+2) t) (P (j+1) t || P j t)) :
    ∀j,j≤N → ∀t,B j t=P j t := by
  have pairs : ∀n,n+1≤N → (∀t,B n t=P n t) ∧ ∀t,B (n+1) t=P (n+1) t := by
    intro n
    induction n with
    | zero => intro _;exact ⟨zero0,zero1⟩
    | succ n ih =>
      intro hn
      have old := ih (by omega)
      refine ⟨old.2,?_⟩
      intro t
      induction t with
      | zero => exact initial (n+2) (by omega)
      | succ t iht =>
        rw [stepB n (by omega) t,stepP n (by omega) t,old.1 t,old.2 t,iht]
  intro j hj
  by_cases hz : j=0
  · subst j;exact zero0
  · have h := (pairs (j-1) (by omega)).2
    simpa only [show j-1+1=j by omega] using h

/-- Checked periodic words represent actual ordinary Rule30 diagonals of the
specified finite seed. This is the reverse direction of the graph encoding. -/
theorem realize_words (q W N : Nat) (words : Nat → Nat) (hq : 0<q)
    (zero0 : words 0=0) (zero1 : words 1=0)
    (initial : ∀j,j≤N → profile q (words j) 0=if j<2 then false else W.testBit (j-2))
    (steps : ∀j,j+2≤N → WordStep q (words (j+1)) (words j) (words (j+2))) :
    ∀j,j≤N → ∀t,A W j t=profile q (words j) t := by
  apply finite_profiles_unique N (A W) (fun j => profile q (words j))
  · intro t;rw [A_zero0,zero0];simp [profile]
  · intro t;rw [A_zero1,zero1];simp [profile]
  · intro j hj;rw [A_initial];exact (initial j hj).symm
  · intro j _ t;exact A_step W j t
  · intro j hj;exact wordStep_sound q (words (j+1)) (words j) (words (j+2)) hq (steps j hj)

theorem realized_prefix_period (q W N n p : Nat) (words : Nat → Nat) (hq : 0<q)
    (hn : n+2≤N)
    (realization : ∀j,j≤N → ∀t,A W j t=profile q (words j) t)
    (per : ∀j,j≤n+2 → WordPer q (words j) p) :
    PrefixPer (rightDiag (wordSeed W)) (n:Int) p := by
  intro i hi t
  by_cases neg : i<0
  · rw [right_white (wordSeed W) 0 (seed_right W) _ i (by omega),
      right_white (wordSeed W) 0 (seed_right W) _ i (by omega)]
  · have cast : (i.toNat:Int)=i := Int.toNat_of_nonneg (by omega)
    have bound : i.toNat+2≤n+2 := by omega
    have index : -2+((i.toNat+2:Nat):Int)=i := by omega
    have hp := (wordPer_iff q (words (i.toNat+2)) p hq).1 (per _ bound) t
    rw [← realization (i.toNat+2) (by omega),← realization (i.toNat+2) (by omega)] at hp
    simpa only [A,index] using hp

-- The concrete seventeen-diagonal witness and checked words follow below.

def packedWords : Nat := 0xd2a9999a32d55555ab2d5556aab2aea956ab517579eae98d8516994a4519954bc69555aca5955a6aa55aa55a57575757b4b4b4b4ccccccccaaaaaaaaaaaaaaaaffffffff0000000000000000
def words (j : Nat) : Nat := (packedWords >>> (32*j)) &&& 4294967295

theorem witness_initials : ∀j:Fin 19,
    profile 32 (words j.val) 0=if j.val<2 then false else (47649:Nat).testBit (j.val-2) := by decide +kernel
theorem witness_steps : ∀j:Fin 17,
    WordStep 32 (words (j.val+1)) (words j.val) (words (j.val+2)) := by decide +kernel

theorem witness_realization : ∀j,j≤18 → ∀t,A 47649 j t=profile 32 (words j) t :=
  realize_words 32 47649 18 words (by omega) (by decide +kernel) (by decide +kernel)
    (fun j hj => witness_initials ⟨j,by omega⟩)
    (fun j hj => witness_steps ⟨j,by omega⟩)

theorem witness_prefix32 : PrefixPer (rightDiag (wordSeed 47649)) 16 32 := by
  apply realized_prefix_period 32 47649 18 16 32 words (by omega) (by omega) witness_realization
  intro j _
  exact (wordPer_iff 32 (words j) 32 (by omega)).2 (profile_period 32 (words j))

theorem witness_prefix4 : PrefixPer (rightDiag (wordSeed 47649)) 3 4 := by
  have per : ∀j:Fin 6,WordPer 32 (words j.val) 4 := by decide +kernel
  apply realized_prefix_period 32 47649 18 3 4 words (by omega) (by omega) witness_realization
  intro j hj
  exact per ⟨j,by omega⟩

theorem witness_nonperiod_two : ¬Period (rightDiag (wordSeed 47649) 3) 2 := by
  have eqD : ∀t,rightDiag (wordSeed 47649) 3 t=profile 32 (words 5) t := by
    intro t
    simpa only [A,show -2+((5:Nat):Int)=(3:Int) by omega] using witness_realization 5 (by omega) t
  have different : profile 32 (words 5) 2≠profile 32 (words 5) 0 := by decide +kernel
  intro per
  exact different (by simpa only [Nat.zero_add,eqD] using per 0)

theorem witness_clock_two : PrefixIsE (rightDiag (wordSeed 47649)) 3 2 := by
  constructor
  · exact witness_prefix4
  · intro e he small
    have hp := prefix_pow_mono (b:=1) small (by omega)
    exact witness_nonperiod_two (hp 3 (by omega))

theorem witness_finite : ∀p:Int,p< -15 ∨ 0<p → wordSeed 47649 p=false := by
  intro p hp
  rcases hp with left | right
  · exact seed_left 47649 16 (by decide +kernel) p (by omega)
  · exact seed_right 47649 p right

/-- An actual finite seed realizes13 additional period32 diagonals after a
period4 prefix. Hence the uniform14-diagonal escape bound cannot be reduced. -/
theorem sharpness_witness :
    PrefixIsE (rightDiag (wordSeed 47649)) 3 2 ∧
    PrefixPer (rightDiag (wordSeed 47649)) 16 32 :=
  ⟨witness_clock_two,witness_prefix32⟩

theorem thirteen_is_not_uniform :
    ¬(∀x:Int → Bool,(∀p,0<p → x p=false) → ∀n:Nat,
      ¬Period (rightDiag x (n:Int)) 2 →
      ¬PrefixPer (rightDiag x) ((n+13:Nat):Int) 32) := by
  intro uniform
  exact uniform (wordSeed 47649) (seed_right 47649) 3 witness_nonperiod_two witness_prefix32

end Ruliology.CellularAutomata.Rule30ProfileClockSharpness
