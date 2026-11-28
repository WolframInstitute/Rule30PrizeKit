module

public import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# White observations every third tick

Three fixed neighboring sites white at every sample force the middle column
of the singleton to eventually repeat 001. If the center is white at the
sample, the west neighbor one tick later and the east neighbor two ticks
later, the middle column eventually repeats 011. For each geometry, a
nonempty group of three eastern cells stays nonempty at later samples.
Before it first becomes nonempty the center stays white, which cannot last
forever for the singleton.

The kit's phase skeletons give both converses at the center. In particular
a white observation at -1 followed one tick later by white at 0 once per
period suffices for 001: the OR in the update makes all three cells at the
earlier sample white. At most one aligned white triple location and phase
can persist anywhere in the singleton.

With an unrestricted western initial half, a single white sample per three
ticks still leaves two independent controls. The last theorems realize
arbitrary sample streams on two eastern neighbors, or on the two flanks,
with any prescribed initial right half. Recurrence of black on each residue
at the singleton’s column -1 is open.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ThirdTick

open Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata.Rule30EtherThree

private def cone (f : Nat → Bool) : Nat → Nat → Bool
  | 0, j => f j
  | n+1, j => rule (cone f n j) (cone f n (j+1)) (cone f n (j+2))

private theorem cone_cell (i : Int) (t n j : Nat) :
    cone (fun k : Nat => cell t (i+k)) n j = cell (t+n) (i+j+n) := by
  induction n generalizing j with
  | zero => simp [cone]
  | succ n ih =>
    simp only [cone,ih,cell]
    congr 1 <;> congr 1 <;> omega

def occupied (a b c : Bool) := a || b || c
def occ (i : Int) (t : Nat) := occupied (cell t i) (cell t (i+1)) (cell t (i+2))

private theorem shape_table (f : Nat → Bool)
    (a : f 3=false) (b : f 4=false) (c : f 5=false)
    (d : cone f 3 0=false) (e : cone f 3 1=false) (g : cone f 3 2=false) :
    cone f 2 2 = occupied (f 6) (f 7) (f 8) := by
  revert d e g
  simp only [cone,Nat.reduceAdd,a,b,c]
  generalize f 0=A, f 1=B, f 2=C, f 6=D, f 7=E, f 8=F
  revert A B C D E F
  decide +kernel

private theorem latch_table (f : Nat → Bool)
    (a : f 0=false) (b : f 1=false) (c : f 2=false) :
    occupied (f 3) (f 4) (f 5)=true →
    occupied (cone f 3 0) (cone f 3 1) (cone f 3 2)=true := by
  simp only [cone,Nat.reduceAdd,a,b,c]
  generalize f 3=A, f 4=B, f 5=C, f 6=D, f 7=E, f 8=F
  revert A B C D E F
  decide +kernel

def White (i : Int) (t : Nat) :=
  cell t (i-1)=false ∧ cell t i=false ∧ cell t (i+1)=false

private theorem sample_step (i : Int) (t : Nat) (h : White i t) (h' : White i (t+3)) :
    cell (t+1) i=false ∧ cell (t+2) i=occ (i+2) t ∧
      (occ (i+2) t=true → occ (i+2) (t+3)=true) := by
  rcases h with ⟨a,b,c⟩
  rcases h' with ⟨d,e,g⟩
  refine ⟨?_,?_,?_⟩
  · simp [cell,a,b,c,rule]
  · have table := shape_table (fun j : Nat => cell t (i-4+j))
    simp only [cone_cell] at table
    simp +arith [occ] at table ⊢
    exact table (by simpa +arith using a) b c (by simpa +arith using d) e g
  · have table := latch_table (fun j : Nat => cell t (i-1+j))
    simp only [cone_cell] at table
    simp +arith [occ] at table ⊢
    exact table (by simpa +arith using a) b c

private theorem lock_of_returns (i : Int) (T : Nat) (high : Bool) (live : Nat → Bool)
    (zero : ∀ k, cell (T+3*k) i=false)
    (one : ∀ k, cell (T+3*k+1) i=(high && live k))
    (two : ∀ k, cell (T+3*k+2) i=live k)
    (holds : ∀ k, live k=true → live (k+1)=true) :
    ∃ K, ∀ k, K ≤ k →
      cell (T+3*k) i=false ∧ cell (T+3*k+1) i=high ∧ cell (T+3*k+2) i=true := by
  have some_black : ∃ k, live k=true := by
    apply Classical.byContradiction
    intro no
    have off (k : Nat) : live k=false := by
      cases hv : live k
      · rfl
      · exact (no ⟨k,hv⟩).elim
    apply no_column_eventually_constant i
    refine ⟨T,false,fun t ht => ?_⟩
    let k := (t-T)/3
    have alt : t=T+3*k ∨ t=T+3*k+1 ∨ t=T+3*k+2 := by dsimp [k]; omega
    rcases alt with eq | eq | eq <;> rw [eq]
    · exact zero k
    · simp [one,off]
    · rw [two,off]
  obtain ⟨K,hit⟩ := some_black
  have stays (k : Nat) (hk : K ≤ k) : live k=true := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hk
    clear hk
    induction n with
    | zero => exact hit
    | succ n ih => exact holds (K+n) ih
  exact ⟨K,fun k hk => ⟨zero k,by simp [one,stays k hk],(two k).trans (stays k hk)⟩⟩

/-- Three white sites at every sample force the middle trace to be 001. -/
theorem clock_of_three_white (i : Int) (T : Nat) (h : ∀ k, White i (T+3*k)) :
    ∃ K, ∀ k, K ≤ k →
      cell (T+3*k) i=false ∧ cell (T+3*k+1) i=false ∧ cell (T+3*k+2) i=true := by
  have step (k : Nat) := sample_step i (T+3*k) (h k)
    (by simpa [Nat.mul_succ,Nat.add_assoc] using h (k+1))
  apply lock_of_returns i T false (fun k => occ (i+2) (T+3*k)) (fun k => (h k).2.1)
      (fun k => (step k).1) (fun k => (step k).2.1)
  intro k
  simpa [Nat.mul_succ,Nat.add_assoc] using (step k).2.2

private theorem periodic_of_three (i : Int) (T : Nat) (h : ∀ k, White i (T+3*k)) :
    EventuallyPeriodic (fun t => cell t i) := by
  obtain ⟨K,lock⟩ := clock_of_three_white i T h
  refine ⟨T+3*K,3,by decide,fun t ht => ?_⟩
  let k := (t-T)/3
  have hk : K ≤ k := by dsimp [k]; omega
  have a := lock k hk
  have b := lock (k+1) (by omega)
  have alt : t=T+3*k ∨ t=T+3*k+1 ∨ t=T+3*k+2 := by dsimp [k]; omega
  rcases alt with eq | eq | eq <;> simp_all +arith

/-- For each sample phase, at least one of any four consecutive fixed columns
is black arbitrarily late at that phase. -/
theorem four_columns_hit (i : Int) (T : Nat) :
    ∃ k, ∃ j : Int, i ≤ j ∧ j ≤ i+3 ∧ cell (T+3*k) j=true := by
  apply Classical.byContradiction
  intro no
  have white (k : Nat) (j : Int) (lo : i ≤ j) (hi : j ≤ i+3) : cell (T+3*k) j=false := by
    cases hv : cell (T+3*k) j
    · rfl
    · exact (no ⟨k,j,lo,hi,hv⟩).elim
  apply jen (i+1) (i+2) (by omega)
  constructor <;> apply periodic_of_three _ T <;> intro k <;>
    exact ⟨white k _ (by omega) (by omega),white k _ (by omega) (by omega),
      white k _ (by omega) (by omega)⟩

/-- At most one location and one phase anywhere in the singleton can sustain
a sampled white triple. The start time itself need not be unique. -/
theorem unique_location_phase (i j : Int) (T S : Nat)
    (h : ∀ k, White i (T+3*k)) (g : ∀ k, White j (S+3*k)) :
    i=j ∧ T%3=S%3 := by
  have eq : i=j := by
    apply Classical.byContradiction
    intro ne
    exact jen i j ne ⟨periodic_of_three i T h, periodic_of_three j S g⟩
  subst j
  refine ⟨rfl,?_⟩
  obtain ⟨K,a⟩ := clock_of_three_white i T h
  obtain ⟨L,b⟩ := clock_of_three_white i S g
  let t := T+3*(K+L+S)+2
  have black : cell t i=true := (a (K+L+S) (by omega)).2.2
  let k := (t-S)/3
  have hk : L ≤ k := by dsimp [k,t]; omega
  have whites := b k hk
  by_cases phase : T%3=S%3
  · exact phase
  · have alt : t=S+3*k ∨ t=S+3*k+1 := by dsimp [k,t]; omega
    rcases alt with e | e <;> rw [e] at black <;> simp_all

/-- The exceptional triple at the center exists exactly for the 001 clock.
The reverse direction uses the kit's right-neighbor skeleton. -/
theorem center_white_iff_001 :
    (∃ T, ∀ k, White 0 (T+3*k)) ↔
    ∃ S, ∀ t, S ≤ t → cell t 0=wordAt3 w001 (t-S) := by
  constructor
  · rintro ⟨T,h⟩
    obtain ⟨K,lock⟩ := clock_of_three_white 0 T h
    refine ⟨T+3*K,fun t ht => ?_⟩
    let k := (t-T)/3
    have tr := lock k (by dsimp [k]; omega)
    have alt : t=T+3*k ∨ t=T+3*k+1 ∨ t=T+3*k+2 := by dsimp [k]; omega
    rw [wordAt3_001]
    rcases alt with e | e | e <;> simp_all +arith <;> omega
  · rintro ⟨S,clock⟩
    obtain ⟨V,hV,sk⟩ := skeleton_001 S clock
    refine ⟨S+3*V,fun k => ?_⟩
    let t := S+3*V+3*k
    have phase : (t-S)%3=0 := by dsimp [t]; omega
    have ht : V ≤ t := by dsimp [t]; omega
    have east := sk t ht phase
    have west := ((col_m1_001 S clock t (by omega)).1 phase).trans east
    have middle := clock t (by omega)
    rw [wordAt3,phase] at middle
    exact ⟨west,middle,east⟩

def Staggered (i : Int) (t : Nat) :=
  cell t i=false ∧ cell (t+1) (i-1)=false ∧ cell (t+2) (i+1)=false

private theorem stagger_table (f : Nat → Bool) (a : f 3=false)
    (b : cone f 1 1=false) (c : cone f 2 2=false) :
    cone f 1 2=occupied (f 4) (f 5) (f 6) ∧ cone f 2 1=cone f 1 2 := by
  revert b c
  simp only [cone,Nat.reduceAdd,a]
  generalize f 1=A, f 2=B, f 4=C, f 5=D, f 6=E
  revert A B C D E
  decide +kernel

private theorem stagger_step (i : Int) (t : Nat) (h : Staggered i t) :
    cell (t+1) i=occ (i+1) t ∧ cell (t+2) i=occ (i+1) t ∧
    (occ (i+1) t=true → occ (i+1) (t+3)=true) := by
  rcases h with ⟨a,b,c⟩
  have table := stagger_table (fun j : Nat => cell t (i-3+j))
  simp only [cone_cell] at table
  simp +arith at table
  obtain ⟨one,two⟩ := table a (by simpa +arith using b) (by simpa +arith using c)
  have m : cell (t+1) i=occ (i+1) t := by simpa +arith [occ] using one
  refine ⟨m,two.trans m,?_⟩
  intro live
  have center := (two.trans m).trans live
  have b1 : cell (t+3) (i+1) = !(cell (t+2) (i+2)) := by
    change rule (cell (t+2) (i+1-1)) (cell (t+2) (i+1)) (cell (t+2) (i+1+1)) = _
    simp +arith [rule,center,c]
  have b2 (on : cell (t+2) (i+2)=true) : cell (t+3) (i+2)=true := by
    change rule (cell (t+2) (i+2-1)) (cell (t+2) (i+2)) _ = _
    simp +arith [rule,c,on]
  cases z : cell (t+2) (i+2)
  · simp [occ,occupied,b1,z]
  · simp [occ,occupied,show i+1+1=i+2 by omega,b2 z]

theorem clock_of_staggered (i : Int) (T : Nat) (h : ∀ k, Staggered i (T+3*k)) :
    ∃ K, ∀ k, K ≤ k →
      cell (T+3*k) i=false ∧ cell (T+3*k+1) i=true ∧ cell (T+3*k+2) i=true := by
  have step (k : Nat) := stagger_step i (T+3*k) (h k)
  apply lock_of_returns i T true (fun k => occ (i+1) (T+3*k)) (fun k => (h k).1)
      (fun k => by simpa using (step k).1) (fun k => (step k).2.1)
  intro k
  simpa [Nat.mul_succ,Nat.add_assoc] using (step k).2.2

theorem center_staggered_iff_011 :
    (∃ T, ∀ k, Staggered 0 (T+3*k)) ↔
    ∃ S, ∀ t, S ≤ t → cell t 0=wordAt3 w011 (t-S) := by
  constructor
  · rintro ⟨T,h⟩
    obtain ⟨K,lock⟩ := clock_of_staggered 0 T h
    refine ⟨T+3*K,fun t ht => ?_⟩
    let k := (t-T)/3
    have tr := lock k (by dsimp [k]; omega)
    have alt : t=T+3*k ∨ t=T+3*k+1 ∨ t=T+3*k+2 := by dsimp [k]; omega
    rw [wordAt3_011]
    rcases alt with e | e | e <;> simp_all +arith <;> omega
  · rintro ⟨S,clock⟩
    obtain ⟨V,hV,sk⟩ := skeleton_011 S clock
    refine ⟨S+3*V,fun k => ?_⟩
    let t := S+3*V+3*k
    have phase : (t-S)%3=0 := by dsimp [t]; omega
    have ht : V ≤ t := by dsimp [t]; omega
    have east := (sk (t+2) (by omega)).2 (by omega)
    have west := (col_m1_011 S clock (t+1) (by omega)).2.1 (by omega)
    have middle := clock t (by omega)
    rw [wordAt3,phase] at middle
    exact ⟨middle,west,east⟩

theorem white_pair_iff_001 :
    (∃ T, ∀ k, cell (T+3*k) (-1)=false ∧ cell (T+3*k+1) 0=false) ↔
    ∃ S, ∀ t, S ≤ t → cell t 0=wordAt3 w001 (t-S) := by
  rw [← center_white_iff_001]
  constructor
  · rintro ⟨T,pair⟩
    refine ⟨T,fun k => ?_⟩
    obtain ⟨west,following⟩ := pair k
    change rule (cell (T+3*k) (-1)) (cell (T+3*k) 0) (cell (T+3*k) 1) = false at following
    simp [rule,west] at following
    exact ⟨west,following.1,following.2⟩
  · rintro ⟨T,triple⟩
    refine ⟨T,fun k => ?_⟩
    obtain ⟨a,b,c⟩ := triple k
    refine ⟨a,?_⟩
    change rule (cell (T+3*k) (-1)) (cell (T+3*k) 0) (cell (T+3*k) 1) = false
    rw [show (0:Int)-1 = -1 by decide] at a
    rw [show (0:Int)+1 = 1 by decide] at c
    rw [a,b,c]; rfl

/-- A two-tick consequence of left permutivity and the black OR latch.
The spatial word 001, ending at i, is equivalent to the temporal word 110 there. -/
theorem word001_iff_110 (i : Int) (t : Nat) :
    (cell t (i-2)=false ∧ cell t (i-1)=false ∧ cell t i=true) ↔
    (cell t i=true ∧ cell (t+1) i=true ∧ cell (t+2) i=false) := by
  generalize east : cell (t+1) (i+1)=v
  change _ ↔ (cell t i=true ∧ rule (cell t (i-1)) (cell t i) (cell t (i+1))=true ∧
    rule (cell (t+1) (i-1)) (rule (cell t (i-1)) (cell t i) (cell t (i+1))) _=false)
  rw [east]
  change _ ↔ (_ ∧ _ ∧ rule (rule (cell t (i-1-1)) (cell t (i-1)) (cell t (i-1+1))) _ v=false)
  rw [show i-1-1=i-2 by omega,show i-1+1=i by omega]
  cases cell t (i-2) <;> cases cell t (i-1) <;> cases cell t i <;> cases cell t (i+1) <;>
    cases v <;> decide

def Clock3 := ∃ T, ∀ t, T ≤ t → cell (t+3) 0=cell t 0

/-- Exact target with two local observations; each involves the same single
white phase at -1 after a suitable shift. -/
theorem clock_iff_markers :
    Clock3 ↔
    (∃ T, ∀ k, cell (T+3*k) (-1)=false ∧ cell (T+3*k+1) 0=false) ∨
    (∃ T, ∀ k, Staggered 0 (T+3*k)) := by
  rw [white_pair_iff_001,center_staggered_iff_011]
  constructor
  · rintro ⟨T,h⟩
    rcases normalize_period_three h with ⟨S,_,hs⟩ | ⟨S,_,hs⟩
    · exact Or.inl ⟨S,hs⟩
    · exact Or.inr ⟨S,hs⟩
  · have period (w : List Bool) (S : Nat)
        (hw : ∀ t, S ≤ t → cell t 0=wordAt3 w (t-S)) : Clock3 := by
      refine ⟨S,fun t ht => ?_⟩
      rw [hw _ (by omega),hw _ ht,wordAt3,wordAt3,show (t+3-S)%3=(t-S)%3 by omega]
    rintro (⟨S,h⟩ | ⟨S,h⟩) <;> exact period _ S h

/-! ## Controls for a single sampled white site -/

open Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Realization

private abbrev Row := Int → Bool
private def tick (x : Row) (u : Bool) (p : Int) :=
  rule (if p=1 then u else x (p-1)) (x p) (x (p+1))

-- Varying the boundary now flips the second cell two ticks later.
private def firstInput (x : Row) (v : Bool) :=
  xor v (tick (tick x false) false 2)
private def lastInput (x : Row) (v : Bool) := xor v (x 1 || x 2)

private theorem set_one (x : Row) (v : Bool) : tick x (lastInput x v) 1 = v := by
  change xor (xor v (x 1 || x 2)) (x 1 || x 2) = v
  cases v <;> cases (x 1 || x 2) <;> rfl

private theorem set_two (x : Row) (v b : Bool) : tick (tick x (firstInput x v)) b 2 = v := by
  change xor (xor (xor v (xor (xor false (x 1 || x 2))
    (tick x false 2 || tick x false 3))) (x 1 || x 2)) (tick x false 2 || tick x false 3) = v
  cases v <;> cases (x 1 || x 2) <;> cases (tick x false 2 || tick x false 3) <;> rfl

private def mid (x : Row) (a : Bool) := tick (tick x false) a
private def blocks (R : Row) (u : Nat → Bool) (choose : Nat → Row → Bool) : Nat → Row
  | 0 => R
  | k+1 => let x := blocks R u choose k
           let y := mid x (choose k x)
           tick y (lastInput y (u k))

private def driver (R : Row) (u : Nat → Bool) (choose : Nat → Row → Bool) (t : Nat) : Bool :=
  let k := t/3
  let x := blocks R u choose k
  if t%3=0 then false else if t%3=1 then choose k x
    else lastInput (mid x (choose k x)) (u k)

private theorem at_start (R : Row) (u : Nat → Bool) (v : Nat → Row → Bool) (k : Nat) :
    rh R (driver R u v) (3*k) = blocks R u v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have step (n : Nat) : rh R (driver R u v) (n+1) =
        tick (rh R (driver R u v) n) (driver R u v n) := rfl
    rw [Nat.mul_succ,step (3*k+2),step (3*k+1),step (3*k),ih]
    simp [driver,blocks,mid,show (3*k+2)/3=k by omega,show (3*k+1)/3=k by omega,
      show (3*k+2)%3=2 by omega,show (3*k+1)%3=1 by omega]

/-- For every literal initial right half, the two eastern sample sequences can
be independently prescribed from sample one, while every boundary sample is white.
The western completion is an unrestricted full-line initial configuration. -/
theorem arbitrary_sample_neighbors (R : Int → Bool) (u v : Nat → Bool) :
    ∃ x : Int → Bool, (∀ p, 1 ≤ p → x p = R p) ∧
      (∀ k, evol x (3*k) 0 = false) ∧
      (∀ k, evol x (3*(k+1)) 1 = u k ∧ evol x (3*(k+1)) 2 = v k) := by
  let choose (k : Nat) (x : Row) := firstInput (tick x false) (v k)
  let d := driver R u choose
  refine ⟨conf R d,(realize R d).1,?_,?_⟩
  · intro k
    rw [(realize R d).2]
    simp [d,driver]
  · intro k
    rw [evol_conf R d _ 1,evol_conf R d _ 2,ite_eq_left (by decide),ite_eq_left (by decide)]
    change rh R (driver R u choose) _ 1 = _ ∧ rh R (driver R u choose) _ 2 = _
    rw [at_start]
    exact ⟨set_one _ _,set_two _ _ _⟩

/-- The missing residue can also be surrounded by prescribed samples on
both immediate neighbors, with any fixed initial right half. The first
eastern sample is already fixed by that initial half. -/
theorem arbitrary_sample_flanks (R : Int → Bool) (west east : Nat → Bool) :
    ∃ x : Int → Bool, (∀ p, 1 ≤ p → x p=R p) ∧ (∀ k, evol x (3*k) 0=false) ∧
      (∀ k, evol x (3*k) (-1)=west k ∧ evol x (3*(k+1)) 1=east k) := by
  let choose (k : Nat) (row : Row) := xor (west k) (row 1)
  let d := driver R east choose
  refine ⟨conf R d,(realize R d).1,?_,?_⟩
  · intro k
    rw [(realize R d).2]; simp [d,driver]
  · intro k
    constructor
    · rw [evol_conf,ite_eq_right (by decide)]
      change xor (d (3*k+1)) (d (3*k) || rh R d (3*k) 1) = west k
      have a : d (3*k+1) = choose k (blocks R east choose k) := by
        simp [d,driver,show (3*k+1)%3=1 by omega,show (3*k+1)/3=k by omega]
      have b : d (3*k)=false := by simp [d,driver]
      rw [a,b,show d=driver R east choose by rfl,at_start]
      exact xor_xor_cancel _ _
    · rw [evol_conf,ite_eq_left (by decide)]
      change rh R (driver R east choose) _ 1 = _
      rw [at_start]
      exact set_one _ _

/-! ## Restart at the actual leftmost black cell -/

def EdgeRow (x : Int → Bool) := x 0=true ∧ ∀ p, p<0 → x p=false

/-- A uniform assertion about the eastern data, with no uniform deadline
assumed. Each of the three time residues has a hit at distance d. -/
def Covers (d : Nat) := ∀ x, EdgeRow x → ∀ s : Nat, s<3 →
  ∃ k, evol x (s+3*k) (d : Int)=true

private theorem restart_at (x : Int → Bool) (T t : Nat) (offset p : Int) :
    evol (fun z => evol x T (z+offset)) t p = evol x (T+t) (p+offset) := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    simp only [evol,ih]
    congr 1 <;> congr 1 <;> omega

/-- Moving the origin back to the new black edge shows that the distances
with a universal guarantee are downward closed. -/
theorem covers_previous (d : Nat) (h : Covers (d+1)) : Covers d := by
  intro x hx s hs
  let y (z : Int) := evol x 1 (z+(-1))
  have edge : EdgeRow y := by
    constructor
    · change rule (x (-2)) (x (-1)) (x 0)=true
      rw [hx.2 _ (by decide),hx.2 _ (by decide),hx.1]; rfl
    · intro z hz
      change rule (x (z+-1-1)) (x (z+-1)) (x (z+-1+1))=false
      rw [hx.2 _ (by omega),hx.2 _ (by omega),hx.2 _ (by omega)]; rfl
  let r := (s+2)%3
  obtain ⟨k,hit⟩ := h y edge r (by dsimp [r]; omega)
  rw [show y=(fun z => evol x 1 (z+(-1))) by rfl,restart_at] at hit
  refine ⟨(1+(r+3*k)-s)/3,?_⟩
  rw [show s+3*((1+(r+3*k)-s)/3)=1+(r+3*k) by dsimp [r]; omega]
  simpa +arith using hit

/-- Unbounded covered distances would give arbitrarily late black at the
specific singleton column -1 on each time residue. -/
theorem hit_at_minus_one_of_unbounded (h : ∀ D, ∃ d, D ≤ d ∧ Covers d) (T : Nat) :
    ∃ k, cell (T+3*k) (-1)=true := by
  obtain ⟨d,hd,cover⟩ := h T
  let S := d+1
  let y (z : Int) := evol seed S (z + -(S : Int))
  have edge : EdgeRow y := by
    constructor
    · simp only [y,evol_seed,Int.zero_add,cell_left_edge]
    · intro z hz
      rw [show y z=cell S (z + -(S : Int)) by simp [y,evol_seed]]
      apply cell_eq_false_of_lt
      omega
  let s := (3+T%3-S%3)%3
  obtain ⟨k,hit⟩ := cover y edge s (by dsimp [s]; omega)
  rw [show y=(fun z => evol seed S (z + -(S : Int))) by rfl,restart_at,evol_seed] at hit
  have ht : T ≤ S := by dsimp [S]; omega
  refine ⟨(S+(s+3*k)-T)/3,?_⟩
  rw [show T+3*((S+(s+3*k)-T)/3)=S+(s+3*k) by dsimp [s]; omega]
  simpa [show (d : Int) + -(S : Int) = -1 by dsimp [S]; omega] using hit

theorem exclude_three_of_unbounded (h : ∀ D, ∃ d, D ≤ d ∧ Covers d) : ¬Clock3 := by
  intro clock
  rcases clock_iff_markers.mp clock with ⟨T,wh⟩ | ⟨T,wh⟩
  · obtain ⟨k,b⟩ := hit_at_minus_one_of_unbounded h T
    simp [(wh k).1] at b
  · obtain ⟨k,b⟩ := hit_at_minus_one_of_unbounded h (T+1)
    have w := (wh k).2.1
    change cell (T+3*k+1) (-1)=false at w
    rw [show T+1+3*k=T+3*k+1 by omega,w] at b
    contradiction

/-! ## Residue-refined `CoversAt` channels, branching `HitTree` certificates, and sharpness witnesses -/

/-- Single-residue coverage at distance `d` and time residue `s`. -/
def CoversAt (d s : Nat) : Prop :=
  ∀ x, EdgeRow x → ∃ k, evol x (s + 3 * k) (d : Int) = true

/-- **Residue Decomposition of `Covers` and `(d + s) % 3`-Preserving Descent (`covers_iff_and_coversAt_previous`).** -/
theorem covers_iff_and_coversAt_previous :
    (∀ d : Nat, Covers d ↔ CoversAt d 0 ∧ CoversAt d 1 ∧ CoversAt d 2) ∧
    (∀ d s : Nat, CoversAt (d + 1) ((s + 2) % 3) → CoversAt d (s % 3)) := by
  refine ⟨fun d => ⟨fun h => ⟨fun x hx => h x hx 0 (by decide),
                              fun x hx => h x hx 1 (by decide),
                              fun x hx => h x hx 2 (by decide)⟩,
                    fun ⟨h0, h1, h2⟩ x hx s hs => ?_⟩, fun d s h x hx => ?_⟩
  · have hsc : s = 0 ∨ s = 1 ∨ s = 2 := by omega
    rcases hsc with rfl | rfl | rfl
    · exact h0 x hx
    · exact h1 x hx
    · exact h2 x hx
  · let y (z : Int) := evol x 1 (z + (-1))
    have edge : EdgeRow y := by
      constructor
      · change rule (x (-2)) (x (-1)) (x 0) = true
        rw [hx.2 _ (by decide), hx.2 _ (by decide), hx.1]; rfl
      · intro z hz
        change rule (x (z + -1 - 1)) (x (z + -1)) (x (z + -1 + 1)) = false
        rw [hx.2 _ (by omega), hx.2 _ (by omega), hx.2 _ (by omega)]; rfl
    let r := (s + 2) % 3
    obtain ⟨k, hit⟩ := h y edge
    rw [show y = (fun z => evol x 1 (z + (-1))) from rfl, restart_at] at hit
    have hd1 : ((d + 1 : Nat) : Int) + (-1 : Int) = (d : Int) := by omega
    rw [hd1] at hit
    refine ⟨(1 + (r + 3 * k) - s % 3) / 3, ?_⟩
    have ht1 : s % 3 + 3 * ((1 + (r + 3 * k) - s % 3) / 3) = 1 + (r + 3 * k) := by dsimp [r]; omega
    rw [ht1]; exact hit

/-- **Single-Diagonal Unbounded Coverage Forces Infinitely Late `-1` Blacks on Its Residue (`hit_at_minus_one_of_unbounded_diag`).** -/
theorem hit_at_minus_one_of_unbounded_diag (r : Nat) (hr : r < 3)
    (h : ∀ D, ∃ d, D ≤ d ∧ CoversAt d ((3 + r - d % 3) % 3))
    (T : Nat) (hTr : (T + 2) % 3 = r) :
    ∃ k, cell (T + 3 * k) (-1) = true := by
  obtain ⟨d, hd, cover⟩ := h T
  let S := d + 1
  let y (z : Int) := evol seed S (z + -(S : Int))
  have edge : EdgeRow y := by
    constructor
    · simp only [y, evol_seed, Int.zero_add, cell_left_edge]
    · intro z hz
      rw [show y z = cell S (z + -(S : Int)) by simp [y, evol_seed]]
      exact cell_eq_false_of_lt S _ (by omega)
  let s := (3 + r - d % 3) % 3
  obtain ⟨k, hit⟩ := cover y edge
  rw [show y = (fun z => evol seed S (z + -(S : Int))) from rfl, restart_at, evol_seed] at hit
  have hdS : (d : Int) + -(S : Int) = -1 := by dsimp [S]; omega
  rw [hdS] at hit
  refine ⟨(S + (s + 3 * k) - T) / 3, ?_⟩
  have htS : T + 3 * ((S + (s + 3 * k) - T) / 3) = S + (s + 3 * k) := by dsimp [S, s]; omega
  rw [htS]; exact hit

def maskEdgeRow (mask : Nat) (p : Int) : Bool :=
  if p < 0 then false else if p = 0 then true else mask.testBit p.toNat

theorem edgeRow_maskEdgeRow (mask : Nat) : EdgeRow (maskEdgeRow mask) :=
  ⟨by simp [maskEdgeRow], fun p hp => by simp [maskEdgeRow, hp]⟩

def initConeBits (d t mask : Nat) : Nat :=
  let base := 1 + 2 * (mask / 2)
  if d ≤ t then base <<< (t - d) else base >>> (d - t)

def stepConeBits (cur : Nat) : Nat :=
  cur ^^^ ((cur >>> 1) ||| (cur >>> 2))

def topConeBits (cur0 : Nat) : Nat → Nat
  | 0 => cur0
  | t + 1 => stepConeBits (topConeBits cur0 t)

def coneMaskHit (d t mask : Nat) : Bool :=
  (topConeBits (initConeBits d t mask) t).testBit 0

private theorem base_testBit_eq_maskEdgeRow (mask q : Nat) :
    (1 + 2 * (mask / 2)).testBit q = maskEdgeRow mask (q : Int) := by
  cases q with
  | zero => simp [maskEdgeRow, Nat.testBit_zero, Nat.add_mul_mod_self_left]
  | succ i =>
    rw [Nat.testBit_succ, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
    have h12 : 1 / 2 = 0 := rfl
    rw [h12, Nat.zero_add, ← Nat.testBit_succ]
    unfold maskEdgeRow
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp

private theorem initConeBits_testBit (d t mask u : Nat) :
    (initConeBits d t mask).testBit u = maskEdgeRow mask ((d : Int) - (t : Int) + (u : Int)) := by
  unfold initConeBits
  by_cases hdt : d ≤ t
  · simp only [hdt, ↓reduceIte, Nat.testBit_shiftLeft]
    by_cases hu : t - d ≤ u
    · simp only [hu, decide_true, Bool.true_and, base_testBit_eq_maskEdgeRow]
      congr 1; omega
    · simp only [hu, decide_false, Bool.false_and]
      have hneg : (d : Int) - (t : Int) + (u : Int) < 0 := by omega
      simp [maskEdgeRow, hneg]
  · simp only [hdt, ↓reduceIte, Nat.testBit_shiftRight, base_testBit_eq_maskEdgeRow]
    congr 1; omega

private theorem topConeBits_spec (x : Int → Bool) (i : Int) (cur0 : Nat) (T : Nat)
    (h0 : ∀ u, u ≤ 2 * T → cur0.testBit u = x (i + (u : Int))) :
    ∀ t, t ≤ T → ∀ j, j + 2 * t ≤ 2 * T →
      (topConeBits cur0 t).testBit j = evol x t (i + (j : Int) + (t : Int)) := by
  intro t
  induction t with
  | zero => intro _ j hj; simpa [topConeBits, evol] using h0 j (by omega)
  | succ t ih =>
    intro ht j hj
    simp only [topConeBits, stepConeBits, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
    rw [show 1 + j = j + 1 by omega, show 2 + j = j + 2 by omega,
        ih (by omega) j (by omega), ih (by omega) (j + 1) (by omega), ih (by omega) (j + 2) (by omega)]
    change rule _ _ _ = rule (evol x t (i + (j : Int) + ((t + 1 : Nat) : Int) - 1))
                              (evol x t (i + (j : Int) + ((t + 1 : Nat) : Int)))
                              (evol x t (i + (j : Int) + ((t + 1 : Nat) : Int) + 1))
    congr 1 <;> congr 1 <;> omega

private theorem evol_congr_cone {x y : Int → Bool} :
    ∀ (t : Nat) (p : Int), (∀ z, p - (t : Int) ≤ z → z ≤ p + (t : Int) → x z = y z) →
      evol x t p = evol y t p
  | 0, p, h => h p (by omega) (by omega)
  | t + 1, p, h => by
    change rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) =
           rule (evol y t (p - 1)) (evol y t p) (evol y t (p + 1))
    rw [evol_congr_cone t (p - 1) (fun z h1 h2 => h z (by omega) (by omega)),
        evol_congr_cone t p (fun z h1 h2 => h z (by omega) (by omega)),
        evol_congr_cone t (p + 1) (fun z h1 h2 => h z (by omega) (by omega))]

private theorem coneMaskHit_eq_evol {x : Int → Bool} (hx : EdgeRow x)
    {d t pos mask : Nat} (hreq : d + t ≤ pos)
    (hagree : ∀ q, q ≤ pos → maskEdgeRow mask (q : Int) = x (q : Int)) :
    coneMaskHit d t mask = evol x t (d : Int) := by
  unfold coneMaskHit
  have hsp := topConeBits_spec (maskEdgeRow mask) ((d : Int) - (t : Int)) (initConeBits d t mask) t
    (fun u _ => initConeBits_testBit d t mask u) t (Nat.le_refl _) 0 (by omega)
  have he0 : (d : Int) - (t : Int) + ((0 : Nat) : Int) + (t : Int) = (d : Int) := by omega
  rw [hsp, he0]
  exact evol_congr_cone t (d : Int) (fun z _ hz2 => by
    by_cases hzn : z < 0
    · rw [hx.2 z hzn]; simp [maskEdgeRow, hzn]
    · let q : Nat := z.toNat
      have hqz : (q : Int) = z := by dsimp [q]; omega
      rw [← hqz]; exact hagree q (by dsimp [q]; omega))

def packEastBits (x : Int → Bool) (start : Nat) : Nat → Nat
  | 0 => 0
  | rem + 1 => (if x (start : Int) then 1 else 0) + 2 * packEastBits x (start + 1) rem

private theorem packEastBits_spec (x : Int → Bool) (start rem : Nat) :
    packEastBits x start rem < 2 ^ rem ∧
    ∀ j, j < rem → (packEastBits x start rem).testBit j = x ((start + j : Nat) : Int) := by
  induction rem generalizing start with
  | zero => exact ⟨by simp [packEastBits], fun _ hj => by omega⟩
  | succ n ih =>
    obtain ⟨hlt, hbit⟩ := ih (start + 1)
    refine ⟨by unfold packEastBits; rw [Nat.pow_succ]; cases x (start : Int) <;> (simp only [Bool.false_eq_true, ↓reduceIte]; omega), fun j hj => ?_⟩
    unfold packEastBits
    cases j with
    | zero =>
      cases x (start : Int) <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
    | succ j =>
      cases x (start : Int) <;>
        simp only [↓reduceIte, Nat.testBit_succ, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
      · simpa [Nat.zero_add, show start + 1 + j = start + (j + 1) by omega] using hbit j (by omega)
      · have h12 : 1 / 2 = 0 := rfl
        rw [h12, Nat.zero_add, hbit j (by omega)]; congr 1; omega

def checkLeafAllExt (d t pos mask : Nat) : Bool :=
  let rem := (d + t) - pos
  (List.range (2 ^ rem)).all fun ext =>
    coneMaskHit d t (mask + ext * 2 ^ (pos + 1))

private theorem checkLeafAllExt_sound {x : Int → Bool} (hx : EdgeRow x)
    {d t pos mask : Nat} (hlt : mask < 2 ^ (pos + 1))
    (hagree : ∀ q, q ≤ pos → maskEdgeRow mask (q : Int) = x (q : Int))
    (hchk : checkLeafAllExt d t pos mask = true) : evol x t (d : Int) = true := by
  unfold checkLeafAllExt at hchk
  let rem := (d + t) - pos
  let ext := packEastBits x (pos + 1) rem
  obtain ⟨hext_lt, hext_bit⟩ := packEastBits_spec x (pos + 1) rem
  have hcone := List.all_eq_true.mp hchk ext (List.mem_range.mpr hext_lt)
  let mask' := mask + ext * 2 ^ (pos + 1)
  have hagree' : ∀ q, q ≤ pos + rem → maskEdgeRow mask' (q : Int) = x (q : Int) := by
    intro q hq
    by_cases hqp : q ≤ pos
    · by_cases hq0 : q = 0
      · subst hq0; simp [maskEdgeRow, hx.1]
      · have hmod : mask' % 2 ^ (pos + 1) = mask := by
          dsimp [mask']; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
        have htb : mask'.testBit q = mask.testBit q := by
          have hm := Nat.testBit_mod_two_pow mask' (pos + 1) q
          rw [hmod, decide_eq_true (by omega : q < pos + 1), Bool.true_and] at hm
          exact hm.symm
        have hprev := hagree q hqp
        unfold maskEdgeRow at hprev ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hprev ⊢
        simp only [Int.toNat_natCast] at hprev ⊢
        rw [htb]; exact hprev
    · let j := q - (pos + 1)
      have hqj : q = pos + 1 + j := by dsimp [j]; omega
      have hjrem : j < rem := by dsimp [j]; omega
      have hdiv : mask' / 2 ^ (pos + 1) = ext := by
        dsimp [mask']; rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]
      have htb : mask'.testBit q = ext.testBit j := by
        rw [hqj, ← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow, hdiv]
      unfold maskEdgeRow
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [Int.toNat_natCast]
      rw [htb, hext_bit j hjrem, ← hqj]
  have hev := coneMaskHit_eq_evol hx (d := d) (t := t) (pos := pos + rem) (mask := mask') (by dsimp [rem]; omega) hagree'
  rw [← hev]; exact hcone

inductive HitTree where
  | hit (k : Nat)
  | split (lo hi : HitTree)
  deriving DecidableEq, Repr

def verifyHitTree (d s kMax pos mask : Nat) : HitTree → Bool
  | .hit k => decide (k ≤ kMax) && checkLeafAllExt d (s + 3 * k) pos mask
  | .split lo hi =>
    verifyHitTree d s kMax (pos + 1) mask lo &&
    verifyHitTree d s kMax (pos + 1) (mask + 2 ^ (pos + 1)) hi

private theorem verifyHitTree_aux (tr : HitTree) (d s kMax pos mask : Nat) (x : Int → Bool)
    (hx : EdgeRow x) (hlt : mask < 2 ^ (pos + 1))
    (hagree : ∀ q, q ≤ pos → maskEdgeRow mask (q : Int) = x (q : Int))
    (hv : verifyHitTree d s kMax pos mask tr = true) :
    ∃ k, k ≤ kMax ∧ evol x (s + 3 * k) (d : Int) = true := by
  induction tr generalizing pos mask with
  | hit k =>
    unfold verifyHitTree at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    exact ⟨k, hv.1, checkLeafAllExt_sound hx hlt hagree hv.2⟩
  | split lo hi ih_lo ih_hi =>
    unfold verifyHitTree at hv
    simp only [Bool.and_eq_true] at hv
    cases hbit : x ((pos + 1 : Nat) : Int)
    · refine ih_lo (pos + 1) mask (Nat.lt_trans hlt (Nat.pow_lt_pow_right (by decide) (by omega)))
        (fun q hq => ?_) hv.1
      by_cases hqp : q ≤ pos
      · exact hagree q hqp
      · have hqe : q = pos + 1 := by omega
        subst hqe; rw [hbit]
        unfold maskEdgeRow; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [Int.toNat_natCast]; exact Nat.testBit_lt_two_pow hlt
    · refine ih_hi (pos + 1) (mask + 2 ^ (pos + 1)) (by rw [Nat.pow_succ]; omega)
        (fun q hq => ?_) hv.2
      by_cases hqp : q ≤ pos
      · have hprev := hagree q hqp
        by_cases hq0 : q = 0
        · subst hq0; simpa [maskEdgeRow] using hprev
        · unfold maskEdgeRow at hprev ⊢
          rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hprev ⊢
          simp only [Int.toNat_natCast] at hprev ⊢
          rw [Nat.add_comm, Nat.testBit_two_pow_add_gt (by omega)]; exact hprev
      · have hqe : q = pos + 1 := by omega
        subst hqe; rw [hbit]
        unfold maskEdgeRow; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [Int.toNat_natCast]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; rfl

/-- **Soundness of Branching Eastern Prefix-Certificate Trees (`coversAt_of_hitTree`).** -/
theorem coversAt_of_hitTree {d s kMax : Nat} {tr : HitTree}
    (hv : verifyHitTree d s kMax 0 1 tr = true) :
    (∀ x, EdgeRow x → ∃ k, k ≤ kMax ∧ evol x (s + 3 * k) (d : Int) = true) ∧ CoversAt d s := by
  have hmain : ∀ x, EdgeRow x → ∃ k, k ≤ kMax ∧ evol x (s + 3 * k) (d : Int) = true := by
    intro x hx
    refine verifyHitTree_aux tr d s kMax 0 1 x hx (by decide) (fun q hq => ?_) hv
    have hq0 : q = 0 := by omega
    subst hq0; simp [maskEdgeRow, hx.1]
  exact ⟨hmain, fun x hx => let ⟨k, _, hk⟩ := hmain x hx; ⟨k, hk⟩⟩

end Ruliology.CellularAutomata.Rule30ThirdTick
