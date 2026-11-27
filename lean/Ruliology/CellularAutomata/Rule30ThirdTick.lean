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

end Ruliology.CellularAutomata.Rule30ThirdTick
