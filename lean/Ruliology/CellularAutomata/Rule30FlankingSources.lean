module

public import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Spatial run ends around a period-three center

Under either possible period-three center tail, every sufficiently late aligned
three-tick block contains exactly one run end on the two outer bonds of columns
-3 through 0. The phase skeleton gives a smaller sufficient event too:
spatial 101 at -3,-2,-1 makes column -1 black on three consecutive ticks.

Unconditionally, the singleton has a run end on one of the three bonds between
ages U and 2U for U >= 2. Three consecutive quiet observations force a white
pair; left reconstruction brings it to the singleton's black edge.

With the western tail free, a full Rule 30 orbit can agree with any prescribed
initial right ray and arbitrarily long initial western prefix, then keep two
neighboring bonds quiet forever. The construction feeds column 1 back as the
trace of column 0 and uses the kit's left reconstruction.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30FlankingSources

open Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30EtherThree

abbrev c (t : Nat) := cell t 0
abbrev r (t : Nat) := cell t (-1)

/-- Count run ends at (-3,-2) and (-1,0) at the same tick. -/
def flank (t : Nat) : Nat :=
  (cell t (-3) && !cell t (-2)).toNat + (r t && !c t).toNat

private def flankValue (a b d x y : Bool) : Nat :=
  let q := rule b a x
  let Q := rule d b y
  ((rule Q q a) && !q).toNat + (a && !x).toNat

private theorem flank_eq (t : Nat) :
    flank t = flankValue (r t) (r (t+1)) (r (t+2)) (c t) (c (t+1)) := by
  have q (u : Nat) : cell u (-2) = rule (r (u+1)) (r u) (c u) := by
    simpa [rule,r,c,show (-1:Int)-1 = -2 by decide] using cell_left u (-1)
  have l : cell t (-3) = rule (cell (t+1) (-2)) (cell t (-2)) (r t) := by
    simpa [rule,r,show (-2:Int)+1 = -1 by decide,show (-2:Int)-1 = -3 by decide] using cell_left t (-2)
  simp only [flank, l, q, flankValue]

def block (t : Nat) := flank t + flank (t+1) + flank (t+2)

private theorem at011 {t : Nat}
    (c0 : c t=true) (c1 : c (t+1)=true) (c2 : c (t+2)=false) (c3 : c (t+3)=true)
    (r0 : r t=false) (r1 : r (t+1)=true) (r3 : r (t+3)=false) (r4 : r (t+4)=true) :
    block t = 1 := by
  simp only [block,flank_eq,c0,c1,c2,c3,r0,r1,r3,r4]
  cases r (t+2) <;> rfl

private theorem at001 {t : Nat}
    (c0 : c t=false) (c1 : c (t+1)=false) (c2 : c (t+2)=true) (c3 : c (t+3)=false)
    (r0 : r t=false) (r2 : r (t+2)=true) (r3 : r (t+3)=false) :
    block t = 1 := by
  simp only [block,flank_eq,c0,c1,c2,c3,r0,r2,r3]
  cases r (t+1) <;> cases r (t+4) <;> rfl

private theorem read_at (T t : Nat) (w : List Bool)
    (clock : ∀ s, T ≤ s → c s = wordAt3 w (s-T))
    (i p : Nat) (h : T ≤ t+i) (phase : (t+i-T)%3=p) :
    c (t+i) = w.getD p false := by
  rw [clock _ h,wordAt3,phase]

/-- For either clock there is exactly one run end on the two outer bonds
in each sufficiently late aligned block of three ticks. -/
theorem one_per_block (T : Nat) (w : List Bool) (hw : w=w001 ∨ w=w011)
    (clock : ∀ s, T ≤ s → c s = wordAt3 w (s-T)) :
    ∃ U, T ≤ U ∧ ∀ k, block (U+3*k) = 1 := by
  rcases hw with rfl | rfl
  · obtain ⟨S,hS,sk⟩ := skeleton_001 T clock
    refine ⟨T+3*S,by omega,?_⟩
    intro k
    let t := T+3*S+3*k
    have phase : (t-T)%3=0 := by dsimp [t]; omega
    have ht : S ≤ t := by dsimp [t]; omega
    have hT : T ≤ t := by omega
    have west0 (i : Nat) (ph : (t+i-T)%3=0) : r (t+i)=false :=
      ((col_m1_001 T clock _ (by omega)).1 ph).trans (sk _ (by omega) ph)
    apply at001 (t:=t)
    · exact read_at T t _ clock 0 0 (by omega) (by omega)
    · exact read_at T t _ clock 1 1 (by omega) (by omega)
    · exact read_at T t _ clock 2 2 (by omega) (by omega)
    · exact read_at T t _ clock 3 0 (by omega) (by omega)
    · exact west0 0 (by omega)
    · exact (col_m1_001 T clock _ (by omega)).2.2 (by omega)
    · exact west0 3 (by omega)
  · refine ⟨T+1,by omega,?_⟩
    intro k
    let t := T+1+3*k
    have phase : (t-T)%3=1 := by dsimp [t]; omega
    have ht : T ≤ t := by dsimp [t]; omega
    apply at011 (t:=t)
    · exact read_at T t _ clock 0 1 (by omega) (by omega)
    · exact read_at T t _ clock 1 2 (by omega) (by omega)
    · exact read_at T t _ clock 2 0 (by omega) (by omega)
    · exact read_at T t _ clock 3 1 (by omega) (by omega)
    · exact (col_m1_011 T clock _ (by omega)).2.1 (by omega)
    · exact (col_m1_011 T clock _ (by omega)).2.2 (by omega)
    · exact (col_m1_011 T clock _ (by omega)).2.1 (by omega)
    · exact (col_m1_011 T clock _ (by omega)).2.2 (by omega)

/-- The existing phase skeleton gives a smaller sufficient observation.
Some residue class modulo three at -1 is eventually white under either clock. -/
theorem white_phase_of_period_three {T : Nat} (clock : ∀ t, T ≤ t → c (t+3) = c t) :
    ∃ U, ∀ k, r (U+3*k) = false := by
  rcases normalize_period_three clock with ⟨S,_,word⟩ | ⟨S,_,word⟩
  · obtain ⟨V,hV,sk⟩ := skeleton_001 S word
    refine ⟨S+3*V,fun k => ?_⟩
    have phase : (S+3*V+3*k-S)%3=0 := by omega
    exact ((col_m1_001 S word _ (by omega)).1 phase).trans (sk _ (by omega) phase)
  · exact ⟨S+1,fun k => (col_m1_011 S word _ (by omega)).2.1 (by omega)⟩

/-- Spatial 101 at -3,-2,-1 makes -1 black on three consecutive ticks. -/
private theorem triple_black {t : Nat} (a : cell t (-3)=true)
    (b : cell t (-2)=false) (d : r t=true) : r (t+1)=true ∧ r (t+2)=true := by
  have q : cell (t+1) (-2)=false := by
    change rule (cell t (-3)) (cell t (-2)) (r t) = false
    rw [a,b,d]; rfl
  have step (s : Nat) (h : cell s (-2)=false) (hh : r s=true) : r (s+1)=true := by
    change rule (cell s (-2)) (r s) (c s)=true
    rw [h,hh]; rfl
  exact ⟨step t b d,step (t+1) q (step t b d)⟩

theorem cofinal_101_excludes
    (hits : ∀ U, ∃ t, U ≤ t ∧ cell t (-3)=true ∧ cell t (-2)=false ∧ r t=true) :
    ¬ ∃ T, ∀ t, T ≤ t → c (t+3)=c t := by
  rintro ⟨T,word⟩
  obtain ⟨U,white⟩ := white_phase_of_period_three word
  obtain ⟨t,ht,a,b,d⟩ := hits U
  obtain ⟨e,f⟩ := triple_black a b d
  let k := (t+2-U)/3
  have hw := white k
  have cases' : U+3*k=t ∨ U+3*k=t+1 ∨ U+3*k=t+2 := by dsimp [k]; omega
  rcases cases' with h | h | h <;> rw [h] at hw <;> simp_all

/-! ## A deadline from the singleton left edge -/

open Ruliology.CellularAutomata.Rule30Jen

structure Four where
  a : Bool
  b : Bool
  c : Bool
  d : Bool

def next (x : Four) (l r : Bool) : Four :=
  ⟨rule l x.a x.b, rule x.a x.b x.c, rule x.b x.c x.d, rule x.c x.d r⟩

def ends (a b : Bool) := a && !b
def quiet (x : Four) := !(ends x.a x.b || ends x.b x.c || ends x.c x.d)

private theorem middle (x : Four) (l r L R : Bool) :
    let y := next x l r
    quiet x = true → quiet y = true → quiet (next y L R) = true →
      y.a = false ∧ y.b = false := by
  obtain ⟨a,b,c,d⟩ := x
  revert a b c d l r L R
  decide +kernel

def strip (i : Int) (t : Nat) : Four :=
  ⟨cell t i, cell t (i+1), cell t (i+2), cell t (i+3)⟩

private theorem tick (i : Int) (t : Nat) :
    strip i (t+1) = next (strip i t) (cell t (i-1)) (cell t (i+4)) := by
  simp [strip, next, cell, show i+2-1=i+1 by omega, show i+3-1=i+2 by omega,
    show i+1+1=i+2 by omega, show i+2+1=i+3 by omega, show i+3+1=i+4 by omega]

private theorem white_pair {i : Int} {t : Nat}
    (h : ∀ k, k ≤ 2 → quiet (strip i (t+k)) = true) :
    cell (t+1) i = false ∧ cell (t+1) (i+1) = false := by
  have h₁ := h 1 (by decide)
  have h₂ := h 2 (by decide)
  rw [tick i (t+1), tick i t] at h₂
  rw [tick i t] at h₁
  have hm := middle _ _ _ _ _ (h 0 (by decide)) h₁ h₂
  change (strip i (t+1)).a = false ∧ (strip i (t+1)).b = false
  rw [tick]
  exact hm

/-- A white vertical pair of height d+1 forces the western tip white at its base. -/
private theorem white_tip (d : Nat) (t : Nat) (i : Int)
    (h : ∀ k, k ≤ d → cell (t+k) i = false ∧ cell (t+k) (i+1) = false) :
    cell t (i-d) = false := by
  induction d generalizing i with
  | zero => simpa using (h 0 (by omega)).1
  | succ d ih =>
    have hw (k : Nat) (hk : k ≤ d) :
        cell (t+k) (i-1) = false ∧ cell (t+k) (i-1+1) = false := by
      have h₀ := h k (by omega)
      have h₁ := (h (k+1) (by omega)).1
      rw [show t+(k+1)=t+k+1 by omega] at h₁
      rw [cell_left, h₀.1, h₀.2, h₁]
      simpa using h₀.1
    simpa only [show i-(d.succ : Int)=i-1-(d : Int) by omega] using ih (i-1) hw

/-- Some bond in [i,i+3] sees spatial 10 between U and U+d+2, inclusive.
Here d is the distance from i to the singleton's black left edge at age U+1. -/
theorem deadline (U d : Nat) (i : Int) (hd : i + (U : Int) + 1 = d) :
    ∃ t, U ≤ t ∧ t ≤ U+d+2 ∧ quiet (strip i t) = false := by
  apply Classical.byContradiction
  intro neg
  have no (t : Nat) (lo : U ≤ t) (hi : t ≤ U+d+2) : quiet (strip i t) ≠ false :=
    fun hit => neg ⟨t,lo,hi,hit⟩
  have h k (hk : k ≤ d) := white_pair (i := i) (t := U+k)
    (fun j hj => by
      have hn := no (U+k+j) (by omega) (by omega)
      cases hb : quiet (strip i (U+k+j)) <;> simp_all)
  have hw := white_tip d (U+1) i (fun k hk => by
    rw [show U+1+k=U+k+1 by omega]
    exact h k hk)
  rw [show i-(d : Int) = -((U+1 : Nat) : Int) by omega, cell_left_edge] at hw
  contradiction

/-- In particular the run end recurs somewhere on the three bonds around the target. -/
theorem target_neighborhood (U : Nat) (hU : 2 ≤ U) :
    ∃ t, U ≤ t ∧ t ≤ 2*U ∧ quiet (strip (-3) t) = false := by
  obtain ⟨t,lo,hi,h⟩ := deadline U (U-2) (-3) (by omega)
  exact ⟨t,lo,by omega,h⟩

/-! ## Full-line control with an unrestricted western tail -/

open Ruliology.CellularAutomata.Rule30Realization Ruliology.CellularAutomata.Rule30Jen

private def rightRow (x : Int → Bool) (n : Nat) : Nat → Int → Bool
  | 0, p => x p
  | t+1, p =>
    let prev := rightRow x n t
    let input := if t ≤ n then evol x t 0 else prev 1
    rule (if p=1 then input else prev (p-1)) (prev p) (prev (p+1))

private def driver (x : Int → Bool) (n t : Nat) :=
  if t ≤ n then evol x t 0 else rightRow x n t 1

private theorem driven_eq (x : Int → Bool) (n t : Nat) :
    ∀ p, rh x (driver x n) t p = rightRow x n t p := by
  induction t with
  | zero => intro p; rfl
  | succ t ih => intro p; simp only [rh,rightRow,ih,driver]

/-- Preserve any initial row from -n eastward and its observed trace through
n. The two columns at 0 and 1 then agree forever from n+1, and 1 implies 2
from n+2. The initial western tail of the new row is unrestricted. -/
theorem mirror_after_prefix (x : Int → Bool) (n : Nat) :
    ∃ y : Int → Bool,
      (∀ p, -(n : Int) ≤ p → y p=x p) ∧
      (∀ t, t ≤ n → evol y t 0=evol x t 0) ∧
      (∀ t, n<t → evol y t 0=evol y t 1) ∧
      (∀ t, n+1<t → evol y t 1=true → evol y t 2=true) := by
  let d := driver x n
  let y := conf x d
  have h0 (t : Nat) : evol y t 0=d t := (realize x d).2 t
  have h1 (t : Nat) : evol y t 1=rightRow x n t 1 := by
    rw [show y=conf x d by rfl, evol_conf,ite_eq_left (by decide)]
    exact driven_eq x n t 1
  have agree (t : Nat) (h : t ≤ n) : d t = evol x t 0 := by simp [d,driver,h]
  have mirror (t : Nat) (ht : n<t) : evol y t 0=evol y t 1 := by
    rw [h0,h1]; simp [d,driver,show ¬t≤n by omega]
  refine ⟨y,?_,fun t ht => (h0 t).trans (agree t ht),mirror,?_⟩
  · intro p hp
    have base : conf x (fun t => evol x t 0) = x :=
      unique (realize x _).1 (realize x _).2
    by_cases pos : 1 ≤ p
    · exact (realize x d).1 p pos
    · change conf x d p = x p
      calc
        conf x d p = conf x (fun t => evol x t 0) p := by
          simp only [conf,ite_eq_right pos]
          exact lc_congr x _ _ (fun s hs => agree s (by omega))
        _ = x p := congrFun base p
  · intro t ht
    cases t with
    | zero => omega
    | succ t =>
      have h := mirror t (by omega)
      change rule (evol y t 0) (evol y t 1) (evol y t 2)=true →
        rule (evol y t 1) (evol y t 2) (evol y t 3)=true
      rw [h]
      cases evol y t 1 <;> cases evol y t 2 <;> cases evol y t 3 <;> decide

private theorem from_ray {x y : Int → Bool} {a : Int} (h : ∀ p, a ≤ p → x p = y p)
    (t : Nat) (p : Int) (hp : a + t ≤ p) : evol x t p = evol y t p := by
  induction t generalizing p with
  | zero => exact h p (by omega)
  | succ t ih => simp only [evol, ih (p-1) (by omega), ih p (by omega), ih (p+1) (by omega)]

/-- A finite edit strictly west of the preserved prefix suffices for any
finite duration. In particular a finite starting row stays finite. -/
theorem finite_edit_control (x : Int → Bool) (n M : Nat) (hn : n ≤ M) :
    ∃ z : Int → Bool,
      (∀ p, p < -(M : Int) ∨ -(n : Int) ≤ p → z p = x p) ∧
      (∀ t, t ≤ n → evol z t 0 = evol x t 0) ∧
      (∀ t, n < t → t ≤ M → evol z t 0 = evol z t 1) ∧
      (∀ t, n+1 < t → t ≤ M → evol z t 1 = true → evol z t 2 = true) := by
  obtain ⟨y,ray,initial,equal,order⟩ := mirror_after_prefix x n
  let z (p : Int) := if -(M : Int) ≤ p then y p else x p
  have light (t : Nat) (p : Int) (ht : t ≤ M) (hp : 0 ≤ p) : evol z t p = evol y t p :=
    from_ray (a := -(M : Int)) (fun k hk => ite_eq_left hk) t p (by omega)
  refine ⟨z,?_,?_,?_,?_⟩
  · intro p h
    rcases h with lt | ge
    · exact ite_eq_right (by omega)
    · exact (ite_eq_left (by omega : -(M : Int) ≤ p)).trans (ray p ge)
  · intro t ht
    exact (light t 0 (by omega) (by decide)).trans (initial t ht)
  · intro t lo hi
    rw [light t 0 hi (by decide),light t 1 hi (by decide)]
    exact equal t lo
  · intro t lo hi
    rw [light t 1 hi (by decide),light t 2 hi (by decide)]
    exact order t lo

end Ruliology.CellularAutomata.Rule30FlankingSources
