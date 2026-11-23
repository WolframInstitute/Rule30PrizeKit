module

public import Ruliology.CellularAutomata.GoldenStripCover
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen

/-! Repetitions of the golden half-circle word at all phases and the resulting
exclusion for the even-time right neighbour of an eventual Rule 30 clock. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GoldenHalfCircle
open Golden Golden.Q5 Lean.Grind

structure UnitScale where
  A : Int
  B : Int
  norm : A*A - 5*B*B = 1
  Apos : 0 < A
  Bnonneg : 0 ≤ B

def unitAt : Nat → UnitScale
  | 0 => ⟨1,0,by decide,by decide,by decide⟩
  | n+1 =>
    let u := unitAt n
    ⟨9*u.A+20*u.B, 4*u.A+9*u.B, by have := u.norm; grind,
      by have := u.Apos; have := u.Bnonneg; omega, by have := u.Apos; have := u.Bnonneg; omega⟩

private theorem large (n : Nat) : (n:Int)+1 ≤ (unitAt n).A := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (_:Int) ≤ 9*(unitAt n).A+20*(unitAt n).B
    have := (unitAt n).Bnonneg; omega

def expand (u : UnitScale) : Q5 := ⟨u.A,u.B⟩
def shrink (u : UnitScale) : Q5 := ⟨u.A,-u.B⟩

private theorem unit_prod (u : UnitScale) : shrink u * expand u = 1 :=
  ext' (by simp [shrink,expand]; have := u.norm; grind) (by simp [shrink,expand]; grind)

private theorem expansion (u : UnitScale) : expand u = (u.A : Q5)+(u.B : Q5)*r5 := repr' _
private theorem scale_bounds (u : UnitScale) (hu : 1000 ≤ u.A) :
    0 < shrink u ∧ 1000*shrink u ≤ 1 ∧ 0 ≤ shrink u * shrink u ∧
    1000000*(shrink u*shrink u) ≤ 1 := by
  have ha : (1000 : Q5) ≤ expand u := ⟨0,by change 0 ≤ u.A-1000 ∧ 0 ≤ u.B-0; have := u.Bnonneg; omega⟩
  have inv := unit_prod u
  have hp : 0 < shrink u := by
    apply Classical.byContradiction; intro h
    have h' : shrink u ≤ 0 := by grind
    have := OrderedRing.mul_le_mul_of_nonneg_right h' (show 0 ≤ expand u by grind)
    grind
  have hle := OrderedRing.mul_le_mul_of_nonneg_right ha (Std.le_of_lt hp)
  have hs : 1000*shrink u ≤ 1 := by grind
  have hsq := OrderedRing.mul_le_mul_of_nonneg_left hs (show 0 ≤ 1000*shrink u by grind)
  exact ⟨hp,hs, Std.le_of_lt (OrderedRing.mul_pos hp hp), by grind⟩

private theorem phys_add (p q : Q5) : phys (p+q) = phys p + phys q :=
  ext' (by simp [phys]; omega) (by simp [phys])
private theorem phys_back (u : UnitScale) (k : Q5) : phys (shrink u * k) = expand u * phys k :=
  ext' (by simp [phys,shrink,expand]; grind) (by simp [phys,shrink,expand]; grind)
private theorem time_sum (p : Q5) : 2*r5*(p.b : Q5) = p + phys p :=
  ext' (by simp [r5,phys]; change 5*(0:Int)*p.b = p.a + -p.a; omega) (by simp [r5,phys]; change (2:Int)*p.b = p.b+p.b; omega)

private structure Config (u : UnitScale) (θ : Q5) where
  o : Q5
  s : Q5
  z : Q5
  hs : s = expand u * θ + o
  hz : z = -(shrink u) * θ + phys o
  sb : 0 ≤ s ∧ s < 1
  zb : -1 < z ∧ z ≤ 5
  phase : (u.B : Q5)*θ + (o.b : Q5) < 1

private noncomputable def config (u : UnitScale) (θ : Q5) : Config u θ := by
  let y := (u.B : Q5)*θ
  let b := -floor y
  let k := expand u*θ + (b : Q5)*r5
  let a := -floor k
  let o : Q5 := ⟨a,b⟩
  let s := expand u*θ + o
  let z := -(shrink u)*θ + phys o
  have reduce (w : Q5) : 0 ≤ w+((-floor w : Int) : Q5) ∧ w+((-floor w : Int) : Q5) < 1 := by
    have := floor_spec w; rw [Ring.intCast_neg]; grind
  have sy := reduce y
  have sb : 0 ≤ s ∧ s < 1 := by
    have := reduce k
    have ho : o = (a : Q5) + (b : Q5)*r5 := repr' _
    dsimp only [s]; rw [ho]; dsimp only [k,a] at *; grind
  have sum : s+z = 2*r5*(y+(b:Q5)) := by
    have h₁ : expand u - shrink u = 2*r5*(u.B : Q5) :=
      ext' (by simp [expand,shrink,r5]; change 0 = 5*(0:Int)*u.B; omega) (by simp [expand,shrink,r5]; change u.B + u.B = 2*u.B; omega)
    have h₂ := time_sum o
    change 2*r5*(b:Q5) = o+phys o at h₂
    dsimp only [s,z,y]; grind
  have dr := root_bounds
  have lo := OrderedRing.mul_le_mul_of_nonneg_left sy.1 (show 0 ≤ 2*r5 by grind)
  have hi := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt sy.2) (show 0 ≤ 2*r5 by grind)
  exact ⟨o,s,z,rfl,rfl,sb,by grind,sy.2⟩

private def tick {u θ} (c : Config u θ) (p : Q5) : Int := (shrink u * (c.o+p)).b

private theorem internal {u θ} (c : Config u θ) (p : Q5) :
    shrink u * (c.s+p) = θ + shrink u*(c.o+p) := by
  rw [c.hs]; have := unit_prod u; grind

private theorem lag_time (u : UnitScale) (p : Q5) :
    (2*r5*shrink u)*((shrink u*p).b : Q5) = phys p + (shrink u*shrink u)*p := by
  have hh := time_sum (shrink u*p)
  rw [phys_back] at hh
  have := unit_prod u; grind

private theorem lattice_time {u θ} (c : Config u θ) (p : Q5) :
    (2*r5*shrink u)*(tick c p : Q5) = c.z + phys p + (shrink u*shrink u)*(c.s+p) := by
  have ht := lag_time u (c.o+p)
  rw [phys_add] at ht
  have := internal c p; rw [c.hz]; unfold tick; grind

private theorem member_data {e : Q5} (he : e ∈ families) :
    -1 < e ∧ e < 1 ∧ 1 ≤ phys e ∧ e.a ≤ 0 ∧ -29 ≤ e.a ∧ 1 ≤ e.b ∧ e.b ≤ 13 ∧ (e.a+e.b)%2 = 0 := by
  have lt_at_three (p q : Q5)
      (pos : 0 ≤ (it 3 (q-p)).a ∧ 0 ≤ (it 3 (q-p)).b) (ne : p ≠ q) : p < q := by
    have le : p ≤ q := ⟨3,pos⟩
    exact ⟨le,fun rev => ne (Std.le_antisymm le rev)⟩
  simp [families] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨lt_at_three _ _ (by decide) (by decide),lt_at_three _ _ (by decide) (by decide),
      ⟨3,by decide⟩,by decide,by decide,by decide,by decide,by decide⟩

private theorem strip_facts {e : Q5} (he : e ∈ families) :
    -1 ≤ low e ∧ high e ≤ 1 ∧ high e - low e < 1 := by
  have := member_data he
  unfold low high; split <;> grind

private theorem tick_formula (u : UnitScale) (p : Q5) :
    ((shrink u*p).b : Q5) = expand u*(p.b : Q5) - (u.B : Q5)*p :=
  ext' (by simp [expand,shrink]; grind) (by simp [expand,shrink])

private theorem tick_diff {u θ} (c : Config u θ) (p r : Q5) :
    (tick c r : Q5) - (tick c p : Q5) =
    expand u*((r.b : Q5)-(p.b : Q5)) - (u.B : Q5)*(r-p) := by
  unfold tick
  rw [tick_formula,tick_formula]; simp only [add_b,Ring.intCast_add]; grind

private theorem cast_step {i j : Int} (h : i < j) : (i : Q5)+1 ≤ (j : Q5) := by
  have := cast_le (i := i+1) h
  simpa only [Ring.intCast_add,Ring.intCast_one] using this

/-- Within a single strip, strictly increasing sample times have strictly increasing lattice heights. -/
private theorem height_lt {u θ} (c : Config u θ) {e p r : Q5}
    (he : e ∈ families) (hp : crosses e c.s p) (hr : crosses e c.s r)
    (ht : tick c p < tick c r) : p.b < r.b := by
  have sf := strip_facts he
  have width : -1 < r-p ∧ r-p < 1 := by unfold crosses at hp hr; grind
  by_cases hb : r.b = p.b
  · have de : r-p = ((r.a : Q5)-(p.a : Q5)) := ext' (by simp) (by simp [hb])
    rw [de] at width
    have hae : r.a = p.a := by
      by_cases h : r.a < p.a
      · have := cast_step h; grind
      by_cases h : p.a < r.a
      · have := cast_step h; grind
      omega
    have := ext' hae hb; grind
  by_cases hb' : p.b < r.b
  · exact hb'
  have eb : (u.B : Q5) ≤ expand u := ⟨1,by
    simp [it,up,expand]; have := u.Apos; have := u.Bnonneg; omega⟩
  have bn : (0 : Q5) ≤ (u.B : Q5) := cast_le u.Bnonneg
  have hh := OrderedRing.mul_le_mul_of_nonneg_left (cast_step (show r.b < p.b by omega))
    (show 0 ≤ expand u by grind)
  have hv := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt width.1) bn
  have := tick_diff c p r
  have := cast_lt ht
  grind

private theorem cancel_le {x y k : Q5} (hk : 0 < k) (h : k*x ≤ k*y) : x ≤ y := by
  by_cases hy : y < x
  · have := Q5.mul_lt hy hk; grind
  · grind
private theorem cancel_lt {x y k : Q5} (hk : 0 < k) (h : k*x < k*y) : x < y := by
  by_cases hy : y ≤ x
  · have := OrderedRing.mul_le_mul_of_nonneg_left hy (Std.le_of_lt hk); grind
  · grind

private theorem floor_stays (y v e : Q5) (hv : 0 < v) (hne : low e < high e)
    (avoid : ∀ m : Int, ¬ (v*low e ≤ y-(m : Q5) ∧ y-(m : Q5) < v*high e)) :
    floor (y+v*e) = floor y := by
  have bounds : low e ≤ 0 ∧ low e ≤ -e ∧ 0 ≤ high e ∧ -e ≤ high e := by
    unfold low high at *; split at hne <;> simp_all <;> grind
  have l₁ := OrderedRing.mul_le_mul_of_nonneg_left bounds.1 (Std.le_of_lt hv)
  have l₂ := OrderedRing.mul_le_mul_of_nonneg_left bounds.2.1 (Std.le_of_lt hv)
  have h₁ := OrderedRing.mul_le_mul_of_nonneg_left bounds.2.2.1 (Std.le_of_lt hv)
  have h₂ := OrderedRing.mul_le_mul_of_nonneg_left bounds.2.2.2 (Std.le_of_lt hv)
  have f := floor_spec y
  have g := floor_spec (y+v*e)
  by_cases ha : floor (y+v*e) < floor y
  · have := cast_step ha; have := avoid (floor y); grind
  by_cases hb : floor y < floor (y+v*e)
  · have := cast_step hb; have hh := avoid (floor y+1)
    rw [Ring.intCast_add,Ring.intCast_one] at hh
    grind
  omega

private noncomputable def word (θ : Q5) (t : Nat) := decide ((floor (θ+(t:Q5)*(r5-1)))%2 = 1)

/-- A change of floor lifts to an intervening crossing. The even translation of the floor preserves parity. -/
private theorem copied {u θ} (c : Config u θ) (hu : 1000 ≤ u.A) {e p r : Q5}
    (he : e ∈ families) (gap : consecutive e p r c.s) (t q : Nat) (hq : (q:Int) = (shrink u*e).b)
    (hp : tick c p < t) (hr : (t:Int) < tick c r) : word θ t = word θ (t+q) := by
  let y := θ+(t:Q5)*(r5-1)
  have hv := (scale_bounds u hu).1
  have stable : floor (y+shrink u*e) = floor y := by
    have gp := gap.2.1
    apply floor_stays _ _ _ hv (by unfold crosses at gp; grind)
    intro m hit
    let base : Q5 := ⟨-(t:Int)-m,t⟩
    let w := expand u*base-c.o
    have back : shrink u*(c.o+w) = base := by dsimp [w]; have := unit_prod u; grind
    have hw := internal c w
    rw [back] at hw
    have eqb : θ+base = y-(m:Q5) := by
      have heq := repr' base
      dsimp only [base] at heq
      dsimp only [base]; rw [heq]; simp only [Ring.intCast_sub,Ring.intCast_neg,Ring.intCast_natCast]; dsimp only [y]; grind
    rw [←eqb,←hw] at hit
    have hc : crosses e c.s w := ⟨cancel_le hv hit.1,cancel_lt hv hit.2⟩
    have ht : tick c w = t := congrArg Q5.b back
    exact gap.2.2.2 w (height_lt c he gap.2.1 hc (by omega))
      (height_lt c he hc gap.2.2.1 (by omega)) hc
  let k := -(shrink u*e).a-(shrink u*e).b
  have eqk : k = -(u.A-u.B)*(e.a+e.b) + 2*(2*u.B*e.b) := by dsimp [k,shrink]; grind
  have parity := (member_data he).2.2.2.2.2.2.2
  have hk : k%2 = 0 := by rw [eqk,Int.add_emod,Int.mul_emod _ (e.a+e.b),parity]; simp
  have hq' : (q:Q5) = ((shrink u*e).b : Q5) := congrArg (fun i : Int => (i : Q5)) hq
  have hy : θ+((t+q : Nat):Q5)*(r5-1) = y+shrink u*e+(k:Q5) := by
    have h := repr' (shrink u*e)
    dsimp only [y,k]; rw [Semiring.natCast_add,hq',Ring.intCast_sub,Ring.intCast_neg]; grind
  unfold word
  rw [hy]
  have shift (z : Q5) : floor (z+(k:Q5)) = floor z+k := by
    apply floor_unique; rw [Ring.intCast_add]; have := floor_spec z; grind
  rw [shift,stable,Int.add_emod,hk]; simp [y]

/-- A phase-independent prefix length containing both copies at this scale. -/
private def horizon (u : UnitScale) : Nat := (120*u.A+400*u.B+10).toNat

/-- The last certificate height is at most 100. The reduced phase bounds its signed sample time independently of θ. -/
private theorem end_bound {u θ} (c : Config u θ) {e r : Q5} (he : e ∈ families)
    (hr : crosses e c.s r) (hb : r.b ≤ 100) : tick c r ≤ 101*u.A+304*u.B := by
  have phase := c.phase
  have s := c.hs
  have formula : (tick c r : Q5) =
      expand u*((u.B:Q5)*θ+(c.o.b:Q5)+(r.b:Q5))-(u.B:Q5)*(c.s+r) := by
    unfold tick; rw [tick_formula]; simp only [add_b,Ring.intCast_add]; grind
  have bn : (0 : Q5) ≤ (u.B:Q5) := cast_le u.Bnonneg
  have an : (0 : Q5) ≤ (u.A:Q5) := cast_le (i := 0) (by have := u.Apos; omega)
  have root := root_bounds
  have ex := expansion u
  have bm := OrderedRing.mul_le_mul_of_nonneg_left (show r5 ≤ 3 by grind) bn
  have bp := OrderedRing.mul_le_mul_of_nonneg_left (show 0 ≤ r5 by grind) bn
  have rb : (r.b:Q5) ≤ 100 := cast_le hb
  have hmul := OrderedRing.mul_le_mul_of_nonneg_left
    (show (u.B:Q5)*θ+(c.o.b:Q5)+(r.b:Q5) ≤ 101 by grind) (show 0 ≤ expand u by grind)
  have sf := strip_facts he
  have neg := OrderedRing.mul_le_mul_of_nonneg_left (show -1 ≤ c.s+r by unfold crosses at hr; grind) bn
  apply uncast
  simp only [Ring.intCast_add,Ring.intCast_mul]
  grind

private theorem lag_bounds (u : UnitScale) {e : Q5} (he : e ∈ families) :
    u.A ≤ (shrink u*e).b ∧ (shrink u*e).b ≤ 13*u.A+29*u.B := by
  have data := member_data he
  have bn := u.Bnonneg
  have an : 0 ≤ u.A := by have := u.Apos; omega
  have h₁ := Int.mul_le_mul_of_nonneg_left data.2.2.2.2.2.1 an
  have h₂ := Int.mul_le_mul_of_nonneg_left data.2.2.2.2.2.2.1 an
  have h₃ := Int.mul_le_mul_of_nonneg_left data.2.2.2.1 bn
  have h₄ := Int.mul_le_mul_of_nonneg_left data.2.2.2.2.1 bn
  simp only [mul_b,shrink]; grind

/-- Transfer the certificate’s 10% geometric margin to the sample times, retaining 999/10000. -/
private theorem scaled_bound {h Q X Y A B E : Q5} (hn : 0 ≤ h) (hh : 1000000*h ≤ 1)
    (hq : 1 ≤ Q) (ha : A ≤ 1) (hb : -1 ≤ B) (he : E ≤ 1)
    (hx : 11*Q ≤ 10*Y) (hy : 11*Q ≤ 10*(Y-2*X)) :
    10999*(Q+h*E) ≤ 10000*(Y+h*B) ∧
    10999*(Q+h*E) ≤ 10000*((Y+h*B)-2*(X+h*A)) := by
  have := OrderedRing.mul_le_mul_of_nonneg_left ha hn
  have := OrderedRing.mul_le_mul_of_nonneg_left hb hn
  have := OrderedRing.mul_le_mul_of_nonneg_left he hn
  grind

private theorem run {u θ} (c : Config u θ) (hu : 1000 ≤ u.A) :
    ∃ a b q : Nat, (∃ e ∈ families, q = (shrink u*e).b.toNat) ∧ u.A ≤ (q:Int) ∧
      b+q ≤ horizon u ∧ 10999*q+20000*a ≤ 10000*b+30000 ∧
      ∀ t : Nat, a ≤ t → t ≤ b → word θ t = word θ (t+q) := by
  obtain ⟨e,he,p,r,hrb,gap,hx,hy⟩ := golden_strip_cover c.s c.z c.sb c.zb
  have sc := scale_bounds u hu
  have data := member_data he
  have sf := strip_facts he
  have gp := gap.2.1
  have gr := gap.2.2.1
  have margin := scaled_bound (X := c.z+phys p) (Y := c.z+phys r) sc.2.2.1 sc.2.2.2
    data.2.2.1 (show c.s+p ≤ 1 by unfold crosses at gp; grind)
    (show -1 ≤ c.s+r by unfold crosses at gr; grind) (Std.le_of_lt data.2.1) hx (by grind)
  rw [←lag_time,←lattice_time,←lattice_time] at margin
  let k := 2*r5*shrink u
  have pos : 0 < k := OrderedRing.mul_pos (by have := root_bounds; grind) sc.1
  have h₁ : 10999*(shrink u*e).b ≤ 10000*tick c r := by
    apply uncast
    simp only [Ring.intCast_mul]
    apply cancel_le pos; dsimp only [k]; grind
  have h₂ : 10999*(shrink u*e).b ≤ 10000*(tick c r-2*tick c p) := by
    apply uncast
    simp only [Ring.intCast_mul,Ring.intCast_sub]
    apply cancel_le pos; dsimp only [k]; grind
  have lag := lag_bounds u he
  have stop := end_bound c he gr hrb
  have bn := u.Bnonneg
  refine ⟨(tick c p+1).toNat,(tick c r-1).toNat,(shrink u*e).b.toNat,⟨e,he,rfl⟩,by omega,
    by unfold horizon; omega,by omega,?_⟩
  intro t a b
  exact copied c hu he gap t _ (by omega) (by omega) (by omega)

/-- Exact integer test for x < y√5, including negative x and y. -/
def LtSqrt5 (x y : Int) : Prop :=
  (x < 0 ∧ (0 ≤ y ∨ 5*y*y < x*x)) ∨ (0 ≤ x ∧ 0 < y ∧ x*x < 5*y*y)

/-- Every pair of samples stays within one unit of the line of slope √5 − 1.
For a real phase θ, taking f(t) = ⌊θ+t(√5−1)⌋ gives this inequality directly
from the two floor bounds. -/
def GoldenLine (f : Nat → Int) : Prop :=
  ∀ s t : Nat, LtSqrt5 (f s-f t-1+((s:Int)-t)) ((s:Int)-t)

private theorem sq_mono {x y : Q5} (hx : 0 ≤ x) (h : x ≤ y) : x*x ≤ y*y := by
  have := OrderedRing.mul_le_mul_of_nonneg_left h hx
  have := OrderedRing.mul_le_mul_of_nonneg_right h (show 0 ≤ y by grind)
  grind

private theorem lt_root {x y : Int} (h : LtSqrt5 x y) : (x : Q5) < (y : Q5)*r5 := by
  have root := root_bounds
  have square (v : Q5) : (v*r5)*(v*r5) = 5*v*v := by have := r5_sq; grind
  have sq := square (y:Q5)
  rcases h with ⟨hx,hy | hsq⟩ | ⟨hx,hy,hsq⟩
  · have := cast_lt (j := 0) hx
    have := OrderedRing.mul_le_mul_of_nonneg_right (cast_le hy) (show 0 ≤ r5 by grind)
    grind
  · have hc := cast_lt hsq
    simp only [Ring.intCast_mul] at hc
    have hn : (x : Q5) < 0 := cast_lt hx
    by_cases hle : (y:Q5)*r5 ≤ (x:Q5)
    · have hm := sq_mono (show 0 ≤ -(x:Q5) by grind) (show -(x:Q5) ≤ -((y:Q5)*r5) by grind)
      grind
    · grind
  · have hc := cast_lt hsq
    simp only [Ring.intCast_mul] at hc
    have hp : 0 < (y : Q5)*r5 := OrderedRing.mul_pos (cast_lt hy) (by grind)
    by_cases hle : (y:Q5)*r5 ≤ (x:Q5)
    · have := sq_mono (Std.le_of_lt hp) hle; grind
    · grind

/-- The squared integer test agrees with the order in the quadratic ring. -/
theorem ltSqrt5_iff (x y : Int) : LtSqrt5 x y ↔ (x:Q5) < (y:Q5)*r5 := by
  refine ⟨lt_root, ?_⟩
  intro h
  have dr := root_bounds
  have square (v : Q5) : (v*r5)*(v*r5) = 5*v*v := by have := r5_sq; grind
  have sq := square (y:Q5)
  have strict {a b : Q5} (ha : 0 ≤ a) (hab : a < b) : a*a < b*b := by
    have := OrderedRing.mul_le_mul_of_nonneg_left (Std.le_of_lt hab) ha
    have := OrderedRing.mul_lt_mul_of_pos_right hab (show 0 < b by grind)
    grind
  by_cases hx : x < 0
  · refine Or.inl ⟨hx,?_⟩
    by_cases hy : 0 ≤ y
    · exact Or.inl hy
    · apply Or.inr
      have yn : (y:Q5) < 0 := cast_lt (by omega : y < 0)
      have yp := Q5.mul_lt yn (show 0 < r5 by grind)
      have := strict (show 0 ≤ -((y:Q5)*r5) by grind) (show -((y:Q5)*r5) < -(x:Q5) by grind)
      apply OrderedRing.lt_of_intCast_lt_intCast (R := Q5)
      simp only [Ring.intCast_mul]; grind
  · have xn : (0:Q5) ≤ (x:Q5) := cast_le (by omega : 0 ≤ x)
    have yp : 0 < y := by
      by_cases hn : y ≤ 0
      · have yy : (y:Q5) ≤ 0 := cast_le hn
        have := OrderedRing.mul_le_mul_of_nonneg_right yy (show 0 ≤ r5 by grind); grind
      · omega
    refine Or.inr ⟨by omega,yp,?_⟩
    have := strict xn h
    apply OrderedRing.lt_of_intCast_lt_intCast (R := Q5)
    simp only [Ring.intCast_mul]; grind

/-- Quadratic-intercept floor words inhabit the integer phase class in core Lean. -/
theorem quadratic_phase_goldenLine (θ : Q5) :
    GoldenLine (fun t => floor (θ+(t:Q5)*(r5-1))) := by
  intro s t
  apply (ltSqrt5_iff _ _).mpr
  simp only [Ring.intCast_add,Ring.intCast_sub,Ring.intCast_one,Ring.intCast_natCast]
  have := floor_spec (θ+(s:Q5)*(r5-1))
  have := floor_spec (θ+(t:Q5)*(r5-1)); grind

private theorem finite_max (g : Nat → Q5) (n : Nat) :
    ∃ j ≤ n, ∀ t ≤ n, g t ≤ g j := by
  induction n with
  | zero =>
    refine ⟨0,by omega,fun t ht => ?_⟩
    rw [Nat.eq_zero_of_le_zero ht]
    exact Std.le_refl _
  | succ n ih =>
    obtain ⟨j,hj,hm⟩ := ih
    by_cases h : g (n+1) ≤ g j
    · refine ⟨j,by omega,fun t ht => ?_⟩
      by_cases k : t=n+1
      · simpa [k] using h
      · exact hm t (by omega)
    · refine ⟨n+1,by omega,fun t ht => ?_⟩
      by_cases k : t=n+1
      · subst t; grind
      · have := hm t (by omega); grind

/-- On each finite window, the largest lower endpoint is an admissible intercept. -/
theorem finite_phase (f : Nat → Int) (hf : GoldenLine f) (N : Nat) :
    ∃ θ : Q5, ∀ t ≤ N, floor (θ+(t:Q5)*(r5-1)) = f t := by
  let g (t : Nat) := (f t : Q5)-(t:Q5)*(r5-1)
  obtain ⟨j,_,hm⟩ := finite_max g N
  refine ⟨g j,fun t ht => floor_unique _ _ ?_⟩
  have lower := hm t ht
  have upper := lt_root (hf j t)
  simp only [Ring.intCast_add,Ring.intCast_sub,Ring.intCast_one,Ring.intCast_natCast] at upper
  dsimp only [g] at lower ⊢; grind

/-- The six candidate integer lags at the nth power of 9 + 4√5. -/
def scaleLags (n : Nat) : List Nat := families.map fun e => (shrink (unitAt n)*e).b.toNat

/-- At every scale from three, one of six lags has inclusive excess at least
(999/10000)q − 3 for the parity of any golden line. -/
theorem golden_repeats_at_scale (f : Nat → Int) (hf : GoldenLine f) (n : Nat) (hn : 3 ≤ n) :
    ∃ q ∈ scaleLags n, ∃ a b : Nat, n < q ∧ a ≤ b ∧
      10999*q+20000*a ≤ 10000*b+30000 ∧
      ∀ t : Nat, a ≤ t → t ≤ b → f t % 2 = f (t+q) % 2 := by
  have big (k : Nat) : 1000 ≤ (unitAt (3+k)).A := by
    induction k with
    | zero => decide
    | succ k ih =>
      change 1000 ≤ 9*(unitAt (3+k)).A+20*(unitAt (3+k)).B
      have := (unitAt (3+k)).Bnonneg; omega
  have hu : 1000 ≤ (unitAt n).A := by simpa only [show 3+(n-3)=n by omega] using big (n-3)
  obtain ⟨θ,hθ⟩ := finite_phase f hf (horizon (unitAt n))
  obtain ⟨a,b,q,⟨e,he,hqe⟩,hq,hend,hlen,hw⟩ := run (config (unitAt n) θ) hu
  have hg := large n
  refine ⟨q,List.mem_map.mpr ⟨e,he,hqe.symm⟩,a,b,by omega,by omega,hlen,?_⟩
  intro t ha hb
  have same := hw t ha hb
  unfold word at same
  rw [hθ t (by omega),hθ (t+q) (by omega)] at same
  by_cases h : f t % 2 = 1 <;> simp [h] at same <;> omega

/-- Arbitrarily large repetition excess survives every finite warm-up. -/
theorem unbounded_golden_repeats (f : Nat → Int) (hf : GoldenLine f) (H K : Nat) :
    ∃ a b q : Nat, H ≤ a ∧ K < q ∧ 2*a+q+K < b ∧
      ∀ t : Nat, a ≤ t → t ≤ b → f t % 2 = f (t+q) % 2 := by
  let n := 20*(K+2*H+3)+3
  obtain ⟨q,_,a,b,hq,_,hlen,hs⟩ := golden_repeats_at_scale f hf n (by dsimp [n]; omega)
  dsimp only [n] at hq
  exact ⟨a+H,b,q,by omega,by omega,by omega,fun t ht hb => hs t (by omega) hb⟩

open Rule30Realization

/-- An eventual period-two clock excludes every golden half-circle phase as the
eventual even-time right neighbour of a row with a leftmost black cell. -/
theorem no_eventual_golden_neighbour (x : Int → Bool) (L T H : Nat) (f : Nat → Int) (hf : GoldenLine f)
    (hleft : x (-(L:Int)) = true) (hzero : ∀ j, j < -(L:Int) → x j = false)
    (clock : ∀ t, T ≤ t → evol x t 0 = decide (t%2 = 1))
    (visible : ∀ t, H ≤ t → evol x (2*t) 1 = decide (f t % 2 = 1)) : False := by
  obtain ⟨a,b,q,ha,hq,hb,agree⟩ := unbounded_golden_repeats f hf (H+T) L
  let m := L+2*(a+q)
  have clocks (i s : Nat) (hi : a ≤ i) : evol x (2*i+s) 0 = decide (s%2 = 1) := by
    rw [clock _ (by omega), show (2*i+s)%2 = s%2 by omega]
  apply Rule30FiniteMaskedJen.window_jen_col hleft hzero (i := 0) (t₁ := 2*a) (t₂ := 2*(a+q))
    m (by omega) (by dsimp [m]; omega)
  · intro s _
    rw [clocks a s (by omega),clocks (a+q) s (by omega)]
  · intro s hs
    unfold Rule30FiniteMaskedJen.orCol
    rw [clocks a s (by omega),clocks (a+q) s (by omega)]
    by_cases hodd : s%2 = 1
    · simp [hodd]
    · simp only [hodd,decide_false,Bool.false_or]
      have h₁ : 2*a+s = 2*(a+s/2) := by omega
      have h₂ : 2*(a+q)+s = 2*((a+s/2)+q) := by omega
      change evol x (2*a+s) 1 = evol x (2*(a+q)+s) 1
      rw [h₁,h₂,visible _ (by omega),visible _ (by omega),agree _ (by omega) (by dsimp [m] at hs; omega)]

end Ruliology.CellularAutomata.Rule30GoldenHalfCircle
