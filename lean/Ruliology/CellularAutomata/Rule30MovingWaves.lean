module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30RingOrbits
public import Ruliology.CellularAutomata.Rule30MovingStrip
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn01
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn02
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn03
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn04
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn05
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn06
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn07
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn08
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn09
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn10
public import Ruliology.CellularAutomata.Rule30Certificates.MovingReturn11

/-!
# Rule 30: Minimum Rightward Light-Speed Return with Exponential Spatial Language

In the co-moving frame moving one cell right per time step (`Rule30RingOrbits.Phi`),
a bi-infinite row `x : Int → Bool` is a travelling return of period `P` if `orbit x P = x`.
By `Rule30RingOrbits.orbit_eq_iff`, this means that after `P` updates of Rule 30, the configuration
returns exactly to itself shifted `P` cells to the right:
`evol x P (i + P) = x i`.

This module establishes that **twelve** is the exact minimum return period `P ≥ 1` admitting
exponential spatial language complexity (positive spatial entropy).

### 1. Zero Spatial Entropy Below 12 (Linear Word Growth)
For every return period `1 ≤ P ≤ 11` and every word length `m`, the number of distinct spatial
words appearing in configurations with `orbit x P = x` is bounded by `81 + 14 * m`:
`low_period_linear_words (P : Nat) (h1 : 1 ≤ P) (h11 : P ≤ 11) (m : Nat) :
  ∃ L : List (List Bool), L.length ≤ 81 + m * 14 ∧
    ∀ (x : Int → Bool), orbit x P = x → ∀ origin : Int, rowWord x origin m ∈ L`
Since the growth of word counts is linear, the spatial topological entropy `h_P` is zero.
The bounds are certified by SAT/RUP refutations on strip relaxations, replayed by the Lean kernel.

### 2. Positive Spatial Entropy at Period 12 (Free Binary Shift)
At period 12, two explicit 34-cell profile tiles can be freely concatenated along the bi-infinite
lattice without any boundary defect:
* `free_binary_period_twelve`: an injective encoding `E : (Int → Bool) → (Int → Bool)` such that
  every coded configuration has exact minimal return period 12.
* `exponential_marked_rings`: an injective family of `2^k` distinct marked periodic rings of size
  `34 * k` for every `k ≥ 1`, all of exact minimal return period 12.
* `exponential_words_twelve`: an injective encoding of all `(n / 34)`-bit binary sequences into
  distinct length-`n` spatial words occurring in moving-period-12 configurations.

### 3. Exact Minimum
Combining the linear obstruction for `1 ≤ P ≤ 11` with the exponential construction at `P = 12`,
12 is the least positive integer `P` whose spatial language grows exponentially.

-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30MovingWaves

open Ruliology.CellularAutomata
open Rule30Realization Rule30RingOrbits Rule30MovingStrip

set_option linter.all false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-! ### Low periods 1..11: Certified Linear Word Growth -/

theorem low_period_linear_words (P : Nat) (h1 : 1 ≤ P) (h11 : P ≤ 11) (m : Nat) :
    ∃ L : List (List Bool),
      L.length ≤ 81 + m * 14 ∧
      ∀ (x : Int → Bool), orbit x P = x → ∀ origin : Int, rowWord x origin m ∈ L := by
  have hcases : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6 ∨
      P = 7 ∨ P = 8 ∨ P = 9 ∨ P = 10 ∨ P = 11 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rule30Certificates.MovingReturn01.linear_words m
  · exact Rule30Certificates.MovingReturn02.linear_words m
  · exact Rule30Certificates.MovingReturn03.linear_words m
  · exact Rule30Certificates.MovingReturn04.linear_words m
  · exact Rule30Certificates.MovingReturn05.linear_words m
  · exact Rule30Certificates.MovingReturn06.linear_words m
  · exact Rule30Certificates.MovingReturn07.linear_words m
  · exact Rule30Certificates.MovingReturn08.linear_words m
  · exact Rule30Certificates.MovingReturn09.linear_words m
  · exact Rule30Certificates.MovingReturn10.linear_words m
  · exact Rule30Certificates.MovingReturn11.linear_words m

/-! ### Period 12: Travelling Tiles, Binary Codes, and Exponential Words -/

namespace TravellingCode
open Ruliology.CellularAutomata
open Rule30Realization Rule30RingOrbits

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def zeroProfiles : List Nat :=
  [2868,3242,2734,2769,1321,1721,2469,1381,1367,2772,3372,2738,
   2986,1131,2644,3674,2406,2389,1493,1323,2868,3242,2734,2769,
   1321,1721,2469,1381,1367,3028,3116,2610,2602,1323]

def oneProfiles : List Nat :=
  [2868,3242,2734,2769,1321,1721,2469,1381,1367,3028,3116,2610,
   2602,1323,2868,3242,2734,2769,1321,1721,2469,1381,1367,2772,
   3372,2738,2986,1131,2644,3674,2406,2389,1493,1323]

def profile (b : Bool) (r t : Nat) : Bool :=
  ((if b then oneProfiles else zeroProfiles).getD r 0).testBit (t%12)

def joined (a b : Bool) (r t : Nat) : Bool :=
  if r<34 then profile a r t else profile b (r-34) t

/-- All four seams, all 34 offsets and all 12 time phases: 1632 exact
local Rule 30 identities, checked by the Lean kernel. -/
theorem tile_certificate : ∀ a b : Bool, ∀ r : Fin 34, ∀ t : Fin 12,
    profile a r.val (t.val+1) =
      xor (joined a b r.val t.val)
        (joined a b (r.val+1) t.val || joined a b (r.val+2) t.val) := by
  decide +kernel

theorem profile_mod (b : Bool) (r t : Nat) :
    profile b r (t%12) = profile b r t := by
  simp only [profile, Nat.mod_mod]

theorem joined_mod (a b : Bool) (r t : Nat) :
    joined a b r (t%12) = joined a b r t := by
  simp only [joined, profile_mod]

theorem profile_succ_mod (b : Bool) (r t : Nat) :
    profile b r (t%12+1) = profile b r (t+1) := by
  have hh : (t%12+1)%12 = (t+1)%12 := by omega
  simp only [profile, hh]

/-- Spatial sites are labelled by Int, so this permits arbitrary code
in BOTH directions, rather than only finite or periodic code words. -/
def field (code : Int → Bool) (t : Nat) (i : Int) : Bool :=
  profile (code (i/34)) (i%34).toNat t

theorem field_local (code : Int → Bool) (t : Nat) (i : Int)
    (d : Nat) (hd : d≤2) :
    field code t (i+(d : Int)) =
      joined (code (i/34)) (code (i/34+1)) ((i%34).toNat+d) t := by
  have h0 : 0 ≤ i % 34 := by omega
  have h1 : i%34<34 := by omega
  have hc : ((i%34).toNat : Int) = i%34 := by omega
  by_cases h : (i%34).toNat+d<34
  · have hq : (i+(d : Int))/34 = i/34 := by omega
    have hr : ((i+(d : Int))%34).toNat = (i%34).toNat+d := by omega
    simp only [field,hq,hr,joined,ite_eq_left h]
  · have hq : (i+(d : Int))/34 = i/34+1 := by omega
    have hr : ((i+(d : Int))%34).toNat = (i%34).toNat+d-34 := by omega
    simp only [field,hq,hr,joined,ite_eq_right h]

theorem phi_field (code : Int → Bool) (t : Nat) :
    Phi (field code t) = field code (t+1) := by
  funext i
  have hr : (i%34).toNat<34 := by omega
  have hc := tile_certificate (code (i/34)) (code (i/34+1))
    ⟨(i%34).toNat,hr⟩ ⟨t%12,by omega⟩
  dsimp only at hc
  simp only [profile_succ_mod,joined_mod] at hc
  have h0 := field_local code t i 0 (by decide)
  have h1 : field code t (i+1) =
      joined (code (i/34)) (code (i/34+1)) ((i%34).toNat+1) t := by
    simpa using field_local code t i 1 (by decide)
  have h2 : field code t (i+2) =
      joined (code (i/34)) (code (i/34+1)) ((i%34).toNat+2) t := by
    simpa using field_local code t i 2 (by decide)
  simp only [Int.ofNat_zero,Int.add_zero,Nat.add_zero] at h0
  change xor (field code t i) (field code t (i+1) || field code t (i+2)) = _
  rw [h0,h1,h2]
  exact hc.symm

theorem orbit_field (code : Int → Bool) : ∀ t : Nat,
    orbit (field code 0) t = field code t
  | 0 => rfl
  | t+1 => by rw [orbit,orbit_field code t,phi_field]

theorem field_period (code : Int → Bool) (t : Nat) :
    field code (t+12) = field code t := by
  funext i
  simp [field,profile]

/-- The central uniform result: every bi-infinite binary code is a
right light-speed wave with co-moving return after 12 steps. -/
theorem period_twelve (code : Int → Bool) :
    orbit (field code 0) 12 = field code 0 := by
  rw [orbit_field,show 12=0+12 by rfl,field_period]

theorem genuine_rule30_wave (code : Int → Bool) (i : Int) :
    evol (field code 0) 12 (i+12) = field code 0 i :=
  (orbit_eq_iff (field code 0) 12).mp (period_twelve code) i

theorem physical_wave_all_times (code : Int → Bool) (t : Nat) (i : Int) :
    evol (field code 0) (t+12) (i+12) = evol (field code 0) t i := by
  have h0 : (i-(t : Int))+((t+12 : Nat) : Int)=i+12 := by omega
  have h1 : (i-(t : Int))+(t : Int)=i := by omega
  calc
    evol (field code 0) (t+12) (i+12) = orbit (field code 0) (t+12) (i-t) := by
      rw [orbit_evol,h0]
    _ = field code (t+12) (i-t) := congrFun (orbit_field code (t+12)) _
    _ = field code t (i-t) := congrFun (field_period code t) _
    _ = orbit (field code 0) t (i-t) := (congrFun (orbit_field code t) _).symm
    _ = evol (field code 0) t i := by rw [orbit_evol,h1]

theorem tile_least_return : ∀ a : Bool, ∀ d : Fin 12, d.val≠0 →
    ∃ r : Fin 34, profile a r.val d.val ≠ profile a r.val 0 := by
  decide +kernel

/-- The return period is exactly 12, not merely a divisor of 12. -/
theorem exact_period_twelve (code : Int → Bool) :
    orbit (field code 0) 12=field code 0 ∧
    ∀ d : Nat, 0<d → d<12 → orbit (field code 0) d≠field code 0 := by
  refine ⟨period_twelve code,?_⟩
  intro d hd hd12 he
  obtain ⟨r,hr⟩ := tile_least_return (code 0) ⟨d,hd12⟩ (by
    change d≠0
    exact Nat.ne_of_gt hd)
  have hh := congrFun he (r.val : Int)
  rw [orbit_field] at hh
  have hq : (r.val : Int)/34=0 := by omega
  have hm : (r.val : Int)%34=r.val := by omega
  simp only [field,hq,hm,Int.toNat_natCast] at hh
  exact hr hh

/-- One bit at offset 20 decodes the symbol of every 34-cell tile. -/
theorem decode (code : Int → Bool) (q : Int) :
    field code 0 (34*q+20) = code q := by
  have hq : (34*q+20)/34=q := by omega
  have hr : (34*q+20)%34=20 := by omega
  simp only [field,hq,hr]
  cases code q <;> decide

theorem code_injective (a b : Int → Bool)
    (h : field a 0 = field b 0) : a=b := by
  funext q
  have hh := congrFun h (34*q+20)
  simpa only [decode] using hh

/-- The coding commutes with a 34-site spatial shift. Together with the
decoder, this explicitly embeds a full binary shift at scale 34. -/
theorem block_shift (code : Int → Bool) (t : Nat) (i : Int) :
    field code t (i+34) = field (fun q => code (q+1)) t i := by
  have hq : (i+34)/34=i/34+1 := by omega
  have hr : (i+34)%34=i%34 := by omega
  simp only [field,hq,hr]

def periodicCode (k : Nat) (hk : 0<k) (w : Fin k → Bool) (q : Int) : Bool :=
  w ⟨(q%(k : Int)).toNat,by
    have h0 : 0≤q%(k : Int) := Int.emod_nonneg _ (by omega)
    have h1 : q%(k : Int)<k := Int.emod_lt_of_pos _ (by omega)
    omega⟩

theorem periodicCode_period (k : Nat) (hk : 0<k) (w : Fin k → Bool) (q : Int) :
    periodicCode k hk w (q+k) = periodicCode k hk w q := by
  simp [periodicCode]

theorem periodicCode_read (k : Nat) (hk : 0<k) (w : Fin k → Bool) (j : Fin k) :
    periodicCode k hk w j.val = w j := by
  have hh : (j.val : Int)%(k : Int) = j.val :=
    Int.emod_eq_of_lt (by omega) (by omega)
  simp only [periodicCode,hh,Int.toNat_natCast]

theorem ring_period (k : Nat) (hk : 0<k) (w : Fin k → Bool) :
    Per (34*k) (field (periodicCode k hk w) 0) := by
  intro i
  have hq : (i+((34*k : Nat) : Int))/34=i/34+k := by omega
  have hr : (i+((34*k : Nat) : Int))%34=i%34 := by omega
  simp only [field,hq,hr,periodicCode_period]

/-- At least 2^k different marked rings of size 34k return after 12
co-moving steps. The finite-word domain and injectivity state the bound
without importing a cardinality or real-analysis library. -/
theorem exponential_ring_family (k : Nat) (hk : 0<k) :
    ∃ E : (Fin k → Bool) → (Int → Bool),
      (∀ u v, E u=E v → u=v) ∧
      ∀ w, Per (34*k) (E w) ∧ orbit (E w) 12=E w ∧
        (∀ d : Nat, 0<d → d<12 → orbit (E w) d≠E w) := by
  let E := fun w => field (periodicCode k hk w) 0
  refine ⟨E,?_,fun w => ⟨ring_period k hk w,exact_period_twelve _⟩⟩
  intro u v h
  have hc := code_injective (periodicCode k hk u) (periodicCode k hk v) h
  funext j
  have hh := congrFun hc j.val
  simpa only [periodicCode_read] using hh

def marker (q : Int) : Bool := decide (q=0)

/-- A localized defect in a periodic background: it returns in the moving
frame but has no positive spatial period. -/
theorem marker_spatially_aperiodic (m : Nat) (hm : 0<m) :
    ¬ Per m (field marker 0) := by
  intro hp
  have hh := per_add_mul hp 20 34
  have hleft : (20 : Int)+((34*m : Nat) : Int)=34*(m : Int)+20 := by omega
  rw [hleft,decode,show (20 : Int)=34*0+20 by omega,decode] at hh
  simp [marker] at hh
  omega

theorem aperiodic_travelling_wave :
    ∃ x : Int → Bool, orbit x 12=x ∧
      (∀ m : Nat, 0<m → ¬ Per m x) :=
  ⟨field marker 0,period_twelve marker,marker_spatially_aperiodic⟩

end TravellingCode

/-- Extend a finite word `u : Fin k → Bool` by `false` outside `0 ≤ q < k`. -/
def codeOfFin (k : Nat) (u : Fin k → Bool) (q : Int) : Bool :=
  if h : 0 ≤ q ∧ q.toNat < k then u ⟨q.toNat, h.2⟩ else false

theorem codeOfFin_read (k : Nat) (u : Fin k → Bool) (j : Fin k) :
    codeOfFin k u (j.val : Int) = u j := by
  have h1 : 0 ≤ (j.val : Int) := Int.natCast_nonneg j.val
  have h2 : (j.val : Int).toNat < k := by
    rw [Int.toNat_natCast]
    exact j.isLt
  simp [codeOfFin, h1, j.isLt]

/-- The prefix of length `n` of the period-12 configuration encoding `u : Fin (n / 34) → Bool`. -/
def word12OfFin (n : Nat) (u : Fin (n / 34) → Bool) : Fin n → Bool :=
  fun i : Fin n => TravellingCode.field (codeOfFin (n / 34) u) 0 (i.val : Int)

theorem word12OfFin_injective (n : Nat) :
    Function.Injective (word12OfFin n) := by
  intro u v h
  funext j
  have hj : 34 * j.val + 20 < n := by
    have := j.isLt
    omega
  have hval := congrFun h ⟨34 * j.val + 20, hj⟩
  dsimp only [word12OfFin] at hval
  have hcast : ((34 * j.val + 20 : Nat) : Int) = 34 * (j.val : Int) + 20 := by omega
  rw [hcast, TravellingCode.decode, TravellingCode.decode,
    codeOfFin_read, codeOfFin_read] at hval
  exact hval

/-- A free bi-infinite binary code, every image of least moving period twelve. -/
theorem free_binary_period_twelve :
    ∃ E : (Int → Bool) → (Int → Bool),
      (∀ a b, E a = E b → a = b) ∧
      ∀ code, orbit (E code) 12 = E code ∧
        (∀ d : Nat, 0 < d → d < 12 → orbit (E code) d ≠ E code) := by
  refine ⟨fun code => TravellingCode.field code 0, ?_, ?_⟩
  · exact TravellingCode.code_injective
  · exact TravellingCode.exact_period_twelve

/-- An injective family indexed by every k-bit word on marked rings of size 34k. -/
theorem exponential_marked_rings (k : Nat) (hk : 0 < k) :
    ∃ E : (Fin k → Bool) → (Int → Bool),
      (∀ u v, E u = E v → u = v) ∧
      ∀ w, Per (34*k) (E w) ∧ orbit (E w) 12 = E w ∧
        (∀ d : Nat, 0 < d → d < 12 → orbit (E w) d ≠ E w) :=
  TravellingCode.exponential_ring_family k hk

/-- For every `n`, there is an injective encoding of `(n / 34)`-bit binary sequences into spatial words
of length `n` that occur in moving-period-12 configurations. -/
theorem exponential_words_twelve (n : Nat) :
    ∃ (word : (Fin (n / 34) → Bool) → (Fin n → Bool)),
      Function.Injective word ∧
      ∀ u, ∃ (x : Int → Bool), orbit x 12 = x ∧
        ∀ j : Fin n, word u j = x (j.val : Int) := by
  refine ⟨word12OfFin n, word12OfFin_injective n, ?_⟩
  intro u
  refine ⟨TravellingCode.field (codeOfFin (n / 34) u) 0, TravellingCode.period_twelve _, ?_⟩
  intro j
  rfl

/-- The exact minimum theorem: every moving return `1 ≤ P ≤ 11` has certified linear spatial word count
growth `≤ 81 + 14 * m`, whereas return 12 achieves exponential spatial words `≥ 2 ^ ⌊n / 34⌋`. -/
theorem minimum_exponential_period_twelve :
    (∀ P, 1 ≤ P → P ≤ 11 →
      ∀ m, ∃ L : List (List Bool), L.length ≤ 81 + m * 14 ∧
        ∀ x, orbit x P = x → ∀ origin, rowWord x origin m ∈ L) ∧
    (∀ n, ∃ (word : (Fin (n / 34) → Bool) → (Fin n → Bool)),
      Function.Injective word ∧
      ∀ u, ∃ x, orbit x 12 = x ∧ ∀ j : Fin n, word u j = x (j.val : Int)) :=
  ⟨low_period_linear_words, exponential_words_twelve⟩

end Ruliology.CellularAutomata.Rule30MovingWaves
