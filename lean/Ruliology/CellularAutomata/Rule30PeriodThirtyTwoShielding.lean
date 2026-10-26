module

public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks0
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks1
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks2
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks3
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks4
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks5
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks6
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks7
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks8
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks9
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks10
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks11
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks12
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks13
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks14
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks15
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks16
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks17
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks18
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks19
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks20
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks21
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks22
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks23
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks24
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks25
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks26
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks27
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks28
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks29
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks30
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks31
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks32
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoChecks33
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoDetection

/-!
# Period-32 shielding rigidity

This partial result concerns finite-support right-triangular Rule 30 states.
If such a state returns after 32 steps and satisfies the stated alternating
two-phase shielding gates, then its complete state already returns after two
steps.  The equivalent numerical moving-front state is consequently one of
the canonical finite stripe integers.

The proof uses the existing Rule30FiniteClockCertificate machinery for
finite-width coverage and shorter-clock propagation.  The contribution here
is the 2,116-node period-32 certificate in 67 closure blocks, its gate check,
the period-32-to-period-two application, and the canonical stripe bridge via
the verified 14-state period-two classifier.  It is a partial result related
to Problem 1, not a proof of Problem 1 or any other prize problem.

A triangular state is the right half of an ordinary Rule 30 configuration
(`Rule30Realization.evol`) read in the frame that moves right one cell per step
(`controlled_iterate_eq_evol`). The integer map `T n = n ^^^ ((n >>> 1) ||| (n >>> 2))`
is the same map on the bits of `n` (`official_integer_iterate`,
`integer_iterate_eq_evol`), so `iterate 32 n = n` says that this right half
reappears after 32 steps translated 32 cells (`integer_return_iff_evol`).

The pool is in `Rule30Certificates/PeriodThirtyTwoPool`. Its 134 kernel checks
(closure and gate for each of the 67 blocks) are split two blocks per module over
`Rule30Certificates/PeriodThirtyTwoChecks0`–`33`, so that each module builds in
under a minute; the whole-pool detection check is
`Rule30Certificates/PeriodThirtyTwoDetection`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding

open Ruliology.CellularAutomata
open Rule30FiniteClockCertificate
open Certificate
def T (x : Nat) : Nat := x ^^^ ((x >>> 1) ||| (x >>> 2))

def iterate : Nat → Nat → Nat
  | 0, x => x
  | p+1, x => iterate p (T x)

def dfaStep (a : Nat) (b : Bool) : Nat :=
  match a, b with
  | 0, false => 7 | 0, true => 1
  | 1, false => 2 | 1, true => 3
  | 2, false => 7 | 2, true => 4
  | 3, false => 5 | 3, true => 7
  | 4, false => 2 | 4, true => 7
  | 5, false => 7 | 5, true => 6
  | 6, false => 5 | 6, true => 7
  | _, _ => 7

def dfaAccept (a : Nat) : Bool := a == 1 || a == 2 || a == 5

def edge (p s : Nat) (b : Bool) : Option Nat := Id.run do
  let base := 2 ^ (2*p)
  let suffix := s % base
  let a := s / base
  if iterate p (2*suffix) % 2 != 0 then return none
  if a == 0 && !b then return none
  let newSuffix := (2*suffix+b.toNat) % base
  return some (newSuffix + base*dfaStep a b)

def gates : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | t+1, x, phase =>
    (if phase % 2 == 0 then x % 4 != 0 else x % 2 != 0) &&
      gates t (T x) (phase+1)

def good (p s : Nat) : Bool :=
  let base := 2^(2*p)
  !(gates p (s%base) 0) || dfaAccept (s/base)

def checkCert (p : Nat) (states : List Nat) : Bool :=
  states.contains 0 && states.all (fun s =>
    good p s && (([false,true] : List Bool).all (fun b =>
      match edge p s b with
      | none => true
      | some nxt => states.contains nxt)))

def states2 : List Nat := [
  0, 17, 34, 42, 51, 69, 86, 90, 101, 109, 116, 119,
  123, 124
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- Checked finite-state closure for period 2. -/
theorem certificate_2 : checkCert 2 states2 = true := by
  decide

def states4 : List Nat := [
  0, 257, 514, 522, 554, 682, 771, 1029, 1045, 1109, 1286, 1306,
  1386, 1450, 1549, 1589, 1621, 1749, 1796, 1799, 1800, 1801, 1803, 1804,
  1806, 1807, 1812, 1814, 1815, 1816, 1817, 1819, 1832, 1833, 1835, 1844,
  1846, 1847, 1876, 1878, 1879, 1896, 1897, 1899, 1960, 1961, 1963, 2004,
  2006, 2007
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- Checked finite-state closure for period 4. -/
theorem certificate_4 : checkCert 4 states4 = true := by
  decide

def states8 : List Nat := [
  0, 65537, 131074, 131082, 131114, 131242, 131754, 133802, 141994, 174762, 196611, 262149,
  262165, 262229, 262485, 263509, 267605, 283989, 327686, 327706, 327786, 328106, 329386, 334506,
  354986, 371370, 393229, 393269, 393429, 394069, 396629, 406869, 415061, 447829, 458756, 458759,
  458760, 458761, 458763, 458764, 458766, 458767, 458768, 458769, 458770, 458771, 458772, 458774,
  458775, 458776, 458777, 458779, 458780, 458781, 458782, 458783, 458784, 458785, 458786, 458787,
  458788, 458789, 458790, 458791, 458792, 458793, 458795, 458796, 458797, 458798, 458799, 458800,
  458801, 458802, 458803, 458804, 458806, 458807, 458808, 458809, 458810, 458811, 458812, 458813,
  458814, 458815, 458832, 458833, 458834, 458835, 458836, 458838, 458839, 458840, 458841, 458842,
  458843, 458844, 458845, 458846, 458847, 458848, 458849, 458850, 458851, 458852, 458853, 458854,
  458855, 458856, 458857, 458859, 458860, 458861, 458862, 458863, 458912, 458913, 458914, 458915,
  458916, 458917, 458918, 458919, 458920, 458921, 458923, 458924, 458925, 458926, 458927, 458960,
  458961, 458962, 458963, 458964, 458966, 458967, 458968, 458969, 458970, 458971, 458972, 458973,
  458974, 458975, 459088, 459089, 459090, 459091, 459092, 459094, 459095, 459096, 459097, 459098,
  459099, 459100, 459101, 459102, 459103, 459168, 459169, 459170, 459171, 459172, 459173, 459174,
  459175, 459176, 459177, 459179, 459180, 459181, 459182, 459183, 459424, 459425, 459426, 459427,
  459428, 459429, 459430, 459431, 459432, 459433, 459435, 459436, 459437, 459438, 459439, 459600,
  459601, 459602, 459603, 459604, 459606, 459607, 459608, 459609, 459610, 459611, 459612, 459613,
  459614, 459615, 460112, 460113, 460114, 460115, 460116, 460118, 460119, 460120, 460121, 460122,
  460123, 460124, 460125, 460126, 460127, 460448, 460449, 460450, 460451, 460452, 460453, 460454,
  460455, 460456, 460457, 460459, 460460, 460461, 460462, 460463, 461472, 461473, 461474, 461475,
  461476, 461477, 461478, 461479, 461480, 461481, 461483, 461484, 461485, 461486, 461487, 462160,
  462161, 462162, 462163, 462164, 462166, 462167, 462168, 462169, 462170, 462171, 462172, 462173,
  462174, 462175, 464208, 464209, 464210, 464211, 464212, 464214, 464215, 464216, 464217, 464218,
  464219, 464220, 464221, 464222, 464223, 465568, 465569, 465570, 465571, 465572, 465573, 465574,
  465575, 465576, 465577, 465579, 465580, 465581, 465582, 465583, 469664, 469665, 469666, 469667,
  469668, 469669, 469670, 469671, 469672, 469673, 469675, 469676, 469677, 469678, 469679, 472400,
  472401, 472402, 472403, 472404, 472406, 472407, 472408, 472409, 472410, 472411, 472412, 472413,
  472414, 472415, 480592, 480593, 480594, 480595, 480596, 480598, 480599, 480600, 480601, 480602,
  480603, 480604, 480605, 480606, 480607, 486048, 486049, 486050, 486051, 486052, 486053, 486054,
  486055, 486056, 486057, 486059, 486060, 486061, 486062, 486063, 502432, 502433, 502434, 502435,
  502436, 502437, 502438, 502439, 502440, 502441, 502443, 502444, 502445, 502446, 502447, 513360,
  513361, 513362, 513363, 513364, 513366, 513367, 513368, 513369, 513370, 513371, 513372, 513373,
  513374, 513375
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
/-- Checked finite-state closure for period 8. -/
theorem certificate_8 : checkCert 8 states8 = true := by
  decide

/-- The graph reader consumes a finite word from its highest occupied
position toward position one. Reaching a state is independent of word length. -/
def walkFrom (p : Nat) (s : Nat) : List Bool → Option Nat
  | [] => some s
  | b::bs =>
      match edge p s b with
      | none => none
      | some nxt => walkFrom p nxt bs

/-- For any checked closed state set, paths of arbitrary length stay inside
the certified set; successful paths ending with good gates must be accepted. -/
theorem certified_all_words (p : Nat) (S : List Nat)
    (hcert : checkCert p S = true)
    (bits : List Bool) (result : Nat)
    (hwalk : walkFrom p 0 bits = some result) :
    good p result = true := by
  have hstart : 0 ∈ S := by
    have hs := (Bool.and_eq_true_iff.mp hcert).1
    simpa using hs
  have hrows : S.all (fun s =>
    good p s && (([false,true] : List Bool).all (fun b =>
      match edge p s b with
      | none => true
      | some nxt => S.contains nxt))) = true :=
    (Bool.and_eq_true_iff.mp hcert).2
  have hrow : ∀ s, s ∈ S →
      good p s && (([false,true] : List Bool).all (fun b =>
        match edge p s b with
        | none => true
        | some nxt => S.contains nxt)) = true := by
    intro s hs
    exact (List.all_eq_true.mp hrows) s hs
  have hgood : ∀ s, s ∈ S → good p s = true := by
    intro s hs
    exact (Bool.and_eq_true_iff.mp (hrow s hs)).1
  have hclosed : ∀ s, s ∈ S → ∀ b : Bool, ∀ nxt : Nat,
      edge p s b = some nxt → nxt ∈ S := by
    intro s hs b nxt hedge
    have hall := (Bool.and_eq_true_iff.mp (hrow s hs)).2
    have hb : (match edge p s b with
      | none => true
      | some nxt => S.contains nxt) = true := by
      exact (List.all_eq_true.mp hall) b (by cases b <;> simp)
    rw [hedge] at hb
    simpa using hb
  have hkeep : ∀ xs : List Bool, ∀ s : Nat, s ∈ S →
      ∀ nxt : Nat, walkFrom p s xs = some nxt → nxt ∈ S := by
    intro xs
    induction xs with
    | nil =>
        intro s hs nxt h
        have heq : s = nxt := by simpa [walkFrom] using h
        simpa [heq] using hs
    | cons b bs ih =>
        intro s hs nxt h
        cases he : edge p s b with
        | none => simp [walkFrom, he] at h
        | some s' =>
            have hs' := hclosed s hs b s' he
            apply ih s' hs' nxt
            simpa [walkFrom, he] using h
  exact hgood result (hkeep bits 0 hstart result hwalk)

/-- A genuinely all-word consequence of the checked temporal period 2 graph. -/
theorem certificate_2_all_words (bits : List Bool) (result : Nat)
    (h : walkFrom 2 0 bits = some result) : good 2 result = true :=
  certified_all_words 2 states2 certificate_2 bits result h

/-- The corresponding unbounded-word graph theorem at period 4. -/
theorem certificate_4_all_words (bits : List Bool) (result : Nat)
    (h : walkFrom 4 0 bits = some result) : good 4 result = true :=
  certified_all_words 4 states4 certificate_4 bits result h

/-- The corresponding unbounded-word graph theorem at period 8. -/
theorem certificate_8_all_words (bits : List Bool) (result : Nat)
    (h : walkFrom 8 0 bits = some result) : good 8 result = true :=
  certified_all_words 8 states8 certificate_8 bits result h

/-- Bit-for-bit identification of the finite integer transformer with
the infinite right-moving Boolean profile used by Rule 30. -/
theorem T_testBit (n k : Nat) :
    (T n).testBit k =
      xor (n.testBit k) (n.testBit (k+1) || n.testBit (k+2)) := by
  simp only [T, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
  rw [Nat.add_comm 1 k, Nat.add_comm 2 k]


/-- The Boolean cellular-automaton version of the same triangular map. -/
def frontStep (v : Nat → Bool) (k : Nat) : Bool :=
  xor (v k) (v (k+1) || v (k+2))

def frontRun : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, v => v
  | p+1, v => frontRun p (frontStep v)

/-- The integer executable and abstract Boolean cellular dynamics agree
at all times and sites, not merely at the gate positions. -/
theorem iterate_testBit (p n : Nat) :
    (fun k => (iterate p n).testBit k) =
      frontRun p (fun k => n.testBit k) := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih =>
      change (fun k => (iterate p (T n)).testBit k) =
        frontRun p (frontStep (fun k => n.testBit k))
      rw [ih (T n)]
      congr 1
      funext k
      exact T_testBit n k

/-- A time-p head observation only depends on its first 2p+1
initial spatial bits. This is the finite light-cone soundness lemma. -/
theorem frontRun_local (p : Nat) (u v : Nat → Bool)
    (h : ∀ k, k ≤ 2*p → u k = v k) :
    frontRun p u 0 = frontRun p v 0 := by
  induction p generalizing u v with
  | zero => exact h 0 (by omega)
  | succ p ih =>
      change frontRun p (frontStep u) 0 = frontRun p (frontStep v) 0
      apply ih
      intro k hk
      unfold frontStep
      rw [h k (by omega), h (k+1) (by omega), h (k+2) (by omega)]


/-- Agreement of every cell beyond the head is preserved by the triangular
front step, irrespective of the two head values. -/
private theorem frontStep_tail_congr {u v : Nat → Bool}
    (h : ∀ k, 1 ≤ k → u k = v k) :
    ∀ k, 1 ≤ k → frontStep u k = frontStep v k := by
  intro k hk
  unfold frontStep
  rw [h k hk, h (k+1) (by omega), h (k+2) (by omega)]

/-- Changing only the current head bit changes its value by exactly the
same XOR at every later time. It cannot affect the driver from the tail. -/
theorem frontRun_head_difference (p : Nat) (u v : Nat → Bool)
    (h : ∀ k, 1 ≤ k → u k = v k) :
    xor (frontRun p u 0) (frontRun p v 0) = xor (u 0) (v 0) := by
  induction p generalizing u v with
  | zero => rfl
  | succ p ih =>
      change xor (frontRun p (frontStep u) 0)
        (frontRun p (frontStep v) 0) = _
      rw [ih (frontStep u) (frontStep v) (frontStep_tail_congr h)]
      have h1 := h 1 (by omega)
      have h2 := h 2 (by omega)
      unfold frontStep
      rw [h1, h2]
      cases hu : u 0 <;> cases hv : v 0 <;>
        cases hc : (v 1 || v 2) <;> simp_all


/-- A Boolean head cell attached to an arbitrary (possibly infinite) right tail. -/
def prependBit (b : Bool) (tail : Nat → Bool) : Nat → Bool
  | 0 => b
  | k+1 => tail k

/-- The effect of the initial head is exactly one permanent XOR bit:
    finite right tails do not enter this statement. -/
theorem frontRun_prepend_xor (p : Nat) (b : Bool) (tail : Nat → Bool) :
    frontRun p (prependBit b tail) 0 =
      xor b (frontRun p (prependBit false tail) 0) := by
  have h : ∀ k, 1 ≤ k →
      prependBit b tail k = prependBit false tail k := by
    intro k hk
    cases k with
    | zero => omega
    | succ k => rfl
  have hh := frontRun_head_difference p (prependBit b tail)
    (prependBit false tail) h
  change xor (frontRun p (prependBit b tail) 0)
      (frontRun p (prependBit false tail) 0) = xor b false at hh
  cases hb : b <;>
    cases h0 : frontRun p (prependBit false tail) 0 <;>
    cases h1 : frontRun p (prependBit b tail) 0 <;>
    simp_all

/-- At any fixed temporal period, the driver's head observation only
    depends on the next 2p right-tail bits, irrespective of the far tail. -/
theorem frontRun_prepend_truncate (p : Nat) (b : Bool)
    (tail : Nat → Bool) :
    frontRun p (prependBit b tail) 0 =
      frontRun p
        (prependBit b (fun k => if k < 2*p then tail k else false)) 0 := by
  apply frontRun_local
  intro k hk
  cases k with
  | zero => rfl
  | succ k =>
      have hsmall : k < 2*p := by omega
      simp [prependBit, hsmall]

/-- A newly inserted head returns after p updates exactly when the
    zero-head driver generated by the same suffix vanishes. -/
theorem frontRun_head_returns_iff (p : Nat) (b : Bool)
    (tail : Nat → Bool) :
    frontRun p (prependBit b tail) 0 = b ↔
      frontRun p (prependBit false tail) 0 = false := by
  rw [frontRun_prepend_xor]
  cases b <;> cases h : frontRun p (prependBit false tail) 0 <;> simp


/-- Appending a binary head to the left of a numerical right suffix agrees
exactly with the Boolean-profile cons constructor. -/
theorem prependNat_testBit (n : Nat) (b : Bool) :
    (fun k => (2*n + b.toNat).testBit k) =
      prependBit b (fun k => n.testBit k) := by
  funext k
  have hb : b.toNat < 2^1 := by cases b <;> decide
  have hh := Nat.testBit_two_pow_mul_add n (i := 1)
    (b := b.toNat) hb k
  cases k with
  | zero =>
      change (2*n + b.toNat).testBit 0 = b
      rw [show 2*n + b.toNat = 2^1*n + b.toNat by rfl]
      rw [Nat.testBit_two_pow_mul_add n hb 0]
      cases b <;> simp
  | succ k =>
      simpa [prependBit] using hh

/-- The zero-head driver is unchanged by deleting all suffix bits at
distance at least 2p, as required for an exact finite-state edge gate. -/
theorem frontRun_zero_suffix_mod (p n : Nat) :
    frontRun p (prependBit false (fun k => n.testBit k)) 0 =
    frontRun p
      (prependBit false (fun k => (n % 2^(2*p)).testBit k)) 0 := by
  apply frontRun_local
  intro k hk
  cases k with
  | zero => rfl
  | succ k =>
      have hlt : k < 2*p := by omega
      simp only [prependBit, Nat.testBit_mod_two_pow]
      simp [hlt]


/-- The least significant bit of the executable iterator is the abstract
moving-frame head. -/
theorem iterate_head_bit (p n : Nat) :
    (iterate p n).testBit 0 =
      frontRun p (fun k => n.testBit k) 0 :=
  congrFun (iterate_testBit p n) 0

/-- The exact edge predicate used by the suffix graph is equivalent to
returning the newly attached head bit after p Rule 30 front steps.
Crucially, this is a theorem for ALL suffix integers, not an enumeration. -/
theorem numerical_edge_iff_head_returns (p n : Nat) (b : Bool) :
    ((iterate p (2*n + b.toNat)).testBit 0 = b) ↔
      ((iterate p (2*(n % 2^(2*p)))).testBit 0 = false) := by
  rw [iterate_head_bit p (2*n + b.toNat)]
  rw [iterate_head_bit p (2*(n % 2^(2*p)))]
  rw [prependNat_testBit n b]
  have hz : 2*(n % 2^(2*p)) =
      2*(n % 2^(2*p)) + false.toNat := by simp
  rw [hz, prependNat_testBit (n % 2^(2*p)) false]
  have h := frontRun_head_returns_iff p b (fun k => n.testBit k)
  rw [frontRun_zero_suffix_mod] at h
  exact h

/-- The graph's integer guard (modulo two) is precisely the head-return
predicate. -/
theorem numerical_edge_guard (p n : Nat) (b : Bool) :
    ((iterate p (2*n + b.toNat)).testBit 0 = b) ↔
      iterate p (2*(n % 2^(2*p))) % 2 = 0 :=
  (numerical_edge_iff_head_returns p n b).trans
    (Nat.mod_two_eq_zero_iff_testBit_zero).symm


/-- Moving one spatial site toward the far right commutes with the
triangular Rule 30 front step. This is the exact engine for recursive
most-significant-bit-first word processing. -/
theorem T_div_two (n : Nat) : T (n/2) = (T n)/2 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [T_testBit, Nat.testBit_div_two]

/-- The spatial-shift commutation survives arbitrary temporal iteration. -/
theorem iterate_div_two (p n : Nat) :
    iterate p (n/2) = (iterate p n)/2 := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih =>
      change iterate p (T (n/2)) = (iterate p (T n))/2
      rw [T_div_two, ih]


/-- Triangular dynamics commute with arbitrary spatial right shifts,
not only a single divide-by-two step. -/
theorem T_shiftRight (n k : Nat) :
    T (n >>> k) = (T n) >>> k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Nat.shiftRight_succ_inside n k]
      rw [ih (n/2), T_div_two]
      rw [Nat.shiftRight_succ_inside (T n) k]

theorem iterate_shiftRight (p n k : Nat) :
    iterate p (n >>> k) = (iterate p n) >>> k := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih =>
      change iterate p (T (n >>> k)) =
        (iterate p (T n)) >>> k
      rw [T_shiftRight, ih]

/-- Every far-right suffix of a finite temporally periodic profile
inherits exactly the same temporal period. -/
theorem period_right_suffix (p n k : Nat)
    (hperiod : iterate p n = n) :
    iterate p (n >>> k) = n >>> k := by
  rw [iterate_shiftRight, hperiod]


/-- Read the finite spatial word from its most significant occupied cell
toward site one. Structural termination uses strict descent by div-two.
Unlike a bounded enumeration, this interpreter accepts arbitrary integers. -/
def readNumber (p : Nat) (n : Nat) : Option Nat :=
  if h : n = 0 then some 0
  else do
    let s ← readNumber p (n / 2)
    edge p s (n.testBit 0)
termination_by n
decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

theorem readNumber_zero (p : Nat) :
    readNumber p 0 = some 0 := by
  simp [readNumber]


/-- The certified graph bounds arbitrary-width *binary integers* read
most-significant bit first, not only already-packaged bit lists. -/
theorem certified_all_numbers (p : Nat) (S : List Nat)
    (hcert : checkCert p S = true) :
    ∀ n s : Nat, readNumber p n = some s → good p s = true := by
  have hstart : 0 ∈ S := by
    simpa using (Bool.and_eq_true_iff.mp hcert).1
  have hrows := (Bool.and_eq_true_iff.mp hcert).2
  have hrow : ∀ s, s ∈ S →
      good p s && (([false,true] : List Bool).all (fun b =>
        match edge p s b with
        | none => true
        | some nxt => S.contains nxt)) = true := by
    intro s hs
    exact (List.all_eq_true.mp hrows) s hs
  have hgood : ∀ s, s ∈ S → good p s = true := by
    intro s hs
    exact (Bool.and_eq_true_iff.mp (hrow s hs)).1
  have hclosed : ∀ s, s ∈ S → ∀ b : Bool, ∀ nxt : Nat,
      edge p s b = some nxt → nxt ∈ S := by
    intro s hs b nxt hedge
    have hall := (Bool.and_eq_true_iff.mp (hrow s hs)).2
    have hb : (match edge p s b with
      | none => true
      | some nxt => S.contains nxt) = true :=
      (List.all_eq_true.mp hall) b (by cases b <;> simp)
    rw [hedge] at hb
    simpa using hb
  have hreach : ∀ n : Nat, ∀ s, readNumber p n = some s → s ∈ S := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro s hs
        by_cases hz : n = 0
        · subst n
          simp [readNumber] at hs
          subst s
          exact hstart
        · have hdiv : n/2 < n :=
            Nat.div_lt_self (by omega) (by decide)
          have hstep : readNumber p n =
              (readNumber p (n/2)).bind
                (fun st => edge p st (n.testBit 0)) := by
            rw [readNumber.eq_1]
            simp [hz]
          rw [hstep] at hs
          cases he : readNumber p (n/2) with
          | none => simp [he] at hs
          | some st =>
              have hst : st ∈ S := ih (n/2) hdiv st he
              simp only [he] at hs
              exact hclosed st hst (n.testBit 0) s hs
  intro n s h
  exact hgood s (hreach n s h)

/-- Kernel-replayed universal graph safety for arbitrary finite integers. -/
theorem certificate_8_all_numbers (n s : Nat)
    (h : readNumber 8 n = some s) : good 8 s = true :=
  certified_all_numbers 8 states8 certificate_8 n s h


/-- Exact low-bit digit used by the graph's binary reader. -/
theorem low_bit_digit (n : Nat) : (n.testBit 0).toNat = n % 2 := by
  have h0 := Nat.mod_two_eq_zero_iff_testBit_zero (x := n)
  cases hb : n.testBit 0 with
  | false =>
      have hm : n % 2 = 0 := h0.mpr hb
      simp [hm]
  | true =>
      have hm : n % 2 ≠ 0 := by
        intro h
        have := h0.mp h
        simp [hb] at this
      have hr : n % 2 < 2 := Nat.mod_lt n (by omega)
      have he : n % 2 = 1 := by omega
      simp [he]

theorem reassemble_low_bit (n : Nat) :
    2*(n/2) + (n.testBit 0).toNat = n := by
  rw [low_bit_digit]
  omega


/-- Explicit executable expansion of the graph's one-bit transition. -/
private theorem edge_formula (p s : Nat) (b : Bool) :
    edge p s b =
      if iterate p (2*(s % 2^(2*p))) % 2 != 0 then none
      else if s / 2^(2*p) == 0 && !b then none
      else some (((2*(s % 2^(2*p)) + b.toNat) % 2^(2*p)) +
        2^(2*p)*dfaStep (s / 2^(2*p)) b) := by
  rfl

/-- Every successful transition encodes the new suffix exactly modulo 2^(2p). -/
theorem edge_suffix_register (p s : Nat) (b : Bool) (u : Nat)
    (h : edge p s b = some u) :
    u % 2^(2*p) = (2*(s % 2^(2*p)) + b.toNat) % 2^(2*p) := by
  rw [edge_formula] at h
  split at h
  · contradiction
  split at h
  · contradiction
  have hu : u = ((2*(s % 2^(2*p)) + b.toNat) % 2^(2*p)) +
      2^(2*p)*dfaStep (s / 2^(2*p)) b := by
    simpa using h.symm
  rw [hu]
  simp [Nat.add_mod, Nat.mul_mod]

/-- A successful edge cannot reset a started (nonzero) stripe-DFA state to
the initial automaton state. -/
private theorem dfaStep_pos (a : Nat) (b : Bool) :
    0 < dfaStep a b := by
  unfold dfaStep
  split <;> omega

/-- Every successful edge installs a positive DFA code, regardless of its
input suffix or head color. -/
theorem edge_nonzero_dfa (p s : Nat) (b : Bool) (u : Nat)
    (h : edge p s b = some u) :
    0 < u / 2^(2*p) := by
  rw [edge_formula] at h
  split at h
  · contradiction
  split at h
  · contradiction
  have hu : u = ((2*(s % 2^(2*p)) + b.toNat) % 2^(2*p)) +
      2^(2*p)*dfaStep (s / 2^(2*p)) b := by
    simpa using h.symm
  rw [hu]
  have hb : 0 < 2^(2*p) := Nat.pow_pos (by omega)
  have hl : ((2*(s % 2^(2*p)) + b.toNat) % 2^(2*p)) <
      2^(2*p) := Nat.mod_lt _ hb
  have hd := dfaStep_pos (s / 2^(2*p)) b
  have hmul : 2^(2*p) ≤ 2^(2*p)*dfaStep (s / 2^(2*p)) b := by
    have hs : ∃ k, dfaStep (s / 2^(2*p)) b = k+1 :=
      ⟨dfaStep (s / 2^(2*p)) b - 1, by omega⟩
    rcases hs with ⟨k, hk⟩
    rw [hk, Nat.mul_succ]
    omega
  have hsum : 2^(2*p) ≤
      ((2*(s % 2^(2*p)) + b.toNat) % 2^(2*p)) +
        2^(2*p)*dfaStep (s / 2^(2*p)) b := by omega
  exact Nat.div_pos hsum hb


/-- The MSB-first reader's suffix register is exactly the low 2p bits
of the input integer. Every nonzero successfully read word also has a
strictly positive (already-started) DFA state. -/
theorem readNumber_register (p : Nat) :
    ∀ n s : Nat, readNumber p n = some s →
      s % 2^(2*p) = n % 2^(2*p) ∧
      (n ≠ 0 → 0 < s / 2^(2*p)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro s hs
      by_cases hz : n = 0
      · subst n
        simp [readNumber] at hs
        subst s
        exact ⟨rfl, by simp⟩
      · have hdiv : n/2 < n :=
          Nat.div_lt_self (by omega) (by decide)
        have hstep : readNumber p n =
          (readNumber p (n/2)).bind
            (fun st => edge p st (n.testBit 0)) := by
          rw [readNumber.eq_1]
          simp [hz]
        rw [hstep] at hs
        cases he : readNumber p (n/2) with
        | none => simp [he] at hs
        | some st =>
            have hi := ih (n/2) hdiv st he
            simp only [he] at hs
            constructor
            · calc
                s % 2^(2*p) =
                    (2*(st % 2^(2*p)) + (n.testBit 0).toNat) %
                      2^(2*p) :=
                    edge_suffix_register p st (n.testBit 0) s hs
                _ = (2*((n/2) % 2^(2*p)) + (n.testBit 0).toNat) %
                      2^(2*p) := by rw [hi.1]
                _ = (2*(n/2) + (n.testBit 0).toNat) %
                      2^(2*p) := by simp [Nat.add_mod, Nat.mul_mod]
                _ = n % 2^(2*p) := by rw [reassemble_low_bit]
            · intro _
              exact edge_nonzero_dfa p st (n.testBit 0) s hs


/-- Every finitely supported period-p moving-frame profile has a
SUCCESSFUL MSB-first reader traversal, at every spatial width. This
eliminates the largest missing semantic bridge between genuine
Rule 30 dynamics and the certified finite automata. -/
theorem periodic_readNumber_success (p : Nat) :
    ∀ n : Nat, iterate p n = n →
      ∃ s : Nat, readNumber p n = some s := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hperiod
      by_cases hz : n = 0
      · subst n
        exact ⟨0, readNumber_zero p⟩
      · have hdiv : n/2 < n :=
          Nat.div_lt_self (by omega) (by decide)
        have htail : iterate p (n/2) = n/2 := by
          rw [iterate_div_two, hperiod]
        obtain ⟨st, hst⟩ := ih (n/2) hdiv htail
        have hi := readNumber_register p (n/2) st hst
        have hh : (iterate p
            (2*(n/2) + (n.testBit 0).toNat)).testBit 0 =
            n.testBit 0 := by
          rw [reassemble_low_bit, hperiod]
        have hguard : iterate p (2*(st % 2^(2*p))) % 2 = 0 := by
          rw [hi.1]
          exact (numerical_edge_guard p (n/2) (n.testBit 0)).mp hh
        have hlead : (st / 2^(2*p) == 0 && !(n.testBit 0)) = false := by
          by_cases hm : n/2 = 0
          · have hb : n.testBit 0 = true := by
              have hr := reassemble_low_bit n
              rw [hm] at hr
              cases hbit : n.testBit 0 with
              | false =>
                  simp [hbit] at hr
                  omega
              | true => rfl
            simp [hb]
          · have hp : 0 < st / 2^(2*p) := hi.2 hm
            have hn0 : st / 2^(2*p) ≠ 0 := by omega
            simp [hn0]
        let result : Nat :=
          ((2*(st % 2^(2*p)) + (n.testBit 0).toNat) % 2^(2*p)) +
            2^(2*p)*dfaStep (st / 2^(2*p)) (n.testBit 0)
        have hedge : edge p st (n.testBit 0) = some result := by
          rw [edge_formula]
          have hguardFalse : (iterate p (2*(st % 2^(2*p))) % 2 != 0) = false := by
            simp [hguard]
          rw [hguardFalse, hlead]
          rfl
        have hstep : readNumber p n =
            (readNumber p (n/2)).bind
              (fun prev => edge p prev (n.testBit 0)) := by
          rw [readNumber.eq_1]
          simp [hz]
        refine ⟨result, ?_⟩
        rw [hstep, hst]
        simpa using hedge

/-- The P=8 graph certificate applies to EVERY finite T^8-periodic
profile of arbitrary width, and constrains its final gates/DFA state. -/
theorem periodic_8_graph_good (n : Nat) (h : iterate 8 n = n) :
    ∃ s, readNumber 8 n = some s ∧ good 8 s = true := by
  obtain ⟨s, hs⟩ := periodic_readNumber_success 8 n h
  exact ⟨s, hs, certificate_8_all_numbers n s hs⟩


/-- The numerical remainder modulo four is uniquely determined by the
two least significant Boolean bits. -/
theorem mod_four_bits (n : Nat) :
    n % 4 = (n.testBit 0).toNat + 2*(n.testBit 1).toNat := by
  have h1 : (n.testBit 1).toNat = (n/2) % 2 := by
    simpa only [Nat.testBit_div_two, Nat.zero_add, Nat.reduceAdd]
      using low_bit_digit (n/2)
  rw [low_bit_digit, h1]
  omega

/-- Agreement on 2p initial bits forces equality of every gate in the
first p time steps, for any starting temporal phase. -/
theorem gates_congr_prefix (p phase x y : Nat)
    (h : ∀ k, k < 2*p → x.testBit k = y.testBit k) :
    gates p x phase = gates p y phase := by
  induction p generalizing x y phase with
  | zero => rfl
  | succ p ih =>
      have h0 : x.testBit 0 = y.testBit 0 := h 0 (by omega)
      have h1 : x.testBit 1 = y.testBit 1 := h 1 (by omega)
      have hmod4 : x % 4 = y % 4 := by
        rw [mod_four_bits x, mod_four_bits y, h0, h1]
      have hmod2 : x % 2 = y % 2 := by
        rw [← low_bit_digit x, ← low_bit_digit y, h0]
      have htail : ∀ k, k < 2*p →
          (T x).testBit k = (T y).testBit k := by
        intro k hk
        rw [T_testBit x k, T_testBit y k]
        rw [h k (by omega), h (k+1) (by omega),
          h (k+2) (by omega)]
      have ht := ih (phase+1) (T x) (T y) htail
      change ((if phase % 2 == 0 then x % 4 != 0 else x % 2 != 0) &&
        gates p (T x) (phase+1)) =
        ((if phase % 2 == 0 then y % 4 != 0 else y % 2 != 0) &&
        gates p (T y) (phase+1))
      rw [hmod4, hmod2, ht]

/-- Gate validity in the first p time steps is determined entirely by
the low 2p initial bits, exactly as used by the graph. -/
theorem gates_suffix_mod (p phase n : Nat) :
    gates p (n % 2^(2*p)) phase = gates p n phase := by
  apply gates_congr_prefix
  intro k hk
  simp [Nat.testBit_mod_two_pow, hk]


/-- The first unified all-width period-eight Rule 30 exclusion theorem:
any finite profile returning after eight moving-frame steps and passing
the exact two-phase shielding gates MUST be accepted by the explicit
eight-state stripe-language automaton, with no bound on spatial width.
This statement uses no assumptions about how the automaton was computed. -/
theorem period_eight_shield_implies_dfa (n : Nat)
    (hperiod : iterate 8 n = n)
    (hshield : gates 8 n 0 = true) :
    ∃ s : Nat, readNumber 8 n = some s ∧
      dfaAccept (s / 2^(2*8)) = true := by
  obtain ⟨s, hs⟩ := periodic_readNumber_success 8 n hperiod
  have hreg := (readNumber_register 8 n s hs).1
  have hcert := certificate_8_all_numbers n s hs
  have hgate : gates 8 (s % 2^(2*8)) 0 = true := by
    calc
      gates 8 (s % 2^(2*8)) 0 =
        gates 8 (n % 2^(2*8)) 0 := by rw [hreg]
      _ = gates 8 n 0 := gates_suffix_mod 8 0 n
      _ = true := hshield
  have haccept : dfaAccept (s / 2^(2*8)) = true := by
    change (!(gates 8 (s % 2^(2*8)) 0) ||
        dfaAccept (s / 2^(2*8))) = true at hcert
    rw [hgate] at hcert
    simpa using hcert
  exact ⟨s, hs, haccept⟩


/-! ## A closed-form arithmetic invariant for the stripe-language DFA -/

/-- Numerical MSB-first words 10, 1010, 101010, ... -/
def evenStripe : Nat → Nat
  | 0 => 2
  | m+1 => 4*evenStripe m + 2

/-- Numerical MSB-first words 110, 11010, 1101010, ... -/
def oddStripe : Nat → Nat
  | 0 => 6
  | m+1 => 4*oddStripe m + 2

/-- Explicit finite stripe family, indexed by parity and length. -/
def IsStripe (n : Nat) : Prop :=
  n = 1 ∨ (∃ m, n = evenStripe m) ∨ (∃ m, n = oddStripe m)

/-- Every DFA state stores a precise arithmetic prefix invariant.
State 7 is absorbing and deliberately unconstrained. -/
def dfaStateInv (a n : Nat) : Prop :=
  match a with
  | 0 => n = 0
  | 1 => n = 1
  | 2 => ∃ m, n = evenStripe m
  | 3 => n = 3
  | 4 => ∃ m, n = 2*evenStripe m + 1
  | 5 => ∃ m, n = oddStripe m
  | 6 => ∃ m, n = 2*oddStripe m + 1
  | _ => True

/-- Arithmetic invariant is stable under every state and input bit.
This proves the stripe DFA recognizes no words outside the stated
closed-form family, without any assumption of a bounded word length. -/
theorem dfaStateInv_step (a n : Nat) (b : Bool)
    (h : dfaStateInv a n) :
    dfaStateInv (dfaStep a b) (2*n + b.toNat) := by
  have ha : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ 7 ≤ a := by omega
  rcases ha with h0 | h1 | h2 | h3 | h4 | h5 | h6 | hlarge
  · subst a
    cases b <;> simp_all [dfaStateInv, dfaStep]
  · subst a
    cases b with
    | false =>
        change n = 1 at h
        change ∃ m, 2*n = evenStripe m
        refine ⟨0, ?_⟩
        simp [h, evenStripe]
    | true =>
        change n = 1 at h
        change 2*n + 1 = 3
        omega
  · subst a
    cases b with
    | false => trivial
    | true =>
        change ∃ m, n = evenStripe m at h
        obtain ⟨m, hm⟩ := h
        change ∃ m, 2*n+1 = 2*evenStripe m + 1
        exact ⟨m, by rw [hm]⟩
  · subst a
    cases b with
    | false =>
        change n=3 at h
        change ∃ m, 2*n = oddStripe m
        exact ⟨0, by simp [h, oddStripe]⟩
    | true => trivial
  · subst a
    cases b with
    | false =>
        change ∃ m, n = 2*evenStripe m + 1 at h
        obtain ⟨m, hm⟩ := h
        change ∃ m, 2*n = evenStripe m
        refine ⟨m+1, ?_⟩
        rw [hm]
        simp [evenStripe]
        omega
    | true => trivial
  · subst a
    cases b with
    | false => trivial
    | true =>
        change ∃ m, n = oddStripe m at h
        obtain ⟨m, hm⟩ := h
        change ∃ m, 2*n+1 = 2*oddStripe m + 1
        exact ⟨m, by rw [hm]⟩
  · subst a
    cases b with
    | false =>
        change ∃ m, n = 2*oddStripe m + 1 at h
        obtain ⟨m, hm⟩ := h
        change ∃ m, 2*n = oddStripe m
        refine ⟨m+1, ?_⟩
        rw [hm]
        simp [oddStripe]
        omega
    | true => trivial
  · have hh : dfaStep a b = 7 := by
      obtain ⟨k, hk⟩ : ∃ k, a = k+7 := ⟨a-7, by omega⟩
      rw [hk]
      cases b <;> simp [dfaStep]
    rw [hh]
    trivial

/-- Acceptance of a nonempty DFA word implies membership in the
arithmetic finite stripe family. -/
theorem dfa_accept_implies_stripe (a n : Nat)
    (hinv : dfaStateInv a n) (hacc : dfaAccept a = true) :
    IsStripe n := by
  have ha : a=1 ∨ a=2 ∨ a=5 := by
    unfold dfaAccept at hacc
    simp only [Bool.or_eq_true, beq_iff_eq] at hacc
    omega
  rcases ha with h1 | h2 | h5
  · subst a
    exact Or.inl hinv
  · subst a
    exact Or.inr (Or.inl hinv)
  · subst a
    exact Or.inr (Or.inr hinv)


/-- An accepted edge updates the DFA quotient exactly, not just its
nonzero status. This is the second half of the complete graph-register
semantics. -/
theorem edge_dfa_register (p st : Nat) (b : Bool) (u : Nat)
    (h : edge p st b = some u) :
    u / 2^(2*p) = dfaStep (st / 2^(2*p)) b := by
  rw [edge_formula] at h
  split at h
  · contradiction
  split at h
  · contradiction
  have hu : u = ((2*(st % 2^(2*p)) + b.toNat) % 2^(2*p)) +
      2^(2*p)*dfaStep (st / 2^(2*p)) b := by
    simpa using h.symm
  rw [hu]
  have hb : 0 < 2^(2*p) := Nat.pow_pos (by omega)
  have hl : ((2*(st % 2^(2*p)) + b.toNat) % 2^(2*p)) <
      2^(2*p) := Nat.mod_lt _ hb
  rw [Nat.add_mul_div_left]
  · simp [Nat.div_eq_of_lt hl]
  · exact hb

/-- The DFA quotient after reading any finite number matches the
arithmetic invariant describing the full MSB-first binary prefix. -/
theorem readNumber_dfaStateInv (p : Nat) :
    ∀ n s : Nat, readNumber p n = some s →
      dfaStateInv (s / 2^(2*p)) n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro s hs
      by_cases hz : n = 0
      · subst n
        simp [readNumber] at hs
        subst s
        simp [dfaStateInv]
      · have hdiv : n/2 < n :=
          Nat.div_lt_self (by omega) (by decide)
        have hstep : readNumber p n =
            (readNumber p (n/2)).bind
              (fun st => edge p st (n.testBit 0)) := by
          rw [readNumber.eq_1]
          simp [hz]
        rw [hstep] at hs
        cases he : readNumber p (n/2) with
        | none => simp [he] at hs
        | some st =>
            have hinv := ih (n/2) hdiv st he
            simp only [he] at hs
            have hnext := dfaStateInv_step (st/2^(2*p)) (n/2)
              (n.testBit 0) hinv
            have hquot := edge_dfa_register p st (n.testBit 0) s hs
            rw [← hquot, reassemble_low_bit] at hnext
            exact hnext

/-- Genuine all-width period-eight shielding classification, now
in the *closed-form numerical stripe family*, with no residual
automaton-acceptance conclusion or unproved language bridge. -/
theorem period_eight_isStripe (n : Nat)
    (hperiod : iterate 8 n = n)
    (hshield : gates 8 n 0 = true) :
    IsStripe n := by
  obtain ⟨s, hs, hacc⟩ := period_eight_shield_implies_dfa n hperiod hshield
  have hinv := readNumber_dfaStateInv 8 n s hs
  exact dfa_accept_implies_stripe (s/2^(2*8)) n hinv hacc


/-- Canonical stripe integer indexed by spatial width minus one.
Thus stripeNumber 0=1, stripeNumber 1=2, stripeNumber 2=6,
stripeNumber 3=10, and so on. -/
def stripeNumber : Nat → Nat
  | 0 => 1
  | k+1 => if k % 2 == 0 then evenStripe (k/2) else oddStripe (k/2)

theorem stripeNumber_even (m : Nat) :
    stripeNumber (2*m+1) = evenStripe m := by
  simp [stripeNumber]

theorem stripeNumber_odd (m : Nat) :
    stripeNumber (2*m+2) = oddStripe m := by
  have heq : 2*m+2 = (2*m+1)+1 := by omega
  rw [heq]
  have hdiv : (2*m+1)/2 = m := by omega
  simp [stripeNumber, hdiv]

/-- Lean-checked equivalence between the closed-form arithmetic families
and a single canonical stripe integer indexed by spatial width. -/
theorem isStripe_iff_exists_stripeNumber (n : Nat) :
    IsStripe n ↔ ∃ w : Nat, n = stripeNumber w := by
  constructor
  · intro h
    rcases h with h | ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨0, by simpa [stripeNumber] using h⟩
    · exact ⟨2*m+1, by rw [hm, stripeNumber_even]⟩
    · exact ⟨2*m+2, by rw [hm, stripeNumber_odd]⟩
  · rintro ⟨w, rfl⟩
    cases w with
    | zero => exact Or.inl rfl
    | succ k =>
        by_cases hmod : k % 2 = 0
        · exact Or.inr (Or.inl ⟨k/2, by simp [stripeNumber, hmod]⟩)
        · exact Or.inr (Or.inr ⟨k/2, by simp [stripeNumber, hmod]⟩)

/-- Final all-width temporal-period-eight stripe classification with an
explicit constructive spatial-width parameter. -/
theorem period_eight_stripe_width (n : Nat)
    (hperiod : iterate 8 n = n)
    (hshield : gates 8 n 0 = true) :
    ∃ w : Nat, n = stripeNumber w :=
  (isStripe_iff_exists_stripeNumber n).mp
    (period_eight_isStripe n hperiod hshield)


/-- Reusable, all-width conclusion of any exact finite-state graph
certificate. This is the generic proof bridge for periods 2, 4, 8,
and future independently kernel-checked graph certificates. -/
theorem any_certified_period_is_stripe (p : Nat) (S : List Nat)
    (hcert : checkCert p S = true)
    (n : Nat) (hperiod : iterate p n = n)
    (hgates : gates p n 0 = true) :
    ∃ w : Nat, n = stripeNumber w := by
  obtain ⟨s, hs⟩ := periodic_readNumber_success p n hperiod
  have hreg := (readNumber_register p n s hs).1
  have hgood := certified_all_numbers p S hcert n s hs
  have hg : gates p (s % 2^(2*p)) 0 = true := by
    calc
      gates p (s % 2^(2*p)) 0 =
          gates p (n % 2^(2*p)) 0 := by rw [hreg]
      _ = gates p n 0 := gates_suffix_mod p 0 n
      _ = true := hgates
  have ha : dfaAccept (s / 2^(2*p)) = true := by
    change (!(gates p (s % 2^(2*p)) 0) ||
      dfaAccept (s / 2^(2*p))) = true at hgood
    rw [hg] at hgood
    simpa using hgood
  have hstripe := dfa_accept_implies_stripe (s/2^(2*p)) n
    (readNumber_dfaStateInv p n s hs) ha
  exact (isStripe_iff_exists_stripeNumber n).mp hstripe

/-- No periodic nonstripe moving-front word of temporal period dividing
two satisfies both two-phase gates, at any finite spatial width. -/
theorem period_two_stripe_width (n : Nat)
    (hperiod : iterate 2 n = n)
    (hgates : gates 2 n 0 = true) :
    ∃ w : Nat, n = stripeNumber w :=
  any_certified_period_is_stripe 2 states2 certificate_2 n hperiod hgates

/-- Same all-width stripe rigidity for full temporal period dividing four. -/
theorem period_four_stripe_width (n : Nat)
    (hperiod : iterate 4 n = n)
    (hgates : gates 4 n 0 = true) :
    ∃ w : Nat, n = stripeNumber w :=
  any_certified_period_is_stripe 4 states4 certificate_4 n hperiod hgates


/-- Every entry of the candidate 2116-node temporal pair pool
meeting the 32 alternating phase gates has a period-2 head code.
This states ONLY a property of the displayed list, not yet universal
coverage of all finite P32 orbits. -/
theorem pool32_gate_to_head_two :
    pool32.all rowGateOK = true := by
  simp only [pool32, List.all_append, Bool.and_eq_true_iff]
  exact And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (block0_gate) (block1_gate)) (block2_gate)) (block3_gate)) (block4_gate)) (block5_gate)) (block6_gate)) (block7_gate)) (block8_gate)) (block9_gate)) (block10_gate)) (block11_gate)) (block12_gate)) (block13_gate)) (block14_gate)) (block15_gate)) (block16_gate)) (block17_gate)) (block18_gate)) (block19_gate)) (block20_gate)) (block21_gate)) (block22_gate)) (block23_gate)) (block24_gate)) (block25_gate)) (block26_gate)) (block27_gate)) (block28_gate)) (block29_gate)) (block30_gate)) (block31_gate)) (block32_gate)) (block33_gate)) (block34_gate)) (block35_gate)) (block36_gate)) (block37_gate)) (block38_gate)) (block39_gate)) (block40_gate)) (block41_gate)) (block42_gate)) (block43_gate)) (block44_gate)) (block45_gate)) (block46_gate)) (block47_gate)) (block48_gate)) (block49_gate)) (block50_gate)) (block51_gate)) (block52_gate)) (block53_gate)) (block54_gate)) (block55_gate)) (block56_gate)) (block57_gate)) (block58_gate)) (block59_gate)) (block60_gate)) (block61_gate)) (block62_gate)) (block63_gate)) (block64_gate)) (block65_gate)) (block66_gate)

/-- Every pool node is closed under the two admissible predecessor
transitions, proved by the Lean kernel in 67 independent blocks. -/
theorem pool32_checked : poolCheck 32 pool32 = true := by
  have hstart : pairMem pool32 0 0 = true := by
    decide +kernel
  have hall : pool32.all (nodeCheck 32 pool32) = true := by
    simp only [pool32, List.all_append, Bool.and_eq_true_iff]
    exact And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_0_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_1_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_2_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_3_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_4_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_5_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_6_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_7_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_8_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_9_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_10_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_11_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_12_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_13_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_14_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_15_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_16_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_17_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_18_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_19_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_20_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_21_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_22_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_23_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_24_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_25_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_26_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_27_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_28_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_29_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_30_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_31_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_32_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_33_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_34_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_35_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_36_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_37_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_38_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_39_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_40_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_41_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_42_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_43_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_44_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_45_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_46_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_47_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_48_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_49_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_50_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_51_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_52_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_53_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_54_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_55_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_56_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_57_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_58_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_59_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_60_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_61_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_62_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_63_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_64_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_65_closed) Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.block_66_closed
  rw [poolCheck]
  exact Bool.and_eq_true_iff.mpr ⟨hstart, hall⟩

/-- For any selected P32 temporal pair, the first (head) column
has period dividing 2. -/
theorem node_gate_implies_head_two (e : Node)
    (he : e ∈ pool32) (hg : nodeGate32 e = true) :
    ∀ t, pat 32 e.b (t+2) = pat 32 e.b t := by
  have h := List.all_eq_true.mp pool32_gate_to_head_two e he
  change (if nodeGate32 e then periodCheck 32 2 e.b else true) = true at h
  simp only [hg, ite_true] at h
  exact (periodCheck_iff 32 2 e.b (by decide)).mp h

/-- The exact 32-step alternating gate forces a head clock of period
two in any finite-support triangular Boolean history. -/
theorem gates_force_head_two
    (x : Nat → Nat → Bool) (W : Nat)
    (hstep : ∀ k t, x k (t+1) =
      xor (x k t) (x (k+1) t || x (k+2) t))
    (hperiod : ∀ k t, x k (t+32) = x k t)
    (hzero : ∀ k, W ≤ k → ∀ t, x k t = false)
    (hgates : ∀ t, t < 32 →
      (if t % 2 == 0 then x 0 t || x 1 t else x 0 t) = true) :
    ∀ t, x 0 (t+2) = x 0 t := by
  have hcover := covers_finite_family 32 (by decide) pool32
    pool32_checked x W hstep hperiod hzero 0
  obtain ⟨e, he, hb, hc⟩ := hcover
  have hg : nodeGate32 e = true := by
    apply List.all_eq_true.mpr
    intro t ht
    change (if t % 2 == 0 then
      pat 32 e.b t || pat 32 e.c t else pat 32 e.b t) = true
    have h := hgates t (List.mem_range.mp ht)
    rw [hb t, hc t] at h
    exact h
  have ht := node_gate_implies_head_two e he hg
  intro t
  rw [hb (t+2),hb t]
  exact ht t

/-- The strong consequence: a full 32-clock finite right Rule30 state
passing all alternating gates already has full period dividing TWO,
at every finite spatial width. -/
theorem finite_state_gate_forces_period_two
    (x : Rule30ControlledResponse.State) (W : Nat)
    (hzero : ∀ k, W ≤ k → x k = false)
    (hfull : Rule30ControlledResponse.iterate x 32 = x)
    (hgates : ∀ t, t < 32 →
      (if t % 2 == 0 then
        Rule30ControlledResponse.iterate x t 0 ||
        Rule30ControlledResponse.iterate x t 1
      else Rule30ControlledResponse.iterate x t 0) = true) :
    Rule30ControlledResponse.iterate x 2 = x := by
  have hp := iterate_period_of_return x 32 hfull
  have hf := iterate_zero_tail x W hzero
  have hh : ∀ t, Rule30ControlledResponse.iterate x (t+2) 0 =
      Rule30ControlledResponse.iterate x t 0 := by
    apply gates_force_head_two
      (fun k t => Rule30ControlledResponse.iterate x t k) W
    · intro k t
      rfl
    · intro k t
      exact congrFun (hp t) k
    · intro k hk t
      exact hf t k hk
    · exact hgates
  exact finite_state_clock_detected 32 2 (by decide) pool32
    pool32_checked Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate.detection32_checked
    x W hzero hfull hh

/-- The independent integer moving-front executable agrees with the
official autonomous triangular Rule 30 iteration at all times and sites. -/
theorem official_integer_iterate (p n : Nat) :
    Rule30ControlledResponse.iterate (fun k => n.testBit k) p =
      (fun k => (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate p n).testBit k) := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih =>
      calc
        Rule30ControlledResponse.iterate (fun k => n.testBit k) (p+1) =
            Rule30ControlledResponse.iterate
              (Rule30ControlledResponse.diagonal (fun k => n.testBit k)) p :=
          (Rule30ControlledResponse.iterate_from (fun k => n.testBit k) p).symm
        _ = Rule30ControlledResponse.iterate
              (fun k => (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.T n).testBit k) p := by
          congr 1
          funext k
          exact (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.T_testBit n k).symm
        _ = (fun k => (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate p (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.T n)).testBit k) :=
          ih (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.T n)
        _ = (fun k => (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate (p+1) n).testBit k) := rfl

/-- The triangular diagonal map is ordinary Rule 30 (`Rule30Realization.evol`) seen
in a frame moving right one cell per step: read any configuration `y` from site
`o` rightwards, and cell `k` after `t` diagonal steps is cell `o + k + t` of
`evol y t`. Cells left of `o` never matter. -/
theorem controlled_iterate_eq_evol (y : Int → Bool) (o : Int) :
    ∀ t k : Nat, Rule30ControlledResponse.iterate (fun j => y (o + j)) t k =
      Rule30Realization.evol y t (o + ((k + t : Nat) : Int))
  | 0, k => by simp [Rule30ControlledResponse.iterate, Rule30Realization.evol]
  | t+1, k => by
      show Rule30ControlledResponse.diagonal
          (Rule30ControlledResponse.iterate (fun j => y (o + j)) t) k = _
      simp only [Rule30ControlledResponse.diagonal]
      rw [controlled_iterate_eq_evol y o t k, controlled_iterate_eq_evol y o t (k+1),
        controlled_iterate_eq_evol y o t (k+2), Rule30Realization.evol]
      have h1 : o + ((k + (t+1) : Nat) : Int) - 1 = o + ((k + t : Nat) : Int) := by omega
      have h3 : o + ((k + (t+1) : Nat) : Int) + 1 = o + ((k + 2 + t : Nat) : Int) := by omega
      have h2 : o + ((k + (t+1) : Nat) : Int) = o + ((k + 1 + t : Nat) : Int) := by omega
      rw [h1, h3, h2]
      rfl

/-- The integer map `T` is ordinary Rule 30 in the moving frame: if bit `j` of `n`
is the cell `o + j` of an arbitrary configuration `y`, then bit `k` of
`iterate t n` is the cell `o + k + t` of `evol y t`. -/
theorem integer_iterate_eq_evol (y : Int → Bool) (o : Int) (n : Nat)
    (hn : ∀ j : Nat, y (o + j) = n.testBit j) (t k : Nat) :
    (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate t n).testBit k =
      Rule30Realization.evol y t (o + ((k + t : Nat) : Int)) := by
  have hx : (fun j : Nat => y (o + j)) = (fun j => n.testBit j) := funext hn
  rw [← controlled_iterate_eq_evol y o t k, hx, official_integer_iterate]

/-- The return hypothesis `iterate p n = n` says exactly that, in ordinary Rule 30
from any configuration that carries the bits of `n` from site `o` on, the right
half from `o` reappears after `p` steps translated `p` cells to the right. -/
theorem integer_return_iff_evol (y : Int → Bool) (o : Int) (n : Nat)
    (hn : ∀ j : Nat, y (o + j) = n.testBit j) (p : Nat) :
    Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate p n = n ↔
      ∀ k : Nat, Rule30Realization.evol y p (o + ((k + p : Nat) : Int)) = y (o + k) := by
  constructor
  · intro h k
    rw [← integer_iterate_eq_evol y o n hn p k, h, hn]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [integer_iterate_eq_evol y o n hn p k, h k, hn]

/-- Under the official geometric head/neighbor gate hypothesis,
an arbitrary finite period-thirty-two integer profile is exactly a
canonical stripe, with no maximum spatial width. -/
theorem finite_period32_official_gate_is_stripe
    (n W : Nat)
    (hfinite : ∀ k, W ≤ k → n.testBit k = false)
    (hreturn : Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate 32 n = n)
    (hgates : ∀ t, t < 32 →
      (if t % 2 == 0 then
        Rule30ControlledResponse.iterate (fun k => n.testBit k) t 0 ||
        Rule30ControlledResponse.iterate (fun k => n.testBit k) t 1
       else Rule30ControlledResponse.iterate (fun k => n.testBit k) t 0) = true) :
    ∃ w : Nat, n = Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.stripeNumber w := by
  have hs : Rule30ControlledResponse.iterate
        (fun k => n.testBit k) 32 = (fun k => n.testBit k) := by
    rw [official_integer_iterate, hreturn]
  have htwoState :=
    Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.finite_state_gate_forces_period_two
      (fun k => n.testBit k) W hfinite hs hgates
  have htwo : Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate 2 n = n := by
    rw [official_integer_iterate] at htwoState
    apply Nat.eq_of_testBit_eq
    intro k
    exact congrFun htwoState k
  have hg0 : (n % 4 != 0) = true := by
    have h := hgates 0 (by decide)
    change (n.testBit 0 || n.testBit 1) = true at h
    rw [Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.mod_four_bits n]
    cases hb0 : n.testBit 0 <;> cases hb1 : n.testBit 1 <;>
      simp [hb0, hb1] at h ⊢
  have hg1 : (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.T n % 2 != 0) = true := by
    have h := hgates 1 (by decide)
    change Rule30ControlledResponse.iterate
      (fun k => n.testBit k) 1 0 = true at h
    rw [official_integer_iterate] at h
    have hh : (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.T n).testBit 0 = true := by
      simpa [Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate] using h
    have hm : Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.T n % 2 = 1 := by
      rw [← Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.low_bit_digit (Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.T n), hh]
      rfl
    simp [hm]
  have hgate2 : Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.gates 2 n 0 = true := by
    simp [Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.gates, hg0, hg1]
  exact Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.period_two_stripe_width n htwo hgate2


/-- Every finite-support official triangular right-front state returning
after 32 steps and satisfying the alternating two-phase shield gates
has an actual full-state temporal period dividing 2. -/
theorem period_thirtytwo_reduces_to_two
    (x : Ruliology.CellularAutomata.Rule30ControlledResponse.State)
    (W : Nat)
    (hfinite : ∀ k, W ≤ k → x k = false)
    (hperiod : Ruliology.CellularAutomata.Rule30ControlledResponse.iterate x 32 = x)
    (hgates : ∀ t, t < 32 →
      (if t % 2 == 0 then
        Ruliology.CellularAutomata.Rule30ControlledResponse.iterate x t 0 ||
        Ruliology.CellularAutomata.Rule30ControlledResponse.iterate x t 1
      else Ruliology.CellularAutomata.Rule30ControlledResponse.iterate x t 0) = true) :
    Ruliology.CellularAutomata.Rule30ControlledResponse.iterate x 2 = x :=
  Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.finite_state_gate_forces_period_two x W
    hfinite hperiod hgates

/-- Full all-finite-width canonical stripe classification for a
32-periodic numerical moving-front state satisfying the shield gates. -/
theorem period_thirtytwo_gate_stripe
    (n W : Nat)
    (hfinite : ∀ k, W ≤ k → n.testBit k = false)
    (hperiod : Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.iterate 32 n = n)
    (hgates : ∀ t, t < 32 →
      (if t % 2 == 0 then
        Ruliology.CellularAutomata.Rule30ControlledResponse.iterate
          (fun k => n.testBit k) t 0 ||
        Ruliology.CellularAutomata.Rule30ControlledResponse.iterate
          (fun k => n.testBit k) t 1
      else Ruliology.CellularAutomata.Rule30ControlledResponse.iterate
          (fun k => n.testBit k) t 0) = true) :
    ∃ w : Nat, n = Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.stripeNumber w :=
  Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.finite_period32_official_gate_is_stripe n W
    hfinite hperiod hgates

end Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding
