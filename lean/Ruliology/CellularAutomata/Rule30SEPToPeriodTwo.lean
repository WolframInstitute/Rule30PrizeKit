module

public import Ruliology.CellularAutomata.Rule30SeparatorEquivalences
public import Ruliology.CellularAutomata.Rule30AlternatingTraceBridge

/-!
# `SEP`, `RW` and `BWH` each exclude a nonconstant period-two center

For every nonzero finite row, a nonconstant center trace of period two from time zero is excluded by
any of the open hypotheses `OrbitSeparator` (`SEP`), `RW`, or `BWH` together with `SmallRW`:
`sep_implies_period_two`, `rw_implies_period_two`, `bwh_small_implies_period_two`, each concluding
`PeriodTwoExcluded` of `Rule30AlternatingTraceBridge`. The coordinate dictionary between the actual
Rule 30 diagram and hard-core streams is proved from four local bits: `actual_cone_chart`,
`actual_peel_chart`, `actual_endpoint_hardcore`, `actual_endpoint_finite_rank`. All diagram times are
nonnegative; the endpoint starts two updates after a center-zero phase, and only the left finite origin
is used. Control `finite_origin_control`: the periodic row of `Rule30AlternatingTraceBridge` has an
alternating center and is nonzero but not finitely supported, so finite origin cannot be omitted.

For the official center column, `center_not_eventually_period_two_of_sep`, `..._of_rw` and
`..._of_bwh` conclude that there is no transient `T` after which `c(t + 2) = c(t)`. None of `SEP`, `RW`
or `BWH` is proved here, so no period is excluded.

**Relation to `Rule30PeriodTwo.Q01` and to mortality.** Proved: `BWH` with `SmallRW` implies `RW`
(`bwh_implies_rw`), `RW` implies `SEP` (`rw_implies_orbit_separator`), `SEP` and `ConstantTailSeparator`
are equivalent (`Rule30SeparatorEquivalences.separator_equivalence`), and each of them gives
`PeriodTwoExcluded`. In `Rule30AlternatingTraceBridge`, mortality of the auxiliary frontier implies
`Q01` (`Q01_of_mortality`) and `PeriodTwoExcluded`, and `Q01` excludes an eventual period two of the
official center column (`Rule30PeriodTwo.not_eventually_period_two_of_Q01`) and every left-finite
row with center `1, 0, 1, 0, …` (`Rule30PeriodTwoSideways.Q01_no_leftfinite_alternating`). No
implication in either direction is proved between `SEP`, `RW` or `BWH` on one side and `Q01` or mortality
on the other. The chart here uses the right half of the row: `actual_endpoint_hardcore` gets the
hard-core property of the endpoint stream from the rule at column `1` (`right_no11`), while `Q01` and
the history of `Rule30AlternatingTraceBridge.immortalFromHistory` have no right half. So `SEP`, `RW` and
`BWH` are reductions of period two that are separate from `Q01` and from mortality, with no known
order of strength.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30SEPToPeriodTwo

open Rule30WedgeBridge Rule30SeparatorBridge Rule30SeparatorEquivalences


open Rule30AlternatingTraceBridge (CAConfig caEvolve caEvolve_succ LeftFinite
  AlternatingCenter center_flip center_even pin front Nonzero FiniteSupport)

def encodePair : Bool → Bool → Sym
  | false,false => 0
  | false,true => 1
  | true,false => 2
  | true,true => 3

def cellPair (y : CAConfig) (t : Nat) (i : Int) : Sym :=
  encodePair (caEvolve t y i) (caEvolve t y (i-1))

theorem pair_inverse_table : ∀ a b c d : Bool,
    phi (encodePair a b)
      (encodePair (xor c (b || a)) (xor d (c || b)))=encodePair c d := by decide

theorem encode_one_high_false : ∀ a b : Bool, encodePair a b=1 → a=false := by decide
theorem encode_xor_binary : ∀ a b : Bool, xor b a=true → binary (encodePair a b) := by
  unfold binary
  decide

theorem pair_backward (y : CAConfig) (t : Nat) (i : Int) :
    phi (cellPair y t i) (cellPair y (t+1) (i-1))=cellPair y t (i-2) := by
  have h1 : i-1-1=i-2 := by omega
  have h2 : i-1+1=i := by omega
  have h3 : i-2-1=i-3 := by omega
  have h4 : i-2+1=i-1 := by omega
  simp only [cellPair,caEvolve_succ,h1,h2,h3,h4]
  exact pair_inverse_table _ _ _ _

def actualEndpoint (y : CAConfig) (o : Nat) : Stream :=
  fun j=>cellPair y (o+2*j+2) (-1)

theorem center_odd (y : CAConfig) (hA : AlternatingCenter y)
    (o : Nat) (ho : caEvolve o y 0=false) (j : Nat) :
    caEvolve (o+2*j+1) y 0=true := by
  rw [center_flip y hA,center_even y (center_flip y hA) o ho j]
  rfl

theorem actual_boundary (y : CAConfig) (hA : AlternatingCenter y)
    (o : Nat) (ho : caEvolve o y 0=false) (j : Nat) :
    boundary (actualEndpoint y o j)=cellPair y (o+2*j+1) (-2) := by
  have hc1 := center_odd y hA o ho j
  have hc0 : caEvolve ((o+2*j+1)+1) y 0=false := by
    have hi : (o+2*j+1)+1=o+2*(j+1) := by omega
    rw [hi]
    exact center_even y (center_flip y hA) o ho (j+1)
  have hp := pin y (o+2*j+1) hc1 hc0
  have hi : o+2*j+2=(o+2*j+1)+1 := by omega
  unfold actualEndpoint
  rw [hi]
  simp only [cellPair,caEvolve_succ]
  change boundary (encodePair
    (xor (caEvolve (o+2*j+1) y (-2))
      (caEvolve (o+2*j+1) y (-1) || caEvolve (o+2*j+1) y 0))
    (xor (caEvolve (o+2*j+1) y (-3))
      (caEvolve (o+2*j+1) y (-2) || caEvolve (o+2*j+1) y (-1)))) =
    encodePair (caEvolve (o+2*j+1) y (-2)) (caEvolve (o+2*j+1) y (-3))
  rw [hp,hc1]
  cases caEvolve (o+2*j+1) y (-2) <;>
    cases caEvolve (o+2*j+1) y (-3) <;> rfl

/-- Exact inverse-cone chart, with no negative-time row. -/
theorem actual_cone_chart (y : CAConfig) (hA : AlternatingCenter y)
    (o : Nat) (ho : caEvolve o y 0=false) (n : Nat) :
    ∀ j, cone (actualEndpoint y o) n j=
      cellPair y (o+2*j+n+1) (-(n+2 : Nat)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j
    match n with
    | 0 => exact actual_boundary y hA o ho j
    | 1 =>
      simp only [cone]
      rw [actual_boundary y hA o ho (j+1)]
      unfold actualEndpoint
      have h1 : o+2*(j+1)+1=(o+2*j+2)+1 := by omega
      have h2 : o+2*j+1+1=o+2*j+2 := by omega
      rw [h1,h2]
      exact pair_backward y (o+2*j+2) (-1)
    | n+2 =>
      simp only [cone]
      rw [ih n (by omega),ih (n+1) (by omega)]
      have h1 : o+2*(j+1)+(n+1)+1=(o+2*(j+1)+n+1)+1 := by omega
      have h2 : -((n+1+2 : Nat) : Int) = -((n+2 : Nat) : Int)-1 := by omega
      have h3 : o+2*j+(n+2)+1=o+2*(j+1)+n+1 := by omega
      have h4 : -((n+2+2 : Nat) : Int) = -((n+2 : Nat) : Int)-2 := by omega
      rw [h1,h2,h3,h4]
      exact pair_backward y (o+2*(j+1)+n+1) (-((n+2 : Nat) : Int))

theorem actual_peel_chart (y : CAConfig) (hA : AlternatingCenter y)
    (o : Nat) (ho : caEvolve o y 0=false) (d : Nat) :
    ∀ t, peelPow d (inverse (actualEndpoint y o)) t=
      cellPair y (o+t+1) (-(2*d+t+2 : Nat)) := by
  induction d with
  | zero =>
    intro t
    simpa only [peelPow,inverse,Nat.mul_zero,Nat.zero_add,Nat.add_zero] using
      actual_cone_chart y hA o ho t 0
  | succ d ih =>
    intro t
    simp only [peelPow,peel,ih]
    have h1 : o+(t+1)+1=(o+t+1)+1 := by omega
    have h2 : -((2*d+(t+1)+2 : Nat) : Int) = -((2*d+t+2 : Nat) : Int)-1 := by omega
    have h3 : -((2*(d+1)+t+2 : Nat) : Int) = -((2*d+t+2 : Nat) : Int)-2 := by omega
    rw [h1,h2,h3]
    exact pair_backward y (o+t+1) (-((2*d+t+2 : Nat) : Int))

theorem actual_endpoint_binary (y : CAConfig) (hA : AlternatingCenter y)
    (o : Nat) (ho : caEvolve o y 0=false) (j : Nat) :
    binary (actualEndpoint y o j) := by
  let t := o+2*j+2
  have ht : t=o+2*(j+1) := by dsimp [t]; omega
  have hc0 : caEvolve t y 0=false := by
    rw [ht]
    exact center_even y (center_flip y hA) o ho (j+1)
  have hc1 : caEvolve (t+1) y 0=true := by rw [ht]; exact center_odd y hA o ho (j+1)
  have hc2 : caEvolve ((t+1)+1) y 0=false := by rw [center_flip y hA,hc1]; rfl
  have hp := pin y (t+1) hc1 hc2
  rw [caEvolve_succ] at hp
  change xor (caEvolve t y (-2)) (caEvolve t y (-1) || caEvolve t y 0)=true at hp
  rw [hc0] at hp
  simp only [Bool.or_false] at hp
  exact encode_xor_binary _ _ hp

theorem pair_one_requires_right (y : CAConfig) (t : Nat)
    (hc0 : caEvolve t y 0=false) (hc1 : caEvolve (t+1) y 0=true)
    (hp : cellPair y t (-1)=1) : caEvolve t y 1=true := by
  have hl := encode_one_high_false _ _ hp
  rw [caEvolve_succ] at hc1
  change xor (caEvolve t y (-1)) (caEvolve t y 0 || caEvolve t y 1)=true at hc1
  simpa only [hl,hc0,Bool.false_or,Bool.false_xor] using hc1

theorem right_no11 (y : CAConfig) (t : Nat)
    (hc0 : caEvolve t y 0=false) (hc1 : caEvolve (t+1) y 0=true) :
    ¬(caEvolve t y 1=true ∧ caEvolve (t+2) y 1=true) := by
  intro ⟨hr0,hr2⟩
  have hr1 : caEvolve (t+1) y 1=true := by
    rw [caEvolve_succ]
    change xor (caEvolve t y 0) (caEvolve t y 1 || caEvolve t y 2)=true
    simp [hc0,hr0]
  have hi : t+2=(t+1)+1 := by omega
  rw [hi,caEvolve_succ] at hr2
  change xor (caEvolve (t+1) y 0)
    (caEvolve (t+1) y 1 || caEvolve (t+1) y 2)=true at hr2
  simp [hc1,hr1] at hr2

theorem actual_endpoint_hardcore (y : CAConfig) (hA : AlternatingCenter y)
    (o : Nat) (ho : caEvolve o y 0=false) : HardCore (actualEndpoint y o) := by
  refine ⟨actual_endpoint_binary y hA o ho,?_⟩
  intro j ⟨ha,hb⟩
  let t := o+2*j+2
  have he (k : Nat) : caEvolve (o+2*k) y 0=false := center_even y (center_flip y hA) o ho k
  have hc0 : caEvolve t y 0=false := by
    have hi : t=o+2*(j+1) := by dsimp [t]; omega
    rw [hi]; exact he (j+1)
  have hc1 : caEvolve (t+1) y 0=true := by rw [center_flip y hA,hc0]; rfl
  have hc2 : caEvolve (t+2) y 0=false := by
    have hi : t+2=(t+1)+1 := by omega
    rw [hi,center_flip y hA,hc1]; rfl
  have hc3 : caEvolve ((t+2)+1) y 0=true := by rw [center_flip y hA,hc2]; rfl
  have ha' : caEvolve t y 1=true := pair_one_requires_right y t hc0 hc1 ha
  have hb' : cellPair y (t+2) (-1)=1 := by
    have hi : t+2=o+2*(j+1)+2 := by dsimp [t]; omega
    rw [hi]; exact hb
  exact right_no11 y t hc0 hc1 ⟨ha',pair_one_requires_right y (t+2) hc2 hc3 hb'⟩

theorem actual_endpoint_finite_rank (y : CAConfig) (hA : AlternatingCenter y)
    (hL : LeftFinite y) (o : Nat) (ho : caEvolve o y 0=false) :
    ∃ d, ∀ t, peelPow d (inverse (actualEndpoint y o)) t=0 := by
  obtain ⟨a,ha,hz⟩ := hL
  let d := a.natAbs+o+2
  have habs : a≤(a.natAbs : Int) := Int.le_natAbs
  refine ⟨d,?_⟩
  intro t
  rw [actual_peel_chart y hA o ho d t]
  unfold cellPair
  have h1 : -((2*d+t+2 : Nat) : Int) < -(a+((o+t+1 : Nat) : Int)) := by dsimp [d]; omega
  have h2 : -((2*d+t+2 : Nat) : Int)-1 < -(a+((o+t+1 : Nat) : Int)) := by dsimp [d]; omega
  rw [(front y a ha hz (o+t+1)).1 _ h1,(front y a ha hz (o+t+1)).1 _ h2]
  rfl

theorem constant_separator_excludes_alternating (hs : ConstantTailSeparator)
    (y : CAConfig) (hL : LeftFinite y) (hA : AlternatingCenter y) : False := by
  obtain ⟨o,ho⟩ : ∃ o, caEvolve o y 0=false := by
    by_cases h : caEvolve 0 y 0=false
    · exact ⟨0,h⟩
    · refine ⟨1,?_⟩
      rw [show 1=0+1 by rfl,center_flip y hA]
      cases hc : caEvolve 0 y 0 <;> simp_all
  obtain ⟨d,hd⟩ := actual_endpoint_finite_rank y hA hL o ho
  exact separator_excludes_finite_peel_rank hs (actualEndpoint y o)
    (actual_endpoint_hardcore y hA o ho) d 0 (by intro t _; exact hd t)

/-- The remaining ladder implication, on the actual Rule 30 definitions. -/
theorem sep_implies_period_two (hs : OrbitSeparator) : Rule30AlternatingTraceBridge.PeriodTwoExcluded := by
  intro y hn hf hA
  exact constant_separator_excludes_alternating
    (orbit_separator_implies_constant_separator hs) y
    (Rule30AlternatingTraceBridge.leftFinite_of_nonzero_finiteSupport y hn hf) hA

theorem rw_implies_period_two (hrw : RW) : Rule30AlternatingTraceBridge.PeriodTwoExcluded :=
  sep_implies_period_two (rw_implies_orbit_separator hrw)

theorem bwh_small_implies_period_two (hb : BWH) (hs : SmallRW) :
    Rule30AlternatingTraceBridge.PeriodTwoExcluded := rw_implies_period_two (bwh_implies_rw hb hs)

/-- The imported torus is a checked counterexample to omitting finite origin. -/
theorem finite_origin_control :
    ∃ y : CAConfig, Nonzero y ∧ AlternatingCenter y ∧ ¬FiniteSupport y := by
  exact ⟨Rule30AlternatingTraceBridge.fromPattern Rule30AlternatingTraceBridge.seedPattern,
    Rule30AlternatingTraceBridge.seed_nonzero, Rule30AlternatingTraceBridge.seed_alternatingCenter,
    Rule30AlternatingTraceBridge.seed_not_finiteSupport⟩


/-! ## The official center column -/

theorem center_not_eventually_period_two_of_sep (hs : OrbitSeparator) :
    ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  Rule30AlternatingTraceBridge.center_not_eventually_period_two_of_excluded
    (sep_implies_period_two hs)

theorem center_not_eventually_period_two_of_rw (hrw : RW) :
    ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  Rule30AlternatingTraceBridge.center_not_eventually_period_two_of_excluded
    (rw_implies_period_two hrw)

theorem center_not_eventually_period_two_of_bwh (hb : BWH) (hs : SmallRW) :
    ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  Rule30AlternatingTraceBridge.center_not_eventually_period_two_of_excluded
    (bwh_small_implies_period_two hb hs)

/-! ## Discharging `SmallRW` via `Rule30WedgeBridge.smallRW` -/

/-- **`BWH` Alone Implies `OrbitSeparator` (`bwh_implies_orbit_separator`):** `BWH` alone implies
`OrbitSeparator`. -/
theorem bwh_implies_orbit_separator (hb : BWH) : OrbitSeparator :=
  rw_implies_orbit_separator (bwh_implies_rw_unconditional hb)

/-- **`BWH` Alone Implies `PeriodTwoExcluded` (`bwh_implies_period_two`):** discharges `SmallRW`
from `bwh_small_implies_period_two`. -/
theorem bwh_implies_period_two (hb : BWH) : Rule30AlternatingTraceBridge.PeriodTwoExcluded :=
  bwh_small_implies_period_two hb smallRW

/-- **`BWH` Alone Excludes Eventual Period Two of the Center Column
(`center_not_eventually_period_two_of_bwh_unconditional`):** discharges `SmallRW` from
`center_not_eventually_period_two_of_bwh`. -/
theorem center_not_eventually_period_two_of_bwh_unconditional (hb : BWH) :
    ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  center_not_eventually_period_two_of_bwh hb smallRW

end Rule30SEPToPeriodTwo
end Ruliology.CellularAutomata
