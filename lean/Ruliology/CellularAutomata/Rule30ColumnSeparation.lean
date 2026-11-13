module

public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Pairwise distinct complete column traces of the single-seed pattern

For every pair of integers p != q, an observation at time at most
max(|p|,|q|)+18 distinguishes their columns. First arrival distinguishes
different distances from the seed. Mirror columns -m and m differ by time
m+18, using certified 20-bit edge windows: the left window is 4-periodic
after time 20 and the right window is 256-periodic from the start. Checking
all 256 phase classes gives the uniform bound for arbitrarily large m.

This concerns complete traces starting at time zero. It does not exclude
eventual equality, prove temporal nonperiodicity, or solve a prize problem.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30ColumnSeparation

open Rule30Jen Rule30Diagonals

def step (left : Bool) (a : Nat) : Nat :=
  (if left then (a <<< 2) ^^^ ((a <<< 1) ||| a)
   else a ^^^ ((a <<< 1) ||| (a <<< 2))) % 2^20

def front (left : Bool) : Nat → Nat
  | 0 => 1
  | t+1 => step left (front left t)

theorem bit_initial (j : Nat) : (1:Nat).testBit j = decide (j=0) := by
  have h := Nat.testBit_bool_toNat true j
  simpa using h

theorem right_bits : ∀ t j, j<20 → (front false t).testBit j = R j t
  | 0,j,hj => by
    rw [front,bit_initial]
    by_cases hz : j=0
    · subst hz; rfl
    · simp [R,cell,hz]
  | t+1,j,hj => by
    simp only [front,step,Bool.false_eq_true,ite_false,Nat.testBit_mod_two_pow,
      hj,decide_true,Bool.true_and,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft]
    rcases j with _ | _ | j
    · simp [right_bits t 0 (by omega),R_zero]
    · simp [right_bits t 0 (by omega),right_bits t 1 (by omega),R_zero,R_one_succ]
    · simp only [show 1≤j+2 by omega,show 2≤j+2 by omega,decide_true,Bool.true_and,
        show j+2-1=j+1 by omega,show j+2-2=j by omega]
      rw [right_bits t (j+2) hj,right_bits t (j+1) (by omega),right_bits t j (by omega)]
      exact (R_step j t).symm

theorem left_bits : ∀ t j, j<20 → (front true t).testBit j = D j t
  | 0,j,hj => by
    rw [front,bit_initial]
    by_cases hz : j=0
    · subst hz; rfl
    · simp [D,cell,hz]
  | t+1,j,hj => by
    simp only [front,step,ite_true,Nat.testBit_mod_two_pow,
      hj,decide_true,Bool.true_and,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft]
    rcases j with _ | _ | j
    · simp [left_bits t 0 (by omega),D_zero]
    · simp [left_bits t 0 (by omega),D_zero,D_one]
    · simp only [show 1≤j+2 by omega,show 2≤j+2 by omega,decide_true,Bool.true_and,
        show j+2-1=j+1 by omega,show j+2-2=j by omega]
      rw [left_bits t (j+2) hj,left_bits t (j+1) (by omega),left_bits t j (by omega)]
      exact (D_step j t).symm

theorem front_agree (left : Bool) (a b : Nat) (h : front left a = front left b) :
    ∀ n, front left (a+n) = front left (b+n)
  | 0 => h
  | n+1 => by
    rw [show a+(n+1)=(a+n)+1 by omega,show b+(n+1)=(b+n)+1 by omega,front,front,
      front_agree left a b h n]

set_option maxHeartbeats 0 in
theorem right_cycle : front false 256 = 1 := by decide

set_option maxHeartbeats 0 in
theorem left_cycle : front true 24 = front true 20 := by decide

theorem right_periodic (t : Nat) : front false (t+256) = front false t := by
  have h := front_agree false 256 0 right_cycle t
  simpa [Nat.add_comm] using h

theorem left_periodic (t : Nat) (ht : 20≤t) : front true (t+4) = front true t := by
  have h := front_agree true 24 20 left_cycle (t-20)
  simpa [show 24+(t-20)=t+4 by omega,show 20+(t-20)=t by omega] using h

theorem right_reduce (t : Nat) : front false t = front false (t%256) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases ht : t<256
    · rw [Nat.mod_eq_of_lt ht]
    · rw [show t=(t-256)+256 by omega,right_periodic,ih (t-256) (by omega)]
      congr 1
      omega

theorem left_reduce (t : Nat) (ht : 20≤t) : front true t = front true (20+t%4) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases hsmall : t<24
    · congr 1; omega
    · rw [show t=(t-4)+4 by omega,left_periodic (t-4) (by omega),ih (t-4) (by omega) (by omega)]
      congr 1
      omega

def diagnostic : Bool :=
  (List.range 256).all fun r => (List.range 19).any fun j =>
    decide ((front true (20+(r+j)%4)).testBit j ≠ (front false ((r+j)%256)).testBit j)

set_option maxHeartbeats 0 in
theorem diagnostic_ok : diagnostic = true := by decide

def smallDiagnostic : Bool :=
  (List.range 19).all fun k => (List.range 19).any fun j =>
    decide ((front true (k+1+j)).testBit j ≠ (front false (k+1+j)).testBit j)

set_option maxHeartbeats 0 in
theorem small_diagnostic_ok : smallDiagnostic = true := by decide

theorem small_witness (m : Nat) (hm : 0<m) (hsmall : m<20) :
    ∃ j, j<19 ∧ (front true (m+j)).testBit j ≠ (front false (m+j)).testBit j := by
  have h := List.all_eq_true.mp small_diagnostic_ok (m-1) (List.mem_range.mpr (by omega))
  obtain ⟨j,hj,he⟩ := List.any_eq_true.mp h
  refine ⟨j,List.mem_range.mp hj,?_⟩
  simpa [show m-1+1=m by omega] using he

theorem large_witness (m : Nat) (hm : 20≤m) :
    ∃ j, j<19 ∧ (front true (m+j)).testBit j ≠ (front false (m+j)).testBit j := by
  have h := List.all_eq_true.mp diagnostic_ok (m%256) (List.mem_range.mpr (by omega))
  obtain ⟨j,hj,he⟩ := List.any_eq_true.mp h
  refine ⟨j,List.mem_range.mp hj,?_⟩
  rw [left_reduce (m+j) (by omega),right_reduce]
  have h4 : (m+j)%4 = (m%256+j)%4 := by omega
  have h256 : (m+j)%256 = (m%256+j)%256 := by omega
  rw [h4,h256]
  exact of_decide_eq_true he

/-- An unbounded family: every pair of distinct mirror columns differs no
later than 18 steps after the first black cell reaches those columns. -/
theorem mirror_columns_distinguishable (m : Nat) (hm : 0<m) :
    ∃ j, j≤18 ∧ cell (m+j) (-(m:Int)) ≠ cell (m+j) (m:Int) := by
  obtain ⟨j,hj,he⟩ := if hs : m<20 then small_witness m hm hs else large_witness m (by omega)
  refine ⟨j,by omega,?_⟩
  rw [left_bits (m+j) j (by omega),right_bits (m+j) j (by omega)] at he
  simpa only [D,R,show (j:Int)-((m+j:Nat):Int)=-(m:Int) by omega,
    show ((m+j:Nat):Int)-(j:Int)=(m:Int) by omega] using he

theorem first_arrival_black (p : Int) : cell p.natAbs p = true := by
  generalize hm : p.natAbs = m
  rcases Int.natAbs_eq_iff.mp hm with hp | hp
  · rw [hp]; simpa [R] using R_zero m
  · rw [hp]; exact cell_left_edge m

theorem white_before_arrival (t : Nat) (p : Int) (ht : t<p.natAbs) : cell t p = false := by
  rcases Int.natAbs_eq_iff.mp (rfl : p.natAbs=p.natAbs) with hp | hp
  · rw [hp]; exact cell_eq_false_of_gt t _ (by omega)
  · rw [hp]; exact cell_eq_false_of_lt t _ (by omega)

/-- Every two different spatial columns of the single-seed pattern have
different complete traces, with an explicit observation-time bound. This
does not assert anything about eventual equality or temporal periodicity. -/
theorem columns_distinguishable (p q : Int) (hne : p≠q) :
    ∃ t, t≤max p.natAbs q.natAbs+18 ∧ cell t p ≠ cell t q := by
  rcases Nat.lt_trichotomy p.natAbs q.natAbs with hlt | heq | hgt
  · refine ⟨p.natAbs,by omega,?_⟩
    rw [first_arrival_black,white_before_arrival _ _ hlt]
    decide
  · have hop : p = -q := (Int.natAbs_eq_natAbs_iff.mp heq).resolve_left hne
    cases q with
    | ofNat m =>
      change p≠(m:Int) at hne
      change p.natAbs=m at heq
      change p=-(m:Int) at hop
      have hm : 0<m := by omega
      obtain ⟨j,hj,hw⟩ := mirror_columns_distinguishable m hm
      refine ⟨m+j,by omega,?_⟩
      simpa only [hop,Int.ofNat_eq_natCast] using hw
    | negSucc m =>
      obtain ⟨j,hj,hw⟩ := mirror_columns_distinguishable (m+1) (by omega)
      refine ⟨m+1+j,by omega,?_⟩
      simpa [hop,Int.negSucc_eq] using Ne.symm hw
  · refine ⟨q.natAbs,by omega,?_⟩
    rw [first_arrival_black,white_before_arrival _ _ hgt]
    decide

theorem columns_injective {p q : Int} (h : ∀ t, cell t p = cell t q) : p=q := by
  by_cases heq : p=q
  · exact heq
  · obtain ⟨t,_,ht⟩ := columns_distinguishable p q heq
    exact False.elim (ht (h t))

/-! ### Exact first-arrival characterization `t = p.natAbs` and finite-horizon trace injectivity -/

/-- **Exact Characterization of the First Black Arrival Time `t = p.natAbs` (`first_black_time_iff_natAbs_and_prefix_distance`).** -/
theorem first_black_time_iff_natAbs_and_prefix_distance (p q : Int) (t : Nat) :
    ((cell t p = true ∧ ∀ s, s < t → cell s p = false) ↔ t = p.natAbs) ∧
    ((∀ s, s ≤ min p.natAbs q.natAbs → cell s p = cell s q) → p.natAbs = q.natAbs) := by
  refine ⟨⟨fun ⟨hb, hw⟩ => ?_, fun h => ?_⟩, fun hagree => ?_⟩
  · rcases Nat.lt_trichotomy t p.natAbs with hlt | heq | hgt
    · rw [white_before_arrival t p hlt] at hb; cases hb
    · exact heq
    · have := hw p.natAbs hgt
      rw [first_arrival_black p] at this; cases this
  · subst h
    exact ⟨first_arrival_black p, fun s hs => white_before_arrival s p hs⟩
  · rcases Nat.lt_trichotomy p.natAbs q.natAbs with hlt | heq | hgt
    · have h1 := hagree p.natAbs (by omega)
      rw [first_arrival_black p, white_before_arrival p.natAbs q hlt] at h1
      cases h1
    · exact heq
    · have h1 := hagree q.natAbs (by omega)
      rw [white_before_arrival q.natAbs p hgt, first_arrival_black q] at h1
      cases h1

/-- **Finite-Horizon Trace Injectivity Equivalence (`columns_eq_iff_bounded_agree`):**
two spatial columns `p, q : Int` of the single-seed pattern coincide (`p = q`) if and only if
their traces agree through time `max p.natAbs q.natAbs + 18`. -/
theorem columns_eq_iff_bounded_agree (p q : Int) :
    p = q ↔ ∀ t, t ≤ max p.natAbs q.natAbs + 18 → cell t p = cell t q := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    by_cases heq : p = q
    · exact heq
    · obtain ⟨t, ht, hne⟩ := columns_distinguishable p q heq
      exact False.elim (hne (h t ht))

end Ruliology.CellularAutomata.Rule30ColumnSeparation
