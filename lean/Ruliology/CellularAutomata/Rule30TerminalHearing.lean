module

public import Ruliology.CellularAutomata.Rule30TerminalCensus

/-!
# A wall bound sets the pair density in the terminal census

Galindo's `Rule30TerminalCensus` bounds the single seed's horizontal words by disjoint age pairs. Any uniform bound K (p/q)^n on
the OR words beside a wall, with `p^b < 4^a q^b`, makes a mean of a/b pairs at unbounded widths sufficient for Problem 1
(`problem1_of_hearing_and_pairs`). With the five-cell 39/32 of `Rule30HorizontalDiversity`, one pair per seven positions suffices
(`one_in_seven`); Galindo's census used 3/20. Whether the single seed has that many pairs is open.

Contributed by Gareth Herbert with Claude (Anthropic) and GPT (OpenAI).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30TerminalHearing
open Ruliology.CellularAutomata Rule30Realization Rule30HorizontalDiversity Rule30TerminalCensus

/-- Galindo's abundance hypothesis with an arbitrary rational threshold a/b. -/
def PairDensity (a b : Nat) : Prop := ∀ L : Nat, ∃ s ≥ L, ∃ N > 0, ∃ c : Census s N,
  a * (s*N) ≤ b * pairSum c.pairs s

private theorem vocabulary_at_density {s N a b : Nat} (c : Census s N) (hN : 0 < N)
    (hm : a * (s*N) ≤ b * pairSum c.pairs s) : (4^a)^s ≤ (H s)^b := by
  have h : ((4^a)^s)^N ≤ ((H s)^b)^N := calc
    _ = 4^(a*(s*N)) := by rw [← Nat.pow_mul,← Nat.pow_mul]
    _ ≤ 4^(b*pairSum c.pairs s) := Nat.pow_le_pow_right (by decide) hm
    _ = (4^(pairSum c.pairs s))^b := by rw [← Nat.pow_mul,Nat.mul_comm]
    _ ≤ ((H s)^N)^b := Nat.pow_le_pow_left (vocabulary_budget c) _
    _ = _ := Nat.pow_right_comm ..
  exact Nat.le_of_not_lt (fun hh => (Nat.not_lt_of_ge h) (Nat.pow_lt_pow_left hh (by omega)))

private theorem growth_gap (u v A : Nat) (hu : 0 < u) (hv : u < v) :
    ∃ L : Nat, ∀ s ≥ L, A * u^s < v^s := by
  -- Galindo's elementary rate-gap argument, here with arbitrary bases u < v.
  have linear (s : Nat) : (s+u)*u^s ≤ u*v^s := by
    induction s with
    | zero => simp
    | succ k ih =>
      have step : (k+1+u)*u ≤ (u+1)*(k+u) := calc
        _ = (k+u)*u + u := by rw [show k+1+u=(k+u)+1 by omega,Nat.add_mul,Nat.one_mul]
        _ ≤ (k+u)*u + (k+u) := Nat.add_le_add_left (by omega) _
        _ = _ := by rw [Nat.add_mul u 1 (k+u),Nat.one_mul,Nat.mul_comm u (k+u)]
      calc
        _ = ((k+1+u)*u)*u^k := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ ((u+1)*(k+u))*u^k := Nat.mul_le_mul_right _ step
        _ = (u+1)*((k+u)*u^k) := Nat.mul_assoc ..
        _ ≤ v*(u*v^k) := Nat.mul_le_mul (by omega) ih
        _ = _ := by rw [Nat.pow_succ]; ac_rfl
  refine ⟨u*A+1,?_⟩
  intro s hs
  apply Nat.lt_of_not_ge
  intro low
  have h := Nat.le_trans (linear s) (Nat.mul_le_mul_left u low)
  rw [← Nat.mul_assoc] at h
  exact (Nat.not_lt_of_ge h) (Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos hu))

/-- The horizontal half of LookaheadHearing.Consequences, stated using only core Lean. -/
def HorizontalCap (K p q : Nat) : Prop := ∀ {T P : Nat}, 0 < P →
  (∀ t, T ≤ t → Rule30Jen.cell (t+P) 0 = Rule30Jen.cell t 0) →
  ∀ w, H w ≤ T + P * (K*p^w/q^w)

/-- For any uniform wall bound K(p/q)^n, a census mean a/b with 4^a > (p/q)^b
at unbounded widths excludes every eventual period of the singleton centre. -/
theorem problem1_of_hearing_and_pairs {K p q a b : Nat} (hq : 0 < q) (hpq : q ≤ p)
    (cap : HorizontalCap K p q) (gap : p^b < 4^a * q^b) (ab : PairDensity a b) : Rule30Prize.Problem1 := by
  rintro ⟨T,P,hP,per⟩
  have hcap := cap hP per
  let A := T+P*K
  obtain ⟨L,hL⟩ := growth_gap (p^b) (4^a*q^b) (A^b) (Nat.pow_pos (by omega)) gap
  obtain ⟨s,hs,N,hN,c,hm⟩ := ab L
  have hH : H s * q^s ≤ A * p^s := calc
    _ ≤ (T+P*(K*p^s/q^s))*q^s := Nat.mul_le_mul_right _ (hcap s)
    _ = T*q^s + P*((K*p^s/q^s)*q^s) := by rw [Nat.add_mul,Nat.mul_assoc]
    _ ≤ T*p^s + P*(K*p^s) := Nat.add_le_add
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpq s)) (Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
    _ = _ := by dsimp [A]; rw [Nat.add_mul,Nat.mul_assoc]
  have impossible : (4^a*q^b)^s ≤ A^b * (p^b)^s := calc
    _ = (4^a)^s * (q^s)^b := by rw [Nat.mul_pow,Nat.pow_right_comm q b s]
    _ ≤ (H s)^b * (q^s)^b := Nat.mul_le_mul_right _ (vocabulary_at_density c hN hm)
    _ = (H s * q^s)^b := (Nat.mul_pow ..).symm
    _ ≤ (A * p^s)^b := Nat.pow_le_pow_left hH _
    _ = _ := by rw [Nat.mul_pow,Nat.pow_right_comm p s b]
  exact (Nat.not_lt_of_ge impossible) (hL s hs)

/-- One pair per seven age-depth positions suffices, using Galindo's own kernel-checked
five-cell 39/32 bound. Abundance at this density is an open hypothesis. -/
theorem one_in_seven (h : PairDensity 1 7) : Rule30Prize.Problem1 :=
  problem1_of_hearing_and_pairs (K := 9) (p := 39) (q := 32) (by decide) (by decide)
    (fun hp per => Rule30HorizontalDiversity.five_cell_count hp per) (by decide) h

end Ruliology.CellularAutomata.Rule30TerminalHearing
