module

public import Ruliology.CellularAutomata.Rule30DrivenLeftDepthTwo

/-! # A necessary periodicity test for a uniform inverse-edge age

Every predecessor on the driven negative half has another predecessor there by left permutivity.
If depth two is exact for n+1 inverse ticks, the first parent's width-w edge band has an n-step
history under the autonomous band map, provided the cone stays inside the wall. For n ≥ 2^w
the band is therefore on a cycle. A periodic output band can be realized at depth two at any
chosen age of its full width minus two. Together these facts imply that uniform ages for all
inverse depths force every recurrent black-edged output to have at most one full-line parent. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DrivenParentBand

open Rule30Jen Rule30DrivenLeft Rule30EveryKLine Rule30DrivenLeftDepthTwo Rule30UniversalLeftSide

private def backBits (y : Int → Bool) : Nat → Bool
  | 0 => false
  | 1 => false
  | n + 2 => xor (y (-(n : Int) - 1)) (backBits y (n + 1) || backBits y n)

private def back (y : Int → Bool) (p : Int) := backBits y (-p).toNat

private theorem step_back (y : Int → Bool) (p : Int) (hp : p < 0) : stepLine (back y) p = y p := by
  let n := (-p - 1).toNat
  have hn : (n : Int) = -p-1 := by change (((-p-1).toNat : Nat) : Int) = _; omega
  have a : (-(p-1)).toNat = n+2 := by omega
  have b : (-p).toNat = n+1 := by omega
  have c : (-(p+1)).toNat = n := by omega
  simp only [stepLine, back, a, b, c, backBits, show -(n : Int)-1 = p by omega, rule]
  cases y p <;> cases backBits y (n+1) <;> cases backBits y n <;> rfl

private def past (z : Int → Bool) : Nat → Int → Bool
  | 0 => z
  | i+1 => back (past z i)

private theorem cone (z : Int → Bool) (n : Nat) : ∀ j ≤ n, ∀ p : Int, p+j < 0 →
    Rule30Realization.evol (past z n) j p = past z (n-j) p := by
  intro j
  induction j with
  | zero => intro hj p hp; rfl
  | succ j ih =>
    intro hj p hp
    rw [evol_succ]
    unfold stepLine
    rw [ih (by omega) (p-1) (by omega), ih (by omega) p (by omega),
      ih (by omega) (p+1) (by omega), show n-j = (n-(j+1))+1 by omega]
    exact step_back _ p (by omega)

/-- Any one-step parent of the aged row has a band with an actual n-step autonomous history. -/
theorem parent_band_history {n w t : Nat} (h : ExactAt (n+1) 2 t) (room : w+n ≤ t)
    (wall : Nat → Bool) (s z : Int → Bool) (black : s (-2) = true)
    (white : ∀ p, p < -2 → s p = false)
    (parent : ∀ p, p < 0 → stepLine z p = L wall s t p) :
    ∃ v < 2^w, bandK z (-1-(t : Int)) w = rowAt w v n := by
  let chain : Nat → Int → Bool
    | 0 => L wall s t
    | i+1 => past z i
  have steps : ∀ i, i < n+1 → ∀ p, p < 0 → stepLine (chain (i+1)) p = chain i p := by
    intro i _ p hp
    cases i with
    | zero => exact parent p hp
    | succ i => exact step_back _ p hp
  obtain ⟨_, hz⟩ := h wall s chain black (by simpa using white) (fun _ _ => rfl) steps
  let lo : Int := -1-(t : Int)+n
  have outside : ∀ p, p < lo → past z n p = false := by
    intro p hp
    exact hz p (by dsimp [lo] at hp; omega)
  refine ⟨bandK (past z n) lo w, bandK_lt _ _ _, ?_⟩
  rw [← bandK_evol outside w n]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bandK, testBit_bandK]
  by_cases hj : j < w
  · simp only [hj, decide_true, Bool.true_and]
    rw [show lo - (n : Int) + j = -1-(t : Int)+j by dsimp [lo]; omega,
      cone z n n (Nat.le_refl _) _ (by omega), Nat.sub_self]
    rfl
  · simp [hj]

/-- If n ≥ 2^w, every one-step parent band in the stated cone already lies on a cycle. -/
theorem parent_band_on_cycle {n w t : Nat} (h : ExactAt (n+1) 2 t) (room : w+n ≤ t)
    (long : 2^w ≤ n) (wall : Nat → Bool) (s z : Int → Bool) (black : s (-2) = true)
    (white : ∀ p, p < -2 → s p = false)
    (parent : ∀ p, p < 0 → stepLine z p = L wall s t p) :
    ∃ q, 0 < q ∧ rowAt w (bandK z (-1-(t : Int)) w) q = bandK z (-1-(t : Int)) w := by
  obtain ⟨v,hv,history⟩ := parent_band_history h room wall s z black white parent
  rw [history]
  exact on_cycle w v hv n long

open Rule30Realization Rule30FiniteConfigs Rule30FiniteDiagonals

/-- Every finite edge band is on a cycle. The periods may depend on the width. -/
def RecurrentAt (y : Int → Bool) (edge : Int) : Prop :=
  ∀ w, ∃ q, 0 < q ∧ rowAt w (bandK y edge w) q = bandK y edge w

private theorem restrict_line (x : Int → Bool) : ∀ (t : Nat) (p : Int), p ≤ 0 →
    L (fun i => evol x i 2) (fun j => x (j+2)) t p = evol x t (p+2) := by
  intro t
  induction t with
  | zero =>
    intro p hp
    by_cases he : p = 0
    · subst p; rw [L_col0]; rfl
    · rw [L_zero (by omega)]; rfl
  | succ t ih =>
    intro p hp
    by_cases he : p = 0
    · subst p; rw [L_col0]; rfl
    · rw [L_succ (by omega), ih (p-1) (by omega), ih p hp, ih (p+1) (by omega), evol_succ]
      unfold stepLine
      rw [show p-1+2 = p+2-1 by omega, show p+1+2 = p+2+1 by omega]

/-- A periodic width-(t+2) band gives a depth-two realization of the whole negative half at age t. -/
theorem realize_recurrent (y : Int → Bool) (black : y 0 = true) (white : ∀ p, p < 0 → y p = false)
    (t : Nat) (per : ∃ q, 0 < q ∧ rowAt (t+2) (bandK y 0 (t+2)) q = bandK y 0 (t+2)) :
    ∃ wall s, s (-2) = true ∧ (∀ p, p < -2 → s p = false) ∧
      ∀ p, p < 0 → L wall s t p = y (p+2+t) := by
  obtain ⟨q,hq,cycle⟩ := per
  let v := bandK y 0 (t+2)
  let a := t*q-t
  let u := rowAt (t+2) v a
  have backTo : rowAt (t+2) u t = v := by
    change rowAt (t+2) (rowAt (t+2) v a) t = v
    rw [← rowAt_add]
    have hmul : t ≤ t*q := Nat.le_mul_of_pos_right t hq
    rw [show a+t = t*q by dsimp [a]; omega]
    simpa [rowAt] using rowAt_add_mul cycle 0 t
  have bit0 : ∀ i, (rowAt (t+2) u i).testBit 0 = u.testBit 0 := by
    intro i; induction i with
    | zero => rfl
    | succ i ih => rw [rowAt, stepK_bit_zero (by omega), ih]
  have ub : u.testBit 0 = true := by
    rw [← bit0 t, backTo]
    change (bandK y 0 (t+2)).testBit 0 = true
    rw [testBit_bandK]
    simp [black]
  refine ⟨fun i => evol (ofRow u) i 2, fun p => ofRow u (p+2), ?_, ?_, ?_⟩
  · simpa [ofRow] using ub
  · intro p hp; exact ofRow_left u (p+2) (by omega)
  · intro p hp
    rw [restrict_line _ _ _ (by omega)]
    by_cases h : p+2+t < 0
    · rw [white _ h]
      exact evol_eq_false_of_lt (ofRow_left u) t _ (by omega)
    · let j := (p+2+t).toNat
      have hj : (j : Int) = p+2+t := by dsimp [j]; omega
      have hj' : j < t+2 := by omega
      have e := Ld_ofRow (K := t+2) (by omega) u t j hj'
      rw [backTo] at e
      simp only [Ld, v, testBit_bandK, hj', decide_true, Bool.true_and, Int.zero_add] at e
      rwa [hj, show 0-(t : Int)+(p+2+t) = p+2 by omega] at e

/-- If every inverse depth has an exact age, every full-line parent of a recurrent black-edged
row has periodic bands at the retreating edge. -/
theorem recurrent_parent_of_every_k (uniform : ∀ k, ∃ T, ExactAt k 2 T)
    (y z : Int → Bool) (black : y 0 = true) (white : ∀ p, p < 0 → y p = false)
    (recur : RecurrentAt y 0) (parent : stepLine z = y) : RecurrentAt z 1 := by
  intro w
  obtain ⟨T,h⟩ := uniform (2^w+1)
  let t := T+w+2^w
  have ht : T ≤ t := Nat.le_trans (Nat.le_add_right T w) (Nat.le_add_right _ _)
  have later : ExactAt (2^w+1) 2 t := exactAt_of_two h (m := 2) (t := t) (by decide) ht (by omega)
  obtain ⟨wall,s,hs,hw,matchRow⟩ := realize_recurrent y black white t (recur (t+2))
  let z' := fun (p : Int) => z (p+2+t)
  have hp : ∀ p, p < 0 → stepLine z' p = L wall s t p := by
    intro p hn
    rw [matchRow p hn, ← parent]
    simp only [stepLine, z', show p-1+2+(t : Int) = p+2+t-1 by omega,
      show p+1+2+(t : Int) = p+2+t+1 by omega]
  have cyc := parent_band_on_cycle later (w := w) (by dsimp [t]; omega)
    (Nat.le_refl _) wall s z' hs hw hp
  have eq : bandK z' (-1-(t : Int)) w = bandK z 1 w := by
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [testBit_bandK, z', show -1-(t : Int)+j+2+t = 1+(j : Int) by omega]
  rwa [eq] at cyc

/-- The one-tick threshold alone forces the true parent edge for any recurrent output. -/
theorem parent_edge_of_one {T : Nat} (h : ExactAt 1 2 T) (y z : Int → Bool)
    (black : y 0 = true) (white : ∀ p, p < 0 → y p = false)
    (recur : RecurrentAt y 0) (parent : stepLine z = y) :
    z 1 = true ∧ ∀ p, p < 1 → z p = false := by
  obtain ⟨wall,s,hs,hw,matchRow⟩ := realize_recurrent y black white T (recur (T+2))
  let chain : Nat → Int → Bool
    | 0 => L wall s T
    | _+1 => fun p => z (p+2+T)
  have steps : ∀ i, i < 1 → ∀ p, p < 0 → stepLine (chain (i+1)) p = chain i p := by
    intro i hi p hp
    obtain rfl : i = 0 := by omega
    change stepLine (fun j => z (j+2+T)) p = L wall s T p
    rw [matchRow p hp, ← parent]
    simp only [stepLine, show p-1+2+(T : Int) = p+2+T-1 by omega,
      show p+1+2+(T : Int) = p+2+T+1 by omega]
  obtain ⟨hit,clear⟩ := h wall s chain hs (by simpa using hw) (fun _ _ => rfl) steps
  constructor
  · change z (-2-(T : Int)+1+2+T) = true at hit
    simpa only [show -2-(T : Int)+1+2+T = 1 by omega] using hit
  · intro p hp
    have e := clear (p-2-T) (by omega)
    change z (p-2-T+2+T) = false at e
    simpa only [show p-2-(T : Int)+2+T = p by omega] using e

private theorem cycle_cancel {w a b : Nat} (pa : ∃ q, 0 < q ∧ rowAt w a q = a)
    (pb : ∃ q, 0 < q ∧ rowAt w b q = b) (eq : stepK w a = stepK w b) : a = b := by
  obtain ⟨p,hp,ap⟩ := pa
  obtain ⟨q,hq,bq⟩ := pb
  have e : rowAt w a (p*q) = rowAt w b (p*q) := by
    have pos := Nat.mul_pos hp hq
    rw [show p*q = 1+(p*q-1) by omega, rowAt_add, rowAt_add w b]
    exact congrArg (fun v => rowAt w v (p*q-1)) eq
  have ea : rowAt w a (p*q) = a := by simpa [Nat.mul_comm, rowAt] using rowAt_add_mul ap 0 q
  have eb : rowAt w b (p*q) = b := by simpa [rowAt] using rowAt_add_mul bq 0 p
  exact ea.symm.trans (e.trans eb)

/-- If every inverse depth has a depth-two threshold, a recurrent black-edged output has
at most one full-line Rule 30 parent. Both candidate parents are arbitrary configurations. -/
theorem unique_parent_of_every_k (uniform : ∀ k, ∃ T, ExactAt k 2 T)
    (y a b : Int → Bool) (black : y 0 = true) (white : ∀ p, p < 0 → y p = false)
    (recur : RecurrentAt y 0) (pa : stepLine a = y) (pb : stepLine b = y) : a = b := by
  obtain ⟨T,h⟩ := uniform 1
  have wa := (parent_edge_of_one h y a black white recur pa).2
  have wb := (parent_edge_of_one h y b black white recur pb).2
  have ra := recurrent_parent_of_every_k uniform y a black white recur pa
  have rb := recurrent_parent_of_every_k uniform y b black white recur pb
  have bands (w : Nat) : bandK a 1 w = bandK b 1 w := by
    apply cycle_cancel (ra w) (rb w)
    rw [← bandK_step a 1 w wa, ← bandK_step b 1 w wb, pa, pb]
  funext p
  by_cases hp : p < 1
  · rw [wa p hp, wb p hp]
  · let j := (p-1).toNat
    have hj : 1+(j : Int) = p := by dsimp [j]; omega
    have e := congrArg (fun v : Nat => v.testBit j) (bands (j+1))
    simpa only [testBit_bandK, Nat.lt_succ_self, decide_true, Bool.true_and, hj] using e

end Ruliology.CellularAutomata.Rule30DrivenParentBand
