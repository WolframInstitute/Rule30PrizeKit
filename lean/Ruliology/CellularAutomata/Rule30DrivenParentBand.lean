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

/-! ### Unconditional recurrent ancestor edges, parent band cycles, and the `ExactAt → TargetAt` bridge -/

open Rule30ZeroBoundary Rule30ZeroBoundary.IntegerForm Rule30EveryKStatement

private theorem ancestor_edge_of_exactAt {k T : Nat} (h : ExactAt k 2 T)
    (y z : Int → Bool) (edgePos : Int)
    (black : y edgePos = true) (white : ∀ p, p < edgePos → y p = false)
    (recur : RecurrentAt y edgePos) (anc : evol z k = y) :
    z (edgePos + (k : Int)) = true ∧ ∀ p, p < edgePos + (k : Int) → z p = false := by
  let y0 : Int → Bool := fun p => y (p + edgePos)
  have hy0_b : y0 0 = true := by simpa [y0] using black
  have hy0_w : ∀ p, p < 0 → y0 p = false := fun p hp => white (p + edgePos) (by omega)
  have hband_eq : ∀ w, bandK y0 0 w = bandK y edgePos w := by
    intro w; apply Nat.eq_of_testBit_eq; intro j
    simp only [testBit_bandK, y0, show (0 : Int) + (j : Int) + edgePos = edgePos + (j : Int) by omega]
  have hrec0 : RecurrentAt y0 0 := fun w => by rw [hband_eq w]; exact recur w
  obtain ⟨wall, s, hs, hw, matchRow⟩ := realize_recurrent y0 hy0_b hy0_w T (hrec0 (T + 2))
  let chain : Nat → Int → Bool := fun i p =>
    if i = 0 then L wall s T p else evol z (k - i) (p + edgePos + 2 + (T : Int))
  have hsteps : ∀ i, i < k → ∀ p, p < 0 → stepLine (chain (i + 1)) p = chain i p := by
    intro i hi p hp
    by_cases hi0 : i = 0
    · subst hi0
      simp only [chain, ↓reduceIte, show (1 : Nat) ≠ 0 by decide]
      rw [matchRow p hp]
      have hkeq : k = (k - 1) + 1 := by omega
      have hev : y (p + 2 + (T : Int) + edgePos) = stepLine (evol z (k - 1)) (p + edgePos + 2 + (T : Int)) := by
        rw [← anc, hkeq, evol_succ]; congr 1; omega
      dsimp [y0]; rw [hev]
      simp only [stepLine, show p - 1 + edgePos + 2 + (T : Int) = p + edgePos + 2 + (T : Int) - 1 by omega,
        show p + 1 + edgePos + 2 + (T : Int) = p + edgePos + 2 + (T : Int) + 1 by omega]
    · simp only [chain, hi0, Nat.succ_ne_zero, ↓reduceIte]
      have hsub : k - i = (k - (i + 1)) + 1 := by omega
      rw [hsub, evol_succ]
      simp only [stepLine, show p - 1 + edgePos + 2 + (T : Int) = p + edgePos + 2 + (T : Int) - 1 by omega,
        show p + 1 + edgePos + 2 + (T : Int) = p + edgePos + 2 + (T : Int) + 1 by omega]
  by_cases hk0 : k = 0
  · subst hk0
    have heq : z = y := anc
    subst heq
    simpa using And.intro black white
  · obtain ⟨hit, clear⟩ := h wall s chain hs (by simpa using hw) (fun _ _ => by simp [chain]) hsteps
    simp only [chain, hk0, ↓reduceIte, Nat.sub_self, evol] at hit clear
    refine ⟨?_, fun p hp => ?_⟩
    · have he1 : -((2 : Nat) : Int) - (T : Int) + (k : Int) + edgePos + 2 + (T : Int) = edgePos + (k : Int) := by omega
      rw [he1] at hit; exact hit
    · have hc := clear (p - edgePos - 2 - (T : Int)) (by omega)
      have he2 : p - edgePos - 2 - (T : Int) + edgePos + 2 + (T : Int) = p := by omega
      rw [he2] at hc; exact hc

/-- **Unconditional 1-, 2-, and 3-Step Full-Line Ancestor Edges of Recurrent Rows (`recurrent_ancestors_edge_up_to_three`).** -/
theorem recurrent_ancestors_edge_up_to_three (y z : Int → Bool) (edgePos : Int)
    (black : y edgePos = true) (white : ∀ p, p < edgePos → y p = false)
    (recur : RecurrentAt y edgePos) :
    (stepLine z = y → z (edgePos + 1) = true ∧ ∀ p, p < edgePos + 1 → z p = false) ∧
    (evol z 2 = y → z (edgePos + 2) = true ∧ ∀ p, p < edgePos + 2 → z p = false) ∧
    (evol z 3 = y → z (edgePos + 3) = true ∧ ∀ p, p < edgePos + 3 → z p = false) :=
  ⟨fun h1 => ancestor_edge_of_exactAt exactAt_one_eight_and_two_twentyFour_sharp.1.1 y z edgePos black white recur h1,
   fun h2 => ancestor_edge_of_exactAt exactAt_one_eight_and_two_twentyFour_sharp.2.1 y z edgePos black white recur h2,
   fun h3 => ancestor_edge_of_exactAt exactAt_three_thirtyOne_sharp.1 y z edgePos black white recur h3⟩

/-- **Unconditional 1-Step and 2-Step Autonomous Histories of Driven Parent Bands (`parent_band_history_one_and_two`).** -/
theorem parent_band_history_one_and_two :
    (∀ {w t : Nat}, 24 ≤ t → w + 1 ≤ t → ∀ (wall : Nat → Bool) (s z : Int → Bool),
      s (-2) = true → (∀ p, p < -2 → s p = false) → (∀ p, p < 0 → stepLine z p = L wall s t p) →
      ∃ v < 2 ^ w, bandK z (-1 - (t : Int)) w = rowAt w v 1) ∧
    (∀ {w t : Nat}, 31 ≤ t → w + 2 ≤ t → ∀ (wall : Nat → Bool) (s z : Int → Bool),
      s (-2) = true → (∀ p, p < -2 → s p = false) → (∀ p, p < 0 → stepLine z p = L wall s t p) →
      ∃ v < 2 ^ w, bandK z (-1 - (t : Int)) w = rowAt w v 2) :=
  ⟨fun {w t} ht hroom wall s z hb hw hp =>
    parent_band_history (exactAt_zero_and_age_mono.2 2 24 t (by decide) ht
      exactAt_one_eight_and_two_twentyFour_sharp.2.1) hroom wall s z hb hw hp,
   fun {w t} ht hroom wall s z hb hw hp =>
    parent_band_history (exactAt_zero_and_age_mono.2 3 31 t (by decide) ht
      exactAt_three_thirtyOne_sharp.1) hroom wall s z hb hw hp⟩

/-- **Unconditional Width-1 Parent Band Periodicity from Age `31` (`parent_band_width_one_on_cycle_from_31`).** -/
theorem parent_band_width_one_on_cycle_from_31 {t : Nat} (ht : 31 ≤ t)
    (wall : Nat → Bool) (s z : Int → Bool) (black : s (-2) = true)
    (white : ∀ p, p < -2 → s p = false)
    (parent : ∀ p, p < 0 → stepLine z p = L wall s t p) :
    ∃ q, 0 < q ∧ rowAt 1 (bandK z (-1 - (t : Int)) 1) q = bandK z (-1 - (t : Int)) 1 :=
  parent_band_on_cycle
    (exactAt_zero_and_age_mono.2 3 31 t (by decide) ht exactAt_three_thirtyOne_sharp.1)
    (by omega) (by decide) wall s z black white parent

private def zeroBackChain (T : Nat) : Nat → Int → Bool
  | 0 => L (fun _ => false) (start2 false) T
  | i + 1 => back (zeroBackChain T i)

private theorem le_add_one_of_exactAt {k T : Nat} (h : ExactAt k 2 T) : k ≤ T + 1 := by
  by_cases hk0 : k = 0
  · omega
  · have hs := start2_cells false
    have hsteps : ∀ i, i < k → ∀ p, p < 0 → stepLine (zeroBackChain T (i + 1)) p = zeroBackChain T i p := by
      intro i _ p hp; exact step_back (zeroBackChain T i) p hp
    obtain ⟨hit, _⟩ := h (fun _ => false) (start2 false) (zeroBackChain T) hs.1 hs.2.2 (fun _ _ => rfl) hsteps
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    apply Classical.byContradiction
    intro hgt
    have hzero_nonneg : back (zeroBackChain T j) (-((2 : Nat) : Int) - (T : Int) + ((j + 1 : Nat) : Int)) = false := by
      unfold back
      rw [Int.toNat_of_nonpos (by omega)]; rfl
    simp only [zeroBackChain] at hit
    rw [hzero_nonneg] at hit; exact Bool.noConfusion hit

private def mirrorRow (f : Nat → Bool) (p : Int) : Bool :=
  if p < 0 then f (-p).toNat else false

private theorem L_zero_wall_eq_zrow (f : Nat → Bool) :
    ∀ (t : Nat) (p : Int), p ≤ 0 → L (fun _ => false) (mirrorRow f) t p = zrow f t (-p).toNat
  | 0, p, hp => by
    by_cases hp0 : p < 0
    · rw [L_zero hp0, zrow_zero_of_pos f (by omega)]; simp [mirrorRow, hp0]
    · have heq : p = 0 := by omega
      subst heq; simp [L_col0, zrow_wall]
  | t + 1, p, hp => by
    by_cases hp0 : p < 0
    · obtain ⟨i, hi⟩ : ∃ i : Nat, (-p).toNat = i + 1 := ⟨(-p).toNat - 1, by omega⟩
      rw [L_succ hp0, L_zero_wall_eq_zrow f t (p - 1) (by omega),
          L_zero_wall_eq_zrow f t p (by omega), L_zero_wall_eq_zrow f t (p + 1) (by omega),
          hi, zrow_succ]
      have e1 : (-(p - 1)).toNat = i + 2 := by omega
      have e2 : (-(p + 1)).toNat = i := by omega
      rw [e1, e2]; rfl
    · have heq : p = 0 := by omega
      subst heq; simp [L_col0, zrow_wall]

private theorem stepLine_mirror_zrow (V : Nat → Bool) (u : Nat) (p : Int) (hp : p < 0) :
    stepLine (mirrorRow (zrow V u)) p = mirrorRow (zrow V (u + 1)) p := by
  obtain ⟨i, hi⟩ : ∃ i : Nat, (-p).toNat = i + 1 := ⟨(-p).toNat - 1, by omega⟩
  have h1 : mirrorRow (zrow V u) (p - 1) = zrow V u (i + 2) := by
    have hp1 : p - 1 < 0 := by omega
    have e1 : (-(p - 1)).toNat = i + 2 := by omega
    simp [mirrorRow, hp1, e1]
  have h2 : mirrorRow (zrow V u) p = zrow V u (i + 1) := by simp [mirrorRow, hp, hi]
  have h3 : mirrorRow (zrow V u) (p + 1) = zrow V u i := by
    by_cases hp1 : p + 1 < 0
    · have e3 : (-(p + 1)).toNat = i := by omega
      simp [mirrorRow, hp1, e3]
    · have hi0 : i = 0 := by omega
      subst hi0; simp [mirrorRow, hp1, zrow_wall]
  unfold stepLine
  rw [h1, h2, h3]
  simp [mirrorRow, hp, hi, rule, zrow_succ]

private theorem top_of_nz {X : Nat} (hX : X ≠ 0) : Top X X.log2 :=
  ⟨Nat.testBit_log2 hX, fun i hi => Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega)))⟩

private theorem build_zrow_history (k : Nat) (E : Nat → Bool) (bits : Fin k → Bool) :
    ∃ L_row : Nat → Bool, (∀ x, 1 ≤ x → zrow L_row k x = E x) ∧
      ∀ i : Fin k, zrow L_row i.val 1 = bits i := by
  induction k with
  | zero => exact ⟨E, fun _ hx => zrow_zero_of_pos E hx, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨P, endP, wall⟩ := ih (fun i => bits i.succ)
    let L_row := Rule30ZeroBoundary.back (bits 0) P
    have shift (i x : Nat) : zrow L_row (i + 1) x = zrow P i x := by
      rw [Nat.add_comm i 1, zrow_shift]
      exact zrow_congr (zrow_back (bits 0) P) i x
    refine ⟨L_row, fun x hx => (shift k x).trans (endP x hx), fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact (shift j.val 1).trans (wall j)

/-- **Universal Bridge `ExactAt k 2 T → TargetAt k (T + 1)` (`targetAt_of_exactAt`).** -/
theorem targetAt_of_exactAt {k T : Nat} (hT : 2 ≤ T) (hEx : ExactAt k 2 T) :
    TargetAt k (T + 1) := by
  have hkT : k ≤ T + 1 := le_add_one_of_exactAt hEx
  have hphys : PhysicalEdge k (T + 1) := by
    intro L_row m t hm hLm hfin ht V hV
    have hEx_mt : ExactAt k m t := by
      by_cases hm2 : 2 ≤ m
      · exact (two_classes k T hT).1.mpr hEx m t hm2 (by omega)
      · have hm1 : m = 1 := by omega
        subst hm1; exact (two_classes k T hT).2.mpr hEx t ht
    let chain : Nat → Int → Bool := fun i => mirrorRow (zrow V (k - i))
    have hs1 : mirrorRow L_row (-(m : Int)) = true := by
      have hneg : -(m : Int) < 0 := by omega
      have htnm : (-( -(m : Int))).toNat = m := by omega
      simp only [mirrorRow, hneg, ↓reduceIte, htnm, hLm]
    have hs0 : ∀ p, p < -(m : Int) → mirrorRow L_row p = false := by
      intro p hp; simp only [mirrorRow, show p < 0 by omega, ↓reduceIte]; exact hfin _ (by omega)
    have hx0 : ∀ p, p < 0 → chain 0 p = L (fun _ => false) (mirrorRow L_row) t p := by
      intro p hp
      rw [L_zero_wall_eq_zrow L_row t p (by omega)]
      simp only [chain, Nat.sub_zero, mirrorRow, hp, ↓reduceIte]
      exact hV (-p).toNat (by omega)
    have hsteps : ∀ i, i < k → ∀ p, p < 0 → stepLine (chain (i + 1)) p = chain i p := by
      intro i hi p hp
      dsimp [chain]
      rw [stepLine_mirror_zrow V (k - (i + 1)) p hp, show k - (i + 1) + 1 = k - i by omega]
    obtain ⟨hit, clear⟩ := hEx_mt (fun _ => false) (mirrorRow L_row) chain hs1 hs0 hx0 hsteps
    have hedge_pos : 1 ≤ m + t - k := by omega
    have hp_edge : -(m : Int) - (t : Int) + (k : Int) < 0 := by omega
    simp only [chain, Nat.sub_self, mirrorRow, hp_edge, ↓reduceIte] at hit
    have htn : (-(-(m : Int) - (t : Int) + (k : Int))).toNat = m + t - k := by omega
    rw [htn, zrow_zero_of_pos V hedge_pos] at hit
    refine ⟨hit, fun idx hidx => ?_⟩
    have hc := clear (-(idx : Int)) (by omega)
    have hneg_i : -(idx : Int) < 0 := by omega
    have htn_i : (-( -(idx : Int))).toNat = idx := by omega
    simp only [chain, Nat.sub_self, mirrorRow, hneg_i, ↓reduceIte, htn_i] at hc
    rw [zrow_zero_of_pos V (by omega)] at hc
    exact hc
  have hfin_pred : FinitePredecessor k (T + 1) := by
    intro Y t hY ht L_pred hpre
    let m := Y.log2 + 1
    have htopY := top_of_nz hY
    have hLm : rowOfNat Y m = true := htopY.1
    have hLfin : ∀ i, m < i → rowOfNat Y i = false := by
      intro i hi; obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact htopY.2 j (by dsimp [m] at hi; omega)
    have hed := hphys (rowOfNat Y) m t (by dsimp [m]; omega) hLm hLfin ht L_pred
      (fun i hi => (hpre i hi).trans (zrow_rowOfNat Y t i).symm)
    let e := m + t - k
    have he_pos : 1 ≤ e := by dsimp [e, m]; omega
    let A := natOfRow L_pred e
    have rep : ∀ x, 1 ≤ x → rowOfNat A x = L_pred x := rowOfNat_natOfRow hed.2
    have image : iter F k A = iter F t Y := by
      apply Nat.eq_of_testBit_eq; intro i
      exact (zrow_rowOfNat A k (i + 1)).symm.trans ((zrow_congr rep k (i + 1)).trans (hpre (i + 1) (by omega)))
    refine ⟨A, rep, image, ?_, fun i hi => ?_⟩
    · have ha := rep e he_pos
      obtain ⟨j, hj⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
      rw [hj] at ha; change A.testBit j = L_pred (j + 1) at ha
      have heq : Y.log2 + t - k = j := by dsimp [e, m] at hj; omega
      rw [heq, ha, ← hj]; exact hed.1
    · have hgt : e < i + 1 := by dsimp [e, m]; omega
      exact (rep (i + 1) (by omega)).trans (hed.2 (i + 1) hgt)
  refine ⟨hphys, hfin_pred, fun Y t hY ht bits => ?_⟩
  obtain ⟨L_pred, pre, trace⟩ := build_zrow_history k (rowOfNat (iter F t Y)) bits
  obtain ⟨A, rep, image, top⟩ := hfin_pred Y t hY ht L_pred pre
  exact ⟨A, image, top, fun i => (zrow_rowOfNat A i.val 1).symm.trans
    ((zrow_congr rep i.val 1).trans (trace i))⟩

/-- **Unconditional `TargetAt 1 9`, `TargetAt 2 25`, and `TargetAt 3 32` (`targetAt_one_nine_two_twentyFive_three_thirtyTwo`).** -/
theorem targetAt_one_nine_two_twentyFive_three_thirtyTwo :
    TargetAt 1 9 ∧ TargetAt 2 25 ∧ TargetAt 3 32 :=
  ⟨targetAt_of_exactAt (by decide) exactAt_one_eight_and_two_twentyFour_sharp.1.1,
   targetAt_of_exactAt (by decide) exactAt_one_eight_and_two_twentyFour_sharp.2.1,
   targetAt_of_exactAt (by decide) exactAt_three_thirtyOne_sharp.1⟩

end Ruliology.CellularAutomata.Rule30DrivenParentBand
