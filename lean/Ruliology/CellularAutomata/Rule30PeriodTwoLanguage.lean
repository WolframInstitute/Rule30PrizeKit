module

public import Ruliology.CellularAutomata.Rule30PeriodFourSkeleton
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Period 2: the language of the bad class of the right strip

If the center column is `(01)^∞` from time `T` (white at the times `T + 2k`), the strip of columns
`1..b` of the true right half eventually stays in the bad rank class of a bad-class certificate
(`Rule30PeriodFourSkeleton.Cert.sound_bad`, masked Jen). This module adds a kernel-checkable
statement about the *paths* inside the bad class: `occurs C bad pat = false` means that no path of
the strip relaxation that stays in the bad class reads the word `pat` in column `1` at consecutive
white phases (subset simulation over bitmasks of strips, `simMask`). `no_pattern` combines the two:
eventually, column `1` at the white times never spells `pat`.

`Rule30PeriodTwoWidth5` and `Rule30PeriodTwoWidth6` apply it at the strip widths `5` and `6`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoLanguage

open Rule30Jen Rule30StripCertificates Rule30PeriodFourSkeleton

/-- Node `(φ, s)` lies in the bad class. -/
def inBad (C : Cert) (bad φ : Nat) (s : List Bool) : Bool := C.rk φ s == bad

/-- The contribution of the two inputs `x1`, `x2` to the white-to-white successors of `s` that stay
in the bad class and read `y` in column `1`. -/
def cont (C : Cert) (bad : Nat) (s : List Bool) (y x1 x2 : Bool) : Nat :=
  let s1 := lin3 (C.wAt 0 :: (s ++ [x1]))
  let s2 := lin3 (C.wAt 1 :: (s1 ++ [x2]))
  if (inBad C bad 1 s1 && inBad C bad 0 s2 && (s2.headD false == y)) = true then 2 ^ encList s2 else 0

def succMask (C : Cert) (bad : Nat) (s : List Bool) (y : Bool) : Nat :=
  cont C bad s y false false ||| cont C bad s y false true ||| cont C bad s y true false |||
    cont C bad s y true true

/-- One step of the subset simulation: from the strips in `S` (phase `0`) to their successors two
steps later inside the bad class, reading `y`. -/
def occStep (C : Cert) (bad : Nat) (S : Nat) (y : Bool) : List (List Bool) → Nat
  | [] => 0
  | s :: rest => (if S.testBit (encList s) = true then succMask C bad s y else 0) |||
      occStep C bad S y rest

/-- The phase-`0` strips of the bad class that read `y`. -/
def startMask (C : Cert) (bad : Nat) (y : Bool) : List (List Bool) → Nat
  | [] => 0
  | s :: rest => (if (inBad C bad 0 s && (s.headD false == y)) = true then 2 ^ encList s else 0) |||
      startMask C bad y rest

def simMask (C : Cert) (bad : Nat) : Nat → List Bool → Nat
  | S, [] => S
  | S, y :: ys => simMask C bad (occStep C bad S y (allLists C.b)) ys

/-- Some path inside the bad class reads `pat` at consecutive white phases. -/
def occurs (C : Cert) (bad : Nat) : List Bool → Bool
  | [] => true
  | y :: ys => simMask C bad (startMask C bad y (allLists C.b)) ys != 0

/-! ## Soundness -/

theorem testBit_ite (c : Prop) [Decidable c] (a i : Nat) :
    (if c then a else 0).testBit i = (decide c && a.testBit i) := by
  by_cases h : c <;> simp [h]

theorem startMask_bit (C : Cert) (bad : Nat) (y : Bool) : ∀ (L : List (List Bool)) (s : List Bool),
    s ∈ L → inBad C bad 0 s = true → s.headD false = y →
    (startMask C bad y L).testBit (encList s) = true
  | [], s, h, _, _ => by simp at h
  | s' :: rest, s, h, h1, h2 => by
    simp only [startMask, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h
    · left
      have hc : (inBad C bad 0 s && (s.headD false == y)) = true := by rw [h1, h2]; simp
      rw [testBit_ite, decide_eq_true hc, Bool.true_and, Nat.testBit_two_pow_self]
    · right; exact startMask_bit C bad y rest s h h1 h2

theorem occStep_bit (C : Cert) (bad : Nat) (S : Nat) (y : Bool) :
    ∀ (L : List (List Bool)) (s s2 : List Bool) (x1 x2 : Bool), s ∈ L → S.testBit (encList s) = true →
    inBad C bad 1 (lin3 (C.wAt 0 :: (s ++ [x1]))) = true →
    s2 = lin3 (C.wAt 1 :: (lin3 (C.wAt 0 :: (s ++ [x1])) ++ [x2])) →
    inBad C bad 0 s2 = true → s2.headD false = y →
    (occStep C bad S y L).testBit (encList s2) = true
  | [], s, _, _, _, h, _, _, _, _, _ => by simp at h
  | s' :: rest, s, s2, x1, x2, h, hS, h1, hs2, h2, hy => by
    simp only [occStep, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h
    · left
      rw [testBit_ite, decide_eq_true hS, Bool.true_and]
      have hc : (cont C bad s y x1 x2).testBit (encList s2) = true := by
        subst hs2
        have hcond : (inBad C bad 1 (lin3 (C.wAt 0 :: (s ++ [x1]))) &&
            inBad C bad 0 (lin3 (C.wAt 1 :: (lin3 (C.wAt 0 :: (s ++ [x1])) ++ [x2]))) &&
            ((lin3 (C.wAt 1 :: (lin3 (C.wAt 0 :: (s ++ [x1])) ++ [x2]))).headD false == y)) = true := by
          rw [h1, h2, hy]; simp
        unfold cont
        simp only
        rw [testBit_ite, decide_eq_true hcond, Bool.true_and, Nat.testBit_two_pow_self]
      unfold succMask
      simp only [Nat.testBit_or]
      cases x1 <;> cases x2 <;> simp [hc]
    · right; exact occStep_bit C bad S y rest s s2 x1 x2 h hS h1 hs2 h2 hy

/-- **Soundness of `occurs`.** Let the center column be `C.w`-periodic from `T` with `C.w = [false, true]`,
and let the strip stay in the bad class from `T'` on. If `occurs C bad pat = false`, then from any
white time `t ≥ T'`, column `1` at the times `t, t + 2, …` does not spell `pat`. -/
theorem no_pattern (C : Cert) (bad : Nat) (hw : C.w = [false, true]) (T T' : Nat) (hTT : T ≤ T')
    (h : ∀ t, T ≤ t → cell t 0 = C.wAt ((t - T) % C.P))
    (hbad : ∀ t, T' ≤ t → C.rk ((t - T) % C.P) (rowR t C.b) = bad) (hb : 0 < C.b)
    (pat : List Bool) (hocc : occurs C bad pat = false) (t : Nat) (ht : T' ≤ t) (hph : (t - T) % 2 = 0) :
    ¬ ∀ i, i < pat.length → cell (t + 2 * i) 1 = pat.getD i false := by
  intro hm
  have hP : C.P = 2 := by unfold Cert.P; rw [hw]; rfl
  have hw0 : C.wAt 0 = false := by unfold Cert.wAt; rw [hw]; rfl
  have hw1 : C.wAt 1 = true := by unfold Cert.wAt; rw [hw]; rfl
  -- strips along the white times
  have hstep : ∀ u, T' ≤ u → (u - T) % 2 = 0 →
      rowR (u + 1) C.b = lin3 (C.wAt 0 :: (rowR u C.b ++ [cell u ((C.b : Int) + 1)])) ∧
      rowR (u + 2) C.b = lin3 (C.wAt 1 :: (rowR (u + 1) C.b ++ [cell (u + 1) ((C.b : Int) + 1)])) ∧
      inBad C bad 1 (rowR (u + 1) C.b) = true ∧ inBad C bad 0 (rowR (u + 2) C.b) = true ∧
      inBad C bad 0 (rowR u C.b) = true := by
    intro u hu hpu
    have e0 : cell u 0 = C.wAt 0 := by rw [h u (by omega), hP, hpu]
    have e1 : cell (u + 1) 0 = C.wAt 1 := by
      rw [h (u + 1) (by omega), hP, show (u + 1 - T) % 2 = 1 by omega]
    refine ⟨by rw [rowR_succ, e0], by rw [rowR_succ, e1], ?_, ?_, ?_⟩
    · have := hbad (u + 1) (by omega)
      rw [hP, show (u + 1 - T) % 2 = 1 by omega] at this
      unfold inBad; rw [this]; simp
    · have := hbad (u + 2) (by omega)
      rw [hP, show (u + 2 - T) % 2 = 0 by omega] at this
      unfold inBad; rw [this]; simp
    · have := hbad u hu
      rw [hP, hpu] at this
      unfold inBad; rw [this]; simp
  have hhead : ∀ u, (rowR u C.b).headD false = cell u 1 := fun u => rowR_head u C.b hb
  -- the simulation keeps the true strip
  have key : ∀ (ys : List Bool) (S u : Nat), T' ≤ u → (u - T) % 2 = 0 →
      S.testBit (encList (rowR u C.b)) = true →
      (∀ i, i < ys.length → cell (u + 2 * (i + 1)) 1 = ys.getD i false) →
      (simMask C bad S ys).testBit (encList (rowR (u + 2 * ys.length) C.b)) = true := by
    intro ys
    induction ys with
    | nil => intro S u _ _ hS _; exact hS
    | cons y ys ih =>
      intro S u hu hpu hS hys
      obtain ⟨e1, e2, b1, b2, _⟩ := hstep u hu hpu
      have hnext := occStep_bit C bad S y (allLists C.b) (rowR u C.b) (rowR (u + 2) C.b)
        (cell u ((C.b : Int) + 1)) (cell (u + 1) ((C.b : Int) + 1))
        (allLists_mem _ _ (rowR_length u C.b)) hS (by rw [← e1]; exact b1) (by rw [e2, e1]) b2
        (by rw [hhead]; have := hys 0 (by simp); simpa using this)
      have := ih _ (u + 2) (by omega) (by omega) hnext (fun i hi => by
        have := hys (i + 1) (by simp; omega)
        rw [show u + 2 + 2 * (i + 1) = u + 2 * (i + 1 + 1) by omega]
        simpa using this)
      show (simMask C bad (occStep C bad S y (allLists C.b)) ys).testBit _ = true
      rw [show u + 2 * (y :: ys).length = u + 2 + 2 * ys.length by simp; omega]
      exact this
  cases pat with
  | nil => simp [occurs] at hocc
  | cons y ys =>
    have hS0 := startMask_bit C bad y (allLists C.b) (rowR t C.b) (allLists_mem _ _ (rowR_length t C.b))
      (hstep t ht hph).2.2.2.2 (by rw [hhead]; have := hm 0 (by simp); simpa using this)
    have := key ys _ t ht hph hS0 (fun i hi => by
      have := hm (i + 1) (by simp; omega)
      simpa using this)
    simp only [occurs] at hocc
    rw [show (simMask C bad (startMask C bad y (allLists C.b)) ys) = 0 by
      revert hocc; cases (simMask C bad (startMask C bad y (allLists C.b)) ys) == 0 <;> simp] at this
    simp at this

/-! ### Zero-Mask Absorption, Semigroup Composition of `simMask`, and Prefix Forbidden-Word Inheritance -/

/-- **Zero-Mask Absorption of `occStep` (`occStep_zero`):** stepping the empty subset mask `0` yields `0`
for any strip list `L`. -/
theorem occStep_zero (C : Cert) (bad : Nat) (y : Bool) :
    ∀ L : List (List Bool), occStep C bad 0 y L = 0
  | [] => rfl
  | s :: rest => by
    simp [occStep, occStep_zero C bad y rest]

/-- **Zero-Mask Absorption of `simMask` (`simMask_zero`):** simulating any word `ys` from the empty
subset mask `0` yields `0`. -/
theorem simMask_zero (C : Cert) (bad : Nat) :
    ∀ ys : List Bool, simMask C bad 0 ys = 0
  | [] => rfl
  | y :: ys => by
    simp [simMask, occStep_zero, simMask_zero C bad ys]

/-- **Concatenation Semigroup Law of `simMask` (`simMask_append`):** simulating `ys1 ++ ys2` from mask
`S` is identical to simulating `ys2` from `simMask C bad S ys1`. -/
theorem simMask_append (C : Cert) (bad : Nat) :
    ∀ (ys1 ys2 : List Bool) (S : Nat),
      simMask C bad S (ys1 ++ ys2) = simMask C bad (simMask C bad S ys1) ys2
  | [], ys2, S => rfl
  | y :: ys1, ys2, S => by
    simp [simMask, simMask_append C bad ys1 ys2]

/-- **Singleton Pattern Characterization of `occurs` (`occurs_singleton`):** a 1-letter pattern `[y]`
occurs if and only if `startMask C bad y (allLists C.b) != 0`. -/
theorem occurs_singleton (C : Cert) (bad : Nat) (y : Bool) :
    occurs C bad [y] = (startMask C bad y (allLists C.b) != 0) := rfl

/-- **Forbidden-Prefix Propagation (`occurs_append_eq_false`):** if `occurs C bad pat1 = false`, then
every extension `pat1 ++ pat2` also satisfies `occurs C bad (pat1 ++ pat2) = false`. -/
theorem occurs_append_eq_false (C : Cert) (bad : Nat) (pat1 pat2 : List Bool)
    (h : occurs C bad pat1 = false) :
    occurs C bad (pat1 ++ pat2) = false := by
  cases pat1 with
  | nil => simp [occurs] at h
  | cons y ys1 =>
    simp only [occurs, List.cons_append, simMask_append] at h ⊢
    have h0 : simMask C bad (startMask C bad y (allLists C.b)) ys1 = 0 := by
      revert h
      cases simMask C bad (startMask C bad y (allLists C.b)) ys1 == 0 <;> simp
    rw [h0, simMask_zero]
    rfl

/-- **Occurrence Prefix Monotonicity (`occurs_prefix_of_occurs`):** if `pat1 ++ pat2` occurs in the
bad class, then its prefix `pat1` also occurs in the bad class. -/
theorem occurs_prefix_of_occurs (C : Cert) (bad : Nat) (pat1 pat2 : List Bool)
    (h : occurs C bad (pat1 ++ pat2) = true) :
    occurs C bad pat1 = true := by
  cases hp : occurs C bad pat1
  · rw [occurs_append_eq_false C bad pat1 pat2 hp] at h
    contradiction
  · rfl

end Rule30PeriodTwoLanguage
end Ruliology.CellularAutomata
