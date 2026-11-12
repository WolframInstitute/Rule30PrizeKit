module

public import Ruliology.CellularAutomata.Rule30WhitePulse
public import Ruliology.CellularAutomata.Rule30ZeroPredecessor
public import Ruliology.CellularAutomata.Rule30WhitePadding

@[expose] public section

/-!
Endpoint-conditioned backward strip certificates. A checked chain of
predecessor implications forces the state before a terminal block into a
known set. Combining it with a stable zero-driven reachable set excludes
white-padding families for arbitrarily many padding phases.
-/
namespace Ruliology.CellularAutomata.Rule30BackwardTube
open Rule30Jen Rule30Realization Rule30StripCertificates Rule30FiniteStrips
open Rule30WhitePulse Rule30ZeroPredecessor Rule30WhitePadding

def preCheck (K : Nat) (a : Bool) (Q R : Nat) : Bool :=
  allBelow (fun s =>
    (! R.testBit (stripStep K a false s) || Q.testBit s) &&
    (! R.testBit (stripStep K a true s) || Q.testBit s)) (2^K)

theorem preCheck_sound {K Q R s : Nat} {a z : Bool}
    (h : preCheck K a Q R = true) (hs : s < 2^K)
    (ht : R.testBit (stripStep K a z s) = true) : Q.testBit s = true := by
  have hh := allBelow_spec h s hs
  rw [Bool.and_eq_true] at hh
  cases z
  · have hh := hh.1
    rw [ht, Bool.not_true, Bool.false_or] at hh
    exact hh
  · have hh := hh.2
    rw [ht, Bool.not_true, Bool.false_or] at hh
    exact hh

theorem enc_unique {x : Int → Bool} {K t : Nat} {i : Int} {r s : Nat}
    (hr : Rule30FiniteStrips.Enc x K t i r) (hs : Rule30FiniteStrips.Enc x K t i s) : r = s := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < K
  · rw [hr.2 j hj, hs.2 j hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr.1 (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs.1 (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem encRow_step (x : Int → Bool) (K t : Nat) (i : Int) :
    Rule30FiniteStrips.encRow x (t+1) i K =
      stripStep K (evol x t i) (evol x t (i+1+K)) (Rule30FiniteStrips.encRow x t i K) :=
  enc_unique (Rule30FiniteStrips.enc_encRow K (t+1) i) (Rule30FiniteStrips.enc_step (Rule30FiniteStrips.enc_encRow K t i))

theorem enc_backward {x : Int → Bool} {K t Q R : Nat} {i : Int} {a : Bool}
    (h : preCheck K a Q R = true) (ha : evol x t i = a)
    (hR : R.testBit (Rule30FiniteStrips.encRow x (t+1) i K) = true) :
    Q.testBit (Rule30FiniteStrips.encRow x t i K) = true := by
  rw [encRow_step, ha] at hR
  exact preCheck_sound h (Rule30FiniteStrips.enc_encRow K t i).1 hR

theorem encRow_zero_of_prefix {x : Int → Bool} {K t : Nat} {i : Int}
    (h : ∀ j, j < K → evol x t (i+1+j) = false) : Rule30FiniteStrips.encRow x t i K = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj : j < K
  · rw [(Rule30FiniteStrips.enc_encRow K t i).2 j hj, h j hj]
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
      (Rule30FiniteStrips.enc_encRow K t i).1 (Nat.pow_le_pow_right (by decide) (by omega)))

theorem colConst_intersection {K Z Q s : Nat} {b : Bool}
    (h : colConst K (Z &&& Q) b = true) (hs : s < 2^K)
    (hZ : Z.testBit s = true) (hQ : Q.testBit s = true) : s.testBit 0 = b := by
  have hh := allBelow_spec h s hs
  rw [Nat.testBit_and, hZ, hQ] at hh
  simpa using hh

theorem white_tube_forces (K r L Z : Nat) (Q : Nat → Nat) (b : Nat → Bool)
    (f : Nat → Nat) (z : Nat → Bool) (hL : L ≤ r)
    (hf : ∀ t, t ≤ r → f t < 2^K)
    (hstep : ∀ t, t < r → f (t+1) = stripStep K false (z t) (f t))
    (hZ : ∀ t, t ≤ r → Z.testBit (f t) = true)
    (hend : (Q 0).testBit (f r) = true)
    (hpre : ∀ d, d < L → preCheck K false (Q (d+1)) (Q d) = true)
    (hzero : Q L = 1)
    (hforce : ∀ d, d ≤ L → colConst K (Z &&& Q d) (b d) = true) :
    ∀ s, s < r → (f s).testBit 0 = if r-s ≤ L then b (r-s) else false := by
  have hQ : ∀ d, d ≤ L → (Q d).testBit (f (r-d)) = true := by
    intro d
    induction d with
    | zero => simpa using hend
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hs : r-(d+1)+1 = r-d := by omega
      rw [← hs, hstep (r-(d+1)) (by omega)] at hi
      exact preCheck_sound (hpre d (by omega)) (hf _ (by omega)) hi
  have hz : f (r-L) = 0 := by
    have hh := hQ L (by omega)
    rw [hzero] at hh
    exact Nat.testBit_one_eq_true_iff_self_eq_zero.mp hh
  have hzbefore : ∀ s, s ≤ r-L → f s = 0 := by
    have hrec : ∀ d, d ≤ r-L → f (r-L-d) = 0 := by
      intro d
      induction d with
      | zero => simpa using hz
      | succ d ih =>
        intro hd
        have hi := ih (by omega)
        have hs : r-L-(d+1)+1 = r-L-d := by omega
        rw [← hs, hstep _ (by omega)] at hi
        exact stripStep_zero_predecessor (hf _ (by omega)) hi
    intro s hs
    have hh := hrec (r-L-s) (by omega)
    simpa only [show r-L-(r-L-s)=s by omega] using hh
  intro s hs
  split
  · rename_i hd
    have hh := colConst_intersection (hforce (r-s) hd) (hf s (by omega)) (hZ s (by omega))
      (by simpa only [show r-(r-s)=s by omega] using hQ (r-s) hd)
    exact hh
  · rw [hzbefore s (by omega), Nat.zero_testBit]

theorem tail_tube_forces (K a : Nat) (u : List Bool) (P S : Nat → Nat)
    (c : Nat → Bool) (f : Nat → Nat) (z : Nat → Bool)
    (hf : ∀ t, t ≤ a+u.length → f t < 2^K)
    (hstep : ∀ j, j < u.length →
      f (a+j+1) = stripStep K (u.getD j false) (z (a+j)) (f (a+j)))
    (hend : (P u.length).testBit (f (a+u.length)) = true)
    (hpre : ∀ j, j < u.length → preCheck K (u.getD j false) (P j) (P (j+1)) = true)
    (hstart : (S 0).testBit (f a) = true)
    (hforward : ∀ j, j < u.length →
      subsetB K (image K (u.getD j false) (S j)) (S (j+1)) = true)
    (hforce : ∀ j, j < u.length → u.getD j false = false →
      colConst K (S j &&& P j) (c j) = true) :
    (P 0).testBit (f a) = true ∧
    ∀ j, j < u.length → u.getD j false = false → (f (a+j)).testBit 0 = c j := by
  have hP : ∀ d, d ≤ u.length → (P (u.length-d)).testBit (f (a+(u.length-d))) = true := by
    intro d
    induction d with
    | zero => simpa using hend
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hs : a+(u.length-(d+1))+1 = a+(u.length-d) := by omega
      rw [← hs, hstep _ (by omega)] at hi
      have hs' : u.length-d = u.length-(d+1)+1 := by omega
      rw [hs'] at hi
      exact preCheck_sound (hpre (u.length-(d+1)) (by omega)) (hf (a+(u.length-(d+1))) (by omega)) hi
  have hS : ∀ j, j ≤ u.length → (S j).testBit (f (a+j)) = true := by
    intro j
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hmem := mem_imageAux (K := K) (a := u.getD j false) hi (z (a+j)) (2^K) (hf _ (by omega))
      change (image K (u.getD j false) (S j)).testBit
        (stripStep K (u.getD j false) (z (a+j)) (f (a+j))) = true at hmem
      have hs := allBelow_spec (hforward j (by omega)) _
        (stripStep_lt K (u.getD j false) (z (a+j)) (f (a+j)))
      rw [hmem, Bool.not_true, Bool.false_or] at hs
      rw [show a+(j+1)=a+j+1 by omega, hstep j (by omega)]
      exact hs
  constructor
  · simpa using hP u.length (by omega)
  · intro j hj ha
    exact colConst_intersection (hforce j hj ha) (hf _ (by omega)) (hS j (by omega))
      (by simpa only [show u.length-(u.length-j)=j by omega] using hP (u.length-j) (by omega))

theorem padding_getD (u : List Bool) (r s : Nat) :
    (List.replicate r false ++ u).getD s false =
      if s < r then false else u.getD (s-r) false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hs : s < r
  · rw [ite_eq_left hs, List.getElem?_append_left (by simpa using hs),
      List.getElem?_replicate_of_lt hs]
    rfl
  · rw [ite_eq_right hs, List.getElem?_append_right (by simpa using Nat.le_of_not_lt hs)]
    simp

theorem subsetB_self (K S : Nat) : subsetB K S S = true := by
  have h : ∀ n, allBelow (fun s => !S.testBit s || S.testBit s) n = true := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [allBelow, ih, Bool.true_and]
      cases S.testBit n <;> rfl
  exact h (2^K)

/-- A stable white set plus a backward tube from the vacuum excludes an arbitrary tail.
Unlike a forward forcing certificate, the tube may condition on the next period's vacuum. -/
theorem no_padding_of_endpoint_tube {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (K L Z : Nat) (Q P S : Nat → Nat)
    (b c : Nat → Bool) (hK : 1 ≤ K)
    (hZzero : Z.testBit 0 = true) (hZfixed : image K false Z = Z)
    (hSzero : S 0 = Z) (hPend : P u.length = 1) (hQstart : Q 0 = P 0)
    (hQend : Q L = 1)
    (hQpre : ∀ d, d < L → preCheck K false (Q (d+1)) (Q d) = true)
    (hPpre : ∀ j, j < u.length → preCheck K (u.getD j false) (P j) (P (j+1)) = true)
    (hSforward : ∀ j, j < u.length → image K (u.getD j false) (S j) = S (j+1))
    (hQforce : ∀ d, d ≤ L → colConst K (Z &&& Q d) (b d) = true)
    (hPforce : ∀ j, j < u.length → u.getD j false = false →
      colConst K (S j &&& P j) (c j) = true)
    (r : Nat) (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K-1+9*(u.length+1) ≤ r) (hrL : L ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  obtain ⟨T, hT, _⟩ := white_padding_forces_early_white hlo hzero i u r hrpulse hword
  have hperiod : ∀ t, T ≤ t → evol x (t+(r+u.length)) i = evol x t i := by
    intro t ht
    rw [hT t ht, hT (t+(r+u.length)) (by omega),
      show t+(r+u.length)-T=(t-T)+(r+u.length) by omega, Nat.add_mod_right]
  have hblock : ∀ n s, s < r+u.length → evol x (T+n*(r+u.length)+s) i =
      if s < r then false else u.getD (s-r) false := by
    intro n s hs
    rw [hT _ (by omega), show T+n*(r+u.length)+s-T=s+n*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs, padding_getD]
  have hwhite : ∀ n s, s < r → evol x (T+n*(r+u.length)+s) i = false := by
    intro n s hs
    rw [hblock n s (by omega), ite_eq_left hs]
  have hstarts : ∀ n, Rule30FiniteStrips.encRow x (T+n*(r+u.length)) i K = 0 := by
    intro n
    apply encRow_zero_of_prefix
    intro j hj
    have hh := periodic_white_cycles_force_empty_prefix hlo hzero i T r u.length hrpulse
      hperiod hwhite n (j+1) (by omega) (by omega)
    simpa only [show i+1+(j:Int)=i+((j+1:Nat):Int) by omega] using hh
  let g : Nat → Bool := fun s =>
    if s < r then (if r-s ≤ L then b (r-s) else false)
    else u.getD (s-r) false || c (s-r)
  have hphase : ∀ n s, s < r+u.length →
      Rule30FiniteMaskedJen.orCol x i (T+n*(r+u.length)+s) = g s := by
    intro n s hs
    let a := T+n*(r+u.length)
    let f : Nat → Nat := fun t => Rule30FiniteStrips.encRow x (a+t) i K
    let z : Nat → Bool := fun t => evol x (a+t) (i+1+K)
    have hf : ∀ t, f t < 2^K := fun t => (Rule30FiniteStrips.enc_encRow K (a+t) i).1
    have hstep : ∀ t, f (t+1) = stripStep K (evol x (a+t) i) (z t) (f t) := by
      intro t
      simpa only [f, z, Nat.add_assoc] using encRow_step x K (a+t) i
    have hfzero : f 0 = 0 := by simpa only [f, a, Nat.add_zero] using hstarts n
    have hfend : f (r+u.length) = 0 := by
      have hh := hstarts (n+1)
      simpa only [f, a, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hh
    have hfZ : ∀ t, t ≤ r → Z.testBit (f t) = true := by
      intro t
      induction t with
      | zero => intro _; rw [hfzero]; exact hZzero
      | succ t ih =>
        intro ht
        have hi := ih (by omega)
        have hmem := mem_imageAux (K := K) (a := false) hi (z t) (2^K) (hf t)
        change (image K false Z).testBit (stripStep K false (z t) (f t))=true at hmem
        rw [hZfixed] at hmem
        rw [hstep, show evol x (a+t) i=false by exact hwhite n t (by omega)]
        exact hmem
    have htube := tail_tube_forces K r u P S c f z (fun t _ => hf t)
      (fun j hj => by
        rw [hstep]
        have hh := hblock n (r+j) (by omega)
        simp only [show ¬r+j<r by omega, ite_false, Nat.add_sub_cancel_left] at hh
        exact congrArg (fun a' => stripStep K a' (z (r+j)) (f (r+j))) hh)
      (by rw [hPend, hfend]; exact Nat.testBit_one_zero)
      hPpre (by rw [hSzero]; exact hfZ r (by omega))
      (fun j hj => by rw [hSforward j hj]; exact subsetB_self K (S (j+1))) hPforce
    have hwhitebits := white_tube_forces K r L Z Q b f z hrL (fun t _ => hf t)
      (fun t ht => by rw [hstep, show evol x (a+t) i=false by exact hwhite n t ht])
      hfZ (by rw [hQstart]; exact htube.1) hQpre hQend hQforce
    have hcell : ∀ t, evol x (a+t) (i+1) = (f t).testBit 0 := by
      intro t
      simpa only [f, Int.ofNat_zero, Int.add_zero] using
        ((Rule30FiniteStrips.enc_encRow K (a+t) i).2 0 (by omega)).symm
    unfold Rule30FiniteMaskedJen.orCol
    rw [hblock n s hs]
    change ((if s<r then false else u.getD (s-r) false) || evol x (a+s) (i+1)) = g s
    by_cases hsr : s < r
    · rw [ite_eq_left hsr, Bool.false_or, hcell, hwhitebits s hsr]
      simp only [g, ite_eq_left hsr]
    · rw [ite_eq_right hsr]
      rw [show g s = (u.getD (s-r) false || c (s-r)) by simp only [g, ite_eq_right hsr]]
      cases hu : u.getD (s-r) false
      · simp only [Bool.false_or]
        rw [hcell]
        have hh := htube.2 (s-r) (by omega) hu
        simpa only [show r+(s-r)=s by omega] using hh
      · rfl
  have hor : ∀ t, T ≤ t → Rule30FiniteMaskedJen.orCol x i t = g ((t-T)%(r+u.length)) := by
    intro t ht
    have hd := Nat.div_add_mod (t-T) (r+u.length)
    have hh := hphase ((t-T)/(r+u.length)) ((t-T)%(r+u.length)) (Nat.mod_lt _ (by omega))
    have heq : T+(t-T)/(r+u.length)*(r+u.length)+(t-T)%(r+u.length)=t := by
      rw [Nat.mul_comm ((t-T)/(r+u.length))]
      omega
    rwa [heq] at hh
  exact Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero i
    ⟨T, r+u.length, by omega, hperiod⟩
    ⟨T, r+u.length, by omega, fun t ht => by
      rw [hor t ht, hor (t+(r+u.length)) (by omega),
        show t+(r+u.length)-T=(t-T)+(r+u.length) by omega, Nat.add_mod_right]⟩

/-! ## Vacuum predecessor closure, multi-step backward `encRow` chains, and intersection bit uniqueness -/

/-- **Empty-Target Vacuity and Vacuum Predecessor Closure for `preCheck` (`preCheck_zero_right_and_vacuum`):**
`preCheck K a Q 0 = true` for all `K, a, Q`, and `preCheck K false Q 1 = true` whenever `Q.testBit 0 = true`. -/
theorem preCheck_zero_right_and_vacuum (K Q : Nat) (a : Bool) (hQ0 : Q.testBit 0 = true) :
    preCheck K a Q 0 = true ∧ preCheck K false Q 1 = true := by
  have h0 : ∀ n, allBelow (fun s =>
      (! (0 : Nat).testBit (stripStep K a false s) || Q.testBit s) &&
      (! (0 : Nat).testBit (stripStep K a true s) || Q.testBit s)) n = true := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      unfold allBelow
      rw [ih]
      simp
  have h1 : ∀ n, n ≤ 2 ^ K → allBelow (fun s =>
      (! (1 : Nat).testBit (stripStep K false false s) || Q.testBit s) &&
      (! (1 : Nat).testBit (stripStep K false true s) || Q.testBit s)) n = true := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      simp only [allBelow, ih (by omega), Bool.true_and, Bool.and_eq_true]
      have hstep_z : ∀ z : Bool, (! (1 : Nat).testBit (stripStep K false z n) || Q.testBit n) = true := by
        intro z
        cases htb : (1 : Nat).testBit (stripStep K false z n)
        · rfl
        · have hz0 : stripStep K false z n = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp htb
          have hn0 : n = 0 := stripStep_zero_predecessor (by omega : n < 2 ^ K) hz0
          subst hn0
          rw [hQ0, Bool.or_true]
      exact ⟨hstep_z false, hstep_z true⟩
  exact ⟨h0 (2 ^ K), h1 (2 ^ K) (Nat.le_refl _)⟩

/-- **Multi-Step Backward Chain Soundness for `encRow` (`enc_backward_chain`):**
if `P` is a backward-checked chain of masks along driver word `u` and column `i` of `evol x`
reads `u` from `t0` to `t0 + u.length`, then `(P u.length).testBit (encRow x (t0 + u.length) i K) = true`
implies `(P 0).testBit (encRow x t0 i K) = true`. -/
theorem enc_backward_chain {x : Int → Bool} (K t0 : Nat) (i : Int) (u : List Bool) (P : Nat → Nat)
    (hpre : ∀ j, j < u.length → preCheck K (u.getD j false) (P j) (P (j + 1)) = true)
    (hevol : ∀ j, j < u.length → evol x (t0 + j) i = u.getD j false)
    (hend : (P u.length).testBit (Rule30FiniteStrips.encRow x (t0 + u.length) i K) = true) :
    (P 0).testBit (Rule30FiniteStrips.encRow x t0 i K) = true ∧
    ∀ d, d ≤ u.length →
      (P (u.length - d)).testBit (Rule30FiniteStrips.encRow x (t0 + (u.length - d)) i K) = true := by
  have hchain : ∀ d, d ≤ u.length →
      (P (u.length - d)).testBit (Rule30FiniteStrips.encRow x (t0 + (u.length - d)) i K) = true := by
    intro d
    induction d with
    | zero => intro _; simpa using hend
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hidx : t0 + (u.length - d) = (t0 + (u.length - (d + 1))) + 1 := by omega
      have hPidx : u.length - d = (u.length - (d + 1)) + 1 := by omega
      rw [hidx, hPidx] at hi
      exact enc_backward (hpre (u.length - (d + 1)) (by omega)) (hevol (u.length - (d + 1)) (by omega)) hi
  refine ⟨?_, hchain⟩
  have h0 := hchain u.length (Nat.le_refl _)
  simpa using h0

/-- **Uniqueness of Forced Column-1 Bits on Overlapping Masks (`colConst_intersection_unique`):**
if `colConst K (Z &&& Q1) b1 = true` and `colConst K (Z &&& Q2) b2 = true` and a state `s < 2^K`
lies in `Z`, `Q1`, and `Q2`, then `b1 = b2`. -/
theorem colConst_intersection_unique {K Z Q1 Q2 s : Nat} {b1 b2 : Bool}
    (h1 : colConst K (Z &&& Q1) b1 = true)
    (h2 : colConst K (Z &&& Q2) b2 = true)
    (hs : s < 2 ^ K) (hZ : Z.testBit s = true)
    (hQ1 : Q1.testBit s = true) (hQ2 : Q2.testBit s = true) :
    b1 = b2 :=
  (colConst_intersection h1 hs hZ hQ1).symm.trans (colConst_intersection h2 hs hZ hQ2)

end Ruliology.CellularAutomata.Rule30BackwardTube
