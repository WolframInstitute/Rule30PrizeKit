module

public import Ruliology.CellularAutomata.Rule30BackwardTube

@[expose] public section

/-!
A backward certificate under a white driver needs predecessor checks
only on the stable forward reachable set. Restricting to that invariant
set gives an endpoint-conditioned tube with the same padding exclusion.
-/
namespace Ruliology.CellularAutomata.Rule30RestrictedBackwardTube
open Rule30Jen Rule30Realization Rule30StripCertificates Rule30FiniteStrips
open Rule30WhitePulse Rule30ZeroPredecessor Rule30WhitePadding
open Rule30BackwardTube

def restrictedPreCheck (K : Nat) (a : Bool) (Z Q R : Nat) : Bool :=
  allBelow (fun s => !Z.testBit s ||
    ((! R.testBit (stripStep K a false s) || Q.testBit s) &&
    (! R.testBit (stripStep K a true s) || Q.testBit s))) (2^K)

theorem restrictedPreCheck_sound {K Z Q R s : Nat} {a z : Bool}
    (h : restrictedPreCheck K a Z Q R = true) (hs : s < 2^K)
    (hZ : Z.testBit s = true)
    (ht : R.testBit (stripStep K a z s) = true) : Q.testBit s = true := by
  have hh := allBelow_spec h s hs
  rw [hZ, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hh
  cases z
  · have hh := hh.1
    rw [ht, Bool.not_true, Bool.false_or] at hh
    exact hh
  · have hh := hh.2
    rw [ht, Bool.not_true, Bool.false_or] at hh
    exact hh

theorem white_tube_forces (K r L Z : Nat) (Q : Nat → Nat) (b : Nat → Bool)
    (f : Nat → Nat) (z : Nat → Bool) (hL : L ≤ r)
    (hf : ∀ t, t ≤ r → f t < 2^K)
    (hstep : ∀ t, t < r → f (t+1) = stripStep K false (z t) (f t))
    (hZ : ∀ t, t ≤ r → Z.testBit (f t) = true)
    (hend : (Q 0).testBit (f r) = true)
    (hpre : ∀ d, d < L → restrictedPreCheck K false Z (Q (d+1)) (Q d) = true)
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
      exact restrictedPreCheck_sound (hpre d (by omega)) (hf _ (by omega)) (hZ _ (by omega)) hi
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

/-- A stable white set plus a backward tube from the vacuum excludes an arbitrary tail.
Unlike a forward forcing certificate, the tube may condition on the next period's vacuum. -/
theorem no_padding_of_endpoint_tube {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (K L Z : Nat) (Q P S : Nat → Nat)
    (b c : Nat → Bool) (hK : 1 ≤ K)
    (hZzero : Z.testBit 0 = true) (hZfixed : image K false Z = Z)
    (hSzero : S 0 = Z) (hPend : P u.length = 1) (hQstart : Q 0 = P 0)
    (hQend : Q L = 1)
    (hQpre : ∀ d, d < L → restrictedPreCheck K false Z (Q (d+1)) (Q d) = true)
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

/-! ## Vacuity and vacuum laws for `restrictedPreCheck`, one-step `encRow` backward soundness, and finite/seed endpoint-tube exclusions -/

/-- **Empty-Domain, Empty-Target, and Vacuum Predecessor Closure for `restrictedPreCheck` (`restrictedPreCheck_vacuous_and_vacuum`).** -/
theorem restrictedPreCheck_vacuous_and_vacuum (K Z Q R : Nat) (a : Bool) (hQ0 : Q.testBit 0 = true) :
    restrictedPreCheck K a 0 Q R = true ∧
    restrictedPreCheck K a Z Q 0 = true ∧
    restrictedPreCheck K false Z Q 1 = true := by
  have hZ0 : ∀ n, allBelow (fun s => !(0 : Nat).testBit s ||
      ((! R.testBit (stripStep K a false s) || Q.testBit s) &&
       (! R.testBit (stripStep K a true s) || Q.testBit s))) n = true := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => unfold allBelow; rw [ih]; simp
  have hR0 : ∀ n, allBelow (fun s => !Z.testBit s ||
      ((! (0 : Nat).testBit (stripStep K a false s) || Q.testBit s) &&
       (! (0 : Nat).testBit (stripStep K a true s) || Q.testBit s))) n = true := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => unfold allBelow; rw [ih]; simp
  have hR1 : ∀ n, n ≤ 2 ^ K → allBelow (fun s => !Z.testBit s ||
      ((! (1 : Nat).testBit (stripStep K false false s) || Q.testBit s) &&
       (! (1 : Nat).testBit (stripStep K false true s) || Q.testBit s))) n = true := by
    intro n; induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      simp only [allBelow, ih (by omega), Bool.true_and]
      cases Z.testBit n
      · rfl
      · simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
        have hstep_z : ∀ z : Bool, (! (1 : Nat).testBit (stripStep K false z n) || Q.testBit n) = true := by
          intro z
          cases htb : (1 : Nat).testBit (stripStep K false z n)
          · rfl
          · have hz0 : stripStep K false z n = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp htb
            have hn0 : n = 0 := stripStep_zero_predecessor (by omega : n < 2 ^ K) hz0
            subst hn0
            rw [hQ0, Bool.or_true]
        exact ⟨hstep_z false, hstep_z true⟩
  exact ⟨hZ0 (2 ^ K), hR0 (2 ^ K), hR1 (2 ^ K) (Nat.le_refl _)⟩

/-- **One-Step Restricted Backward Soundness for `encRow` (`enc_restricted_backward`).** -/
theorem enc_restricted_backward {x : Int → Bool} {K t Z Q R : Nat} {i : Int} {a : Bool}
    (h : restrictedPreCheck K a Z Q R = true) (ha : evol x t i = a)
    (hZ : Z.testBit (Rule30FiniteStrips.encRow x t i K) = true)
    (hR : R.testBit (Rule30FiniteStrips.encRow x (t + 1) i K) = true) :
    Q.testBit (Rule30FiniteStrips.encRow x t i K) = true := by
  rw [encRow_step, ha] at hR
  exact restrictedPreCheck_sound h (Rule30FiniteStrips.enc_encRow K t i).1 hZ hR

/-- **Finite-Configuration and Single-Seed Endpoint-Tube Exclusions (`no_padding_of_endpoint_tube_finite_and_seed`).** -/
theorem no_padding_of_endpoint_tube_finite_and_seed
    (u : List Bool) (K L Z : Nat) (Q P S : Nat → Nat) (b c : Nat → Bool) (hK : 1 ≤ K)
    (hZzero : Z.testBit 0 = true) (hZfixed : image K false Z = Z)
    (hSzero : S 0 = Z) (hPend : P u.length = 1) (hQstart : Q 0 = P 0) (hQend : Q L = 1)
    (hQpre : ∀ d, d < L → restrictedPreCheck K false Z (Q (d + 1)) (Q d) = true)
    (hPpre : ∀ j, j < u.length → preCheck K (u.getD j false) (P j) (P (j + 1)) = true)
    (hSforward : ∀ j, j < u.length → image K (u.getD j false) (S j) = S (j + 1))
    (hQforce : ∀ d, d ≤ L → colConst K (Z &&& Q d) (b d) = true)
    (hPforce : ∀ j, j < u.length → u.getD j false = false → colConst K (S j &&& P j) (c j) = true)
    (r : Nat) (hrpulse : 10 * u.length + 11 ≤ r) (hrwidth : K - 1 + 9 * (u.length + 1) ≤ r) (hrL : L ≤ r) :
    (∀ {x : Int → Bool}, Rule30PeriodTwoSideways.FinConfig x → (∃ p, x p = true) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u)) ∧
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  refine ⟨fun hfin hne i => ?_, ?_⟩
  · obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
    exact no_padding_of_endpoint_tube hlo hzero i u K L Z Q P S b c hK hZzero hZfixed
      hSzero hPend hQstart hQend hQpre hPpre hSforward hQforce hPforce r hrpulse hrwidth hrL
  · have hzero : ∀ p : Int, p < 0 → seed p = false := fun p hp => by simp [seed, show p ≠ 0 by omega]
    have h := no_padding_of_endpoint_tube (x := seed) (lo := 0) (by decide) hzero 0 u K L Z Q P S b c
      hK hZzero hZfixed hSzero hPend hQstart hQend hQpre hPpre hSforward hQforce hPforce r hrpulse hrwidth hrL
    simpa only [Rule30FiniteStrips.EventuallyWord, Rule30StripCertificates.EventuallyWord, evol_seed] using h

end Ruliology.CellularAutomata.Rule30RestrictedBackwardTube
