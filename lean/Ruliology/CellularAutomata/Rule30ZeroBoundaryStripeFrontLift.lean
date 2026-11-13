module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-! Width projection, universal return periods, parallel upper-window updates,
and sparse return-map certificate soundness for stripe fronts. -/

@[expose] public section

/-! Width projection and certificate lifting for front-window searches.
These lemmas do not assert that arbitrary finite tails have certificates. -/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

def LowEq (n a b : Nat) : Prop := ∀ i, i < n → a.testBit i = b.testBit i

theorem parity_of_bit0 {a b : Nat} (h : a.testBit 0 = b.testBit 0) : a % 2 = b % 2 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp_all [Nat.testBit_zero]

theorem pstep_low {n a b : Nat} (h : LowEq (n+1) a b) :
    LowEq n (pstepN a) (pstepN b) := by
  intro i hi
  change ((a >>> 1) ^^^ (a ||| (a <<< 1))).testBit i =
    ((b >>> 1) ^^^ (b ||| (b <<< 1))).testBit i
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  rw [h (1+i) (by omega), h i (by omega), h (i-1) (by omega)]

theorem sig_congr {n r s a b : Nat} (hp : r % 2 = s % 2) (h : LowEq n a b) :
    sig n r a = sig n s b := by
  induction n generalizing r s a b with
  | zero => rfl
  | succ n ih =>
    have hm := parity_of_bit0 (h 0 (by omega))
    have ht : (r+1) % 2 = (s+1) % 2 := by omega
    change Bool.rec (motive := fun _ => Bool) (sig n (r+1) (pstepN a)) true
      (band (Nat.beq (r%2) 0) (Nat.beq (a%2) 0)) =
        Bool.rec (motive := fun _ => Bool) (sig n (s+1) (pstepN b)) true
          (band (Nat.beq (s%2) 0) (Nat.beq (b%2) 0))
    rw [hp, hm, ih ht (pstep_low h)]

theorem sig_mono {n m r a : Nat} (hn : n ≤ m) (ha : sig n r a = true) :
    sig m r a = true := by
  induction n generalizing m r a with
  | zero => cases ha
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      change Bool.rec (sig n (r+1) (pstepN a)) true
        (band (Nat.beq (r%2) 0) (Nat.beq (a%2) 0)) = true at ha
      change Bool.rec (sig m (r+1) (pstepN a)) true
        (band (Nat.beq (r%2) 0) (Nat.beq (a%2) 0)) = true
      cases hc : band (Nat.beq (r%2) 0) (Nat.beq (a%2) 0) with
      | false =>
        have hh : sig n (r+1) (pstepN a) = true := by simpa only [hc] using ha
        exact ih (by omega) hh
      | true => rfl

theorem fstep_low {n K₁ K₂ a b p : Nat} (h₁ : n ≤ K₁) (h₂ : n ≤ K₂)
    (h : LowEq n a b) (hp : p < 2) :
    LowEq n (fstep K₁ a p) (fstep K₂ b p) := by
  intro i hi
  rw [testBit_fstep K₁ a p i hp, testBit_fstep K₂ b p i hp]
  simp only [show decide (i < K₁) = true from decide_eq_true (by omega),
    show decide (i < K₂) = true from decide_eq_true (by omega), Bool.true_and,
    h i hi, h (i-1) (by omega), h (i-2) (by omega)]

theorem orbit_low {n K₁ K₂ a b p : Nat} (h₁ : n ≤ K₁) (h₂ : n ≤ K₂)
    (h : LowEq n a b) (hp : p < 2) (t : Nat) :
    (orb K₁ t (a,p)).2 = (orb K₂ t (b,p)).2 ∧
      (orb K₁ t (a,p)).2 < 2 ∧
      LowEq n (orb K₁ t (a,p)).1 (orb K₂ t (b,p)).1 := by
  induction t with
  | zero => exact ⟨rfl, hp, h⟩
  | succ t ih =>
    rcases ih with ⟨he, hp', hlow⟩
    change (1-(orb K₁ t (a,p)).2 = 1-(orb K₂ t (b,p)).2) ∧
      1-(orb K₁ t (a,p)).2 < 2 ∧
      LowEq n (fstep K₁ (orb K₁ t (a,p)).1 (orb K₁ t (a,p)).2)
        (fstep K₂ (orb K₂ t (b,p)).1 (orb K₂ t (b,p)).2)
    refine ⟨by rw [he], by omega, ?_⟩
    rw [← he]
    exact fstep_low h₁ h₂ hlow hp'

/-- Reuse all successful residues of a smaller front cycle. A larger cycle
only needs separate witness checks on the lifted exceptional residues.
The higher-width period and the exceptional checks remain explicit premises. -/
theorem punctured_cycle_lift
    {Klo Khi Slo Shi A B p L H : Nat}
    (hK : Slo+1 ≤ Klo) (hwidth : Klo ≤ Khi) (hS : Slo ≤ Shi)
    (hp : p < 2) (hinit : LowEq Klo A B)
    (hL : 0 < L) (hLe : L % 2 = 0)
    (hLo : orb Klo L (B,p) = (B,p))
    (hH : 0 < H) (hHe : H % 2 = 0)
    (hHi : orb Khi H (A,p) = (A,p))
    (E : Nat → Prop)
    (hgood : ∀ r, r < L → r % 2 = 1-p → ¬ E r →
      sig (Slo+1) r (orb Klo r (B,p)).1 = true)
    (hrare : ∀ r, r < H → r % 2 = 1-p → E (r%L) →
      sig (Shi+1) r (orb Khi r (A,p)).1 = true) :
    Cycle Khi Shi A p H := by
  classical
  refine ⟨hHe, hH, hHi, ?_⟩
  intro r hr hpar
  simp only [Nat.zero_add] at hpar ⊢
  by_cases he : E (r%L)
  · exact hrare r hr hpar he
  · have hm : (r%L)%2 = r%2 :=
      Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hLe)
    have hs := hgood (r%L) (Nat.mod_lt _ hL) (by omega) he
    have ho := orb_mod Klo L (B,p) hLo r
    rw [← ho] at hs
    have hb := (orbit_low (n := Klo) (K₁ := Khi) (K₂ := Klo)
      (a := A) (b := B) (p := p) hwidth (Nat.le_refl _) hinit hp r).2.2
    have hl : LowEq (Slo+1) (orb Klo r (B,p)).1 (orb Khi r (A,p)).1 := by
      intro i hi
      exact (hb i (by omega)).symm
    have hc := sig_congr hm hl
    rw [hc] at hs
    exact sig_mono (by omega) hs

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

/-! Period lifting for the triangular front-window permutation.
Existence of a period does not assert the required white-witness checks. -/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift
open Ruliology.CellularAutomata
open Rule30ZeroBoundaryStripeFront

theorem fstep_top_flip (K a p : Nat) (hp : p < 2) :
    fstep (K+1) (a ^^^ 2^K) p = (fstep (K+1) a p) ^^^ 2^K := by
  apply Nat.eq_of_testBit_eq
  intro i
  conv => rhs; rw [Nat.testBit_xor]
  rw [testBit_fstep (K+1) (a ^^^ 2^K) p i hp,
      testBit_fstep (K+1) a p i hp]
  simp only [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : i < K+1
  · rcases (show i < K ∨ i = K by omega) with hil | hiK
    · simp [hi, show K ≠ i by omega, show K ≠ i-1 by omega,
        show K ≠ i-2 by omega]
    · subst i
      rcases (show K = 0 ∨ K = 1 ∨ 2 ≤ K by omega) with rfl | rfl | hk
      · simp [Bool.xor_comm]
      · simp [Bool.xor_comm]
      · simp only [decide_eq_true hi, decide_true, Bool.true_and, Bool.xor_true,
          ite_eq_right (show K ≠ 0 by omega), ite_eq_right (show K ≠ 1 by omega),
          decide_eq_false (show K ≠ K-1 by omega),
          decide_eq_false (show K ≠ K-2 by omega), Bool.xor_false]
        cases a.testBit K <;> cases (a.testBit (K-1) || a.testBit (K-2)) <;> rfl
  · simp [hi, show K ≠ i by omega]

theorem orbit_phase_lt (K a p t : Nat) (hp : p < 2) :
    (orb K t (a,p)).2 < 2 := by
  cases t with
  | zero => exact hp
  | succ t => change 1-(orb K t (a,p)).2 < 2; omega

theorem orbit_top_flip (K a p t : Nat) (hp : p < 2) :
    orb (K+1) t (a ^^^ 2^K,p) =
      ((orb (K+1) t (a,p)).1 ^^^ 2^K, (orb (K+1) t (a,p)).2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [orb, fS, ih]
    rw [fstep_top_flip K _ _ (orbit_phase_lt _ _ _ _ hp)]

theorem fstep_bound (K a p : Nat) : fstep K a p < 2^K := by
  unfold fstep
  exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos K) (by decide))

theorem orbit_bound {K a p : Nat} (ha : a < 2^K) (t : Nat) :
    (orb K t (a,p)).1 < 2^K := by
  cases t with
  | zero => exact ha
  | succ t => exact fstep_bound _ _ _

theorem low_two_choices {K a b : Nat} (ha : a < 2^(K+1)) (hb : b < 2^(K+1))
    (h : LowEq K a b) : a = b ∨ a = b ^^^ 2^K := by
  by_cases he : a.testBit K = b.testBit K
  · left
    apply Nat.eq_of_testBit_eq
    intro i
    rcases (show i < K ∨ i = K ∨ K+1 ≤ i by omega) with hi | hiK | hi
    · exact h i hi
    · subst i; exact he
    · rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt ha hi,
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hb hi]
  · right
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    rcases (show i < K ∨ i = K ∨ K+1 ≤ i by omega) with hi | hiK | hi
    · rw [decide_eq_false (show K ≠ i by omega), Bool.xor_false]
      exact h i hi
    · subst i
      simp only [decide_true, Bool.xor_true]
      cases hA : a.testBit K <;> cases hB : b.testBit K <;> simp_all
    · rw [decide_eq_false (show K ≠ i by omega), Bool.xor_false,
        Rule30ZeroBoundarySmall.testBit_ge_of_lt ha hi,
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hb hi]

/-- Every even return of the lower window yields a return after twice as many
steps in the one-bit-larger window. No certificate-success claim is included. -/
theorem double_period {K a b p L : Nat} (ha : a < 2^(K+1)) (hp : p < 2)
    (hinit : LowEq K a b) (hlo : orb K L (b,p) = (b,p)) :
    orb (K+1) (L+L) (a,p) = (a,p) := by
  have hpair := orbit_low (n := K) (K₁ := K+1) (K₂ := K)
    (a := a) (b := b) (p := p) (by omega) (Nat.le_refl _) hinit hp L
  rw [hlo] at hpair
  have hs : (orb (K+1) L (a,p)).2 = p := hpair.1
  have hl : LowEq K (orb (K+1) L (a,p)).1 a := by
    intro i hi
    exact (hpair.2.2 i hi).trans (hinit i hi).symm
  rcases low_two_choices (orbit_bound ha L) ha hl with he | he
  · have hr : orb (K+1) L (a,p) = (a,p) := Prod.ext he hs
    rw [orb_add, hr, hr]
  · have hr : orb (K+1) L (a,p) = (a ^^^ 2^K,p) := Prod.ext he hs
    rw [orb_add, hr, orbit_top_flip K a p L hp, hr]
    simp [Nat.xor_assoc]

/-- A uniform period bound for every nonempty finite front window. This only
proves return of the window; it says nothing about the white-witness test. -/
theorem universal_front_period (K a p : Nat) (ha : a < 2^(K+1)) (hp : p < 2) :
    orb (K+1) (2^(K+1)) (a,p) = (a,p) := by
  induction K generalizing a p with
  | zero =>
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
      rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;> decide +kernel
  | succ K ih =>
    let b := a % 2^(K+1)
    have hb : b < 2^(K+1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hinit : LowEq (K+1) a b := by
      intro i hi
      simp only [b, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
    have hh := double_period (K := K+1) (a := a) (b := b) (p := p)
      (L := 2^(K+1)) ha hp hinit (ih b p hb hp)
    have hn : 2^(K+1)+2^(K+1) = 2^((K+1)+1) := by
      calc
        2^(K+1)+2^(K+1) = 2^(K+1)*2 := by omega
        _ = 2^((K+1)+1) := (Nat.pow_succ 2 (K+1)).symm
    simpa only [hn] using hh

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

/-! Bit-parallel high-window updates above a shared lower front window.
The generic projection lemmas below do not certify any numerical table. -/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift
open Ruliology.CellularAutomata
open Rule30ZeroBoundaryStripeFront

def scan (l r : Nat) : List Nat → List Nat
  | [] => []
  | a :: xs => (a ^^^ (l ||| r)) :: scan a l xs

def bscan (l r : Bool) : List Bool → List Bool
  | [] => []
  | a :: xs => xor a (l || r) :: bscan a l xs

theorem scan_length (l r : Nat) (xs : List Nat) : (scan l r xs).length = xs.length := by
  induction xs generalizing l r with
  | nil => rfl
  | cons a xs ih => simp only [scan, List.length_cons, ih]

theorem bscan_length (l r : Bool) (xs : List Bool) : (bscan l r xs).length = xs.length := by
  induction xs generalizing l r with
  | nil => rfl
  | cons a xs ih => simp only [bscan, List.length_cons, ih]

theorem map_bit_scan (l r : Nat) (xs : List Nat) (p : Nat) :
    (scan l r xs).map (fun x => x.testBit p) =
      bscan (l.testBit p) (r.testBit p) (xs.map (fun x => x.testBit p)) := by
  induction xs generalizing l r with
  | nil => rfl
  | cons a xs ih =>
    simp only [scan, bscan, List.map_cons, Nat.testBit_xor, Nat.testBit_or, ih]

def bitMask (ALL : Nat) (b : Bool) : Nat := if b then ALL else 0

theorem bitMask_bit {ALL p : Nat} (h : ALL.testBit p = true) (b : Bool) :
    (bitMask ALL b).testBit p = b := by
  cases b <;> simp [bitMask, h]

structure LaneState where
  lo : Nat
  phase : Nat
  planes : List Nat
deriving DecidableEq

structure BoolState where
  lo : Nat
  phase : Nat
  bits : List Bool
deriving DecidableEq

def project (p : Nat) (s : LaneState) : BoolState :=
  ⟨s.lo, s.phase, s.planes.map (fun x => x.testBit p)⟩

def next (K ALL : Nat) (s : LaneState) : LaneState :=
  ⟨fstep K s.lo s.phase, 1-s.phase,
    scan (bitMask ALL (s.lo.testBit (K-1))) (bitMask ALL (s.lo.testBit (K-2))) s.planes⟩

def bnext (K : Nat) (s : BoolState) : BoolState :=
  ⟨fstep K s.lo s.phase, 1-s.phase,
    bscan (s.lo.testBit (K-1)) (s.lo.testBit (K-2)) s.bits⟩

theorem project_next {ALL p : Nat} (h : ALL.testBit p = true) (K : Nat) (s : LaneState) :
    project p (next K ALL s) = bnext K (project p s) := by
  cases s with
  | mk lo phase planes =>
    simp only [project, next, bnext, map_bit_scan, bitMask_bit h]

noncomputable def run (K ALL : Nat) : Nat → LaneState → LaneState :=
  Nat.rec (motive := fun _ => LaneState → LaneState) (fun s => s)
    (fun _ ih s => ih (next K ALL s))

def brun (K : Nat) : Nat → BoolState → BoolState
  | 0, s => s
  | n+1, s => brun K n (bnext K s)

theorem project_run {ALL p : Nat} (h : ALL.testBit p = true) (K t : Nat) (s : LaneState) :
    project p (run K ALL t s) = brun K t (project p s) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    change project p (run K ALL t (next K ALL s)) = brun K t (bnext K (project p s))
    rw [← project_next h K s]
    exact ih _

theorem bscan_getD (l r : Bool) (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    (bscan l r xs).getD i false = xor (xs.getD i false)
      ((if i = 0 then l else xs.getD (i-1) false) ||
       (if i = 0 then r else if i = 1 then l else xs.getD (i-2) false)) := by
  induction xs generalizing l r i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => cases xs with
        | nil => simp at hi
        | cons b xs => rfl
      | succ i =>
        have h := ih a l (i+1) (by simpa using hi)
        cases i <;> simpa [bscan, Nat.add_sub_cancel] using h

def config (K : Nat) (s : BoolState) (i : Nat) : Bool :=
  if i < K then s.lo.testBit i else s.bits.getD (i-K) false

def Represents (K row : Nat) (s : BoolState) : Prop :=
  ∀ i, i < K+s.bits.length → row.testBit i = config K s i

/-- Every high bit uses precisely the two preceding old bits. The shared low
window supplies the two missing boundary bits, for every lane simultaneously. -/
theorem represents_next {K row : Nat} {s : BoolState} (hK : 2 ≤ K)
    (hp : s.phase < 2) (h : Represents K row s) :
    Represents K (fstep (K+s.bits.length) row s.phase) (bnext K s) := by
  intro i hi
  have hti : i < K+s.bits.length := by simpa only [bnext, bscan_length] using hi
  rw [testBit_fstep _ _ _ _ hp]
  by_cases hlo : i < K
  · have hc : ∀ j, j ≤ i → row.testBit j = s.lo.testBit j := by
      intro j hj
      have hjK : j < K := by omega
      simpa only [config, ite_eq_left hjK] using h j (by omega)
    simp only [config, bnext, ite_eq_left hlo]
    rw [testBit_fstep _ _ _ _ hp]
    simp only [decide_eq_true hti, decide_eq_true hlo, Bool.true_and,
      hc i (Nat.le_refl _), hc (i-1) (by omega), hc (i-2) (by omega)]
  · simp only [config, bnext, ite_eq_right hlo]
    rw [bscan_getD _ _ _ _ (by omega)]
    simp only [decide_eq_true hti, Bool.true_and,
      ite_eq_right (show i ≠ 0 by omega), ite_eq_right (show i ≠ 1 by omega)]
    rw [h i hti, h (i-1) (by omega), h (i-2) (by omega)]
    by_cases hb : i = K
    · subst i
      simp [config, show K-1 < K by omega, show K-2 < K by omega]
    · by_cases hb1 : i = K+1
      · subst i
        simp [config, show ¬ (K+1 < K) by omega, show K+1-1 = K by omega, show K+1-2 = K-1 by omega,
          show K+1-K = 1 by omega, show K-1 < K by omega]
      · have hbig : K+2 ≤ i := by omega
        simp only [config, ite_eq_right hlo,
          ite_eq_right (show ¬ (i-1 < K) by omega),
          ite_eq_right (show ¬ (i-2 < K) by omega),
          ite_eq_right (show i-K ≠ 0 by omega),
          ite_eq_right (show i-K ≠ 1 by omega),
          show i-1-K = i-K-1 by omega,
          show i-2-K = i-K-2 by omega]

theorem brun_length (K t : Nat) (s : BoolState) :
    (brun K t s).bits.length = s.bits.length := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    change (brun K t (bnext K s)).bits.length = s.bits.length
    rw [ih]
    exact bscan_length _ _ _

/-- The Boolean lane follows the actual official finite front orbit, for all
times. The representation specifies every bit in the finite window. -/
theorem brun_represents {K row : Nat} {s : BoolState} (hK : 2 ≤ K)
    (hp : s.phase < 2) (h : Represents K row s) (t : Nat) :
    (brun K t s).phase = (orb (K+s.bits.length) t (row,s.phase)).2 ∧
      Represents K (orb (K+s.bits.length) t (row,s.phase)).1 (brun K t s) := by
  induction t generalizing row s with
  | zero => exact ⟨rfl, h⟩
  | succ t ih =>
    have hp' : (bnext K s).phase < 2 := by change 1-s.phase < 2; omega
    have hn := represents_next hK hp h
    have hr := ih (row := fstep (K+s.bits.length) row s.phase) (s := bnext K s) hp' hn
    simpa only [brun, bnext, bscan_length, orb_succ', fS] using hr

theorem run_represents {ALL p K row : Nat} {s : LaneState}
    (hALL : ALL.testBit p = true) (hK : 2 ≤ K) (hp : s.phase < 2)
    (h : Represents K row (project p s)) (t : Nat) :
    Represents K (orb (K+s.planes.length) t (row,s.phase)).1 (project p (run K ALL t s)) := by
  rw [project_run hALL]
  have hr := (brun_represents hK hp h t).2
  simpa only [project, List.length_map] using hr

def word (K : Nat) (s : BoolState) : Nat :=
  s.lo ||| ((pk (fun j => s.bits.getD j false) s.bits.length) <<< K)

theorem word_bound (K : Nat) (s : BoolState) (hlo : s.lo < 2^K) :
    word K s < 2^(K+s.bits.length) := by
  apply Nat.lt_pow_two_of_testBit _
  intro i hi
  unfold word
  rw [Nat.testBit_or, Nat.testBit_shiftLeft,
    Rule30ZeroBoundarySmall.testBit_ge_of_lt hlo (by omega), testBit_pk]
  simp [show K ≤ i by omega, show ¬ (i-K < s.bits.length) by omega]

theorem word_represents (K : Nat) (s : BoolState) (hlo : s.lo < 2^K) :
    Represents K (word K s) s := by
  intro i hi
  unfold word
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : i < K
  · simp only [config, ite_eq_left h, decide_eq_false (show ¬ (K ≤ i) by omega),
      Bool.false_and, Bool.or_false]
  · rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt hlo (by omega), testBit_pk]
    simp only [Bool.false_or, decide_eq_true (show K ≤ i by omega), Bool.true_and,
      decide_eq_true (show i-K < s.bits.length by omega), config, ite_eq_right h]

theorem represents_unique {K row : Nat} {s : BoolState}
    (hr : row < 2^(K+s.bits.length)) (hlo : s.lo < 2^K) (h : Represents K row s) :
    row = word K s := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K+s.bits.length
  · exact (h i hi).trans ((word_represents K s hlo) i hi).symm
  · rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt hr (by omega),
      Rule30ZeroBoundarySmall.testBit_ge_of_lt (word_bound K s hlo) (by omega)]

theorem brun_lo_bound {K : Nat} {s : BoolState} (hlo : s.lo < 2^K) (t : Nat) :
    (brun K t s).lo < 2^K := by
  induction t generalizing s with
  | zero => exact hlo
  | succ t ih =>
    change (brun K t (bnext K s)).lo < 2^K
    exact ih (Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift.fstep_bound _ _ _)

/-- Integer endpoint semantics of the parallel program, including phase.
Every closed program equality can therefore certify all of its input lanes. -/
theorem run_correct {ALL p K : Nat} {s : LaneState}
    (hALL : ALL.testBit p = true) (hK : 2 ≤ K) (hp : s.phase < 2)
    (hlo : s.lo < 2^K) (t : Nat) :
    orb (K+s.planes.length) t (word K (project p s), s.phase) =
      (word K (project p (run K ALL t s)), (run K ALL t s).phase) := by
  have hi := word_represents K (project p s) hlo
  have hr := run_represents hALL hK hp hi t
  have he := project_run hALL K t s
  have hl : (project p (run K ALL t s)).lo < 2^K := by
    rw [he]
    exact brun_lo_bound hlo t
  have hn : (project p (run K ALL t s)).bits.length = s.planes.length := by
    rw [he, brun_length]
    exact List.length_map _
  have hb : (orb (K+s.planes.length) t (word K (project p s),s.phase)).1 <
      2^(K+(project p (run K ALL t s)).bits.length) := by
    rw [hn]
    apply Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift.orbit_bound
    simpa only [project, List.length_map] using word_bound K (project p s) hlo
  apply Prod.ext
  · exact represents_unique hb hl hr
  · have hphase := (brun_represents hK hp hi t).1
    have hh : (project p (run K ALL t s)).phase =
        (orb (K+s.planes.length) t (word K (project p s),s.phase)).2 := by
      rw [he]
      simpa only [project, List.length_map] using hphase
    exact hh.symm

def initial (m a p : Nat) : LaneState :=
  ⟨a, p, (List.range m).map (Rule30ZeroBoundaryLanes.pat m)⟩

def allMask (m : Nat) : Nat := 2^(2^m)-1

theorem allMask_bit {m u : Nat} (hu : u < 2^m) : (allMask m).testBit u = true := by
  simp only [allMask, Nat.testBit_two_pow_sub_one, decide_eq_true hu]

theorem pk_pats (m u : Nat) (hu : u < 2^m) :
    pk (fun j => (((List.range m).map (Rule30ZeroBoundaryLanes.pat m)).getD j 0).testBit u) m = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pk]
  by_cases hi : i < m
  · rw [decide_eq_true hi, Bool.true_and, Rule30ZeroBoundaryLanes.pats_getD m i hi,
      Rule30ZeroBoundaryLanes.pat_spec m i u hi hu]
  · rw [decide_eq_false hi, Bool.false_and,
      Rule30ZeroBoundarySmall.testBit_ge_of_lt hu (by omega)]

theorem initial_word (K m a phase u : Nat) (hu : u < 2^m) :
    word K (project u (initial m a phase)) = a ||| (u <<< K) := by
  simp only [word, project, initial, List.length_map, List.length_range,
    ← Rule30ZeroBoundaryLanes.getD_testBit]
  rw [pk_pats m u hu]

theorem initial_run_correct (K m a phase u t : Nat) (hK : 2 ≤ K)
    (ha : a < 2^K) (hp : phase < 2) (hu : u < 2^m) :
    orb (K+m) t (a ||| (u <<< K), phase) =
      (word K (project u (run K (allMask m) t (initial m a phase))),
        (run K (allMask m) t (initial m a phase)).phase) := by
  have hc := run_correct (s := initial m a phase) (allMask_bit hu) hK hp ha t
  rw [initial_word K m a phase u hu] at hc
  simpa only [initial, List.length_map, List.length_range] using hc

theorem run_zero (K ALL : Nat) (s : LaneState) : run K ALL 0 s = s := rfl

theorem run_succ (K ALL n : Nat) (s : LaneState) :
    run K ALL (n+1) s = run K ALL n (next K ALL s) := rfl

theorem run_add (K ALL a b : Nat) (s : LaneState) :
    run K ALL (a+b) s = run K ALL b (run K ALL a s) := by
  induction a generalizing s with
  | zero => rw [Nat.zero_add, run_zero]
  | succ a ih =>
    rw [Nat.succ_add, run_succ, ih, run_succ]

theorem run_chain {K ALL a b : Nat} {s t u : LaneState}
    (ha : run K ALL a s = t) (hb : run K ALL b t = u) :
    run K ALL (a+b) s = u := by rw [run_add, ha, hb]

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

/-! A reusable sparse certificate rule. A finite return map on upper windows
replaces a long higher-width orbit check. The only extra witness checks are
the lower cycle's exceptional residues in the return map's finite orbit.
Existence of such a successful return map is an explicit hypothesis. -/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

def iter (J : Nat → Nat) : Nat → Nat → Nat
  | 0, u => u
  | n+1, u => J (iter J n u)

theorem iter_lt {J : Nat → Nat} {N u : Nat}
    (hJ : ∀ v, v < N → J v < N) (hu : u < N) (j : Nat) :
    iter J j u < N := by
  induction j with
  | zero => exact hu
  | succ j ih => exact hJ _ ih

theorem block_orbit {K L p N u : Nat} {J embed : Nat → Nat}
    (hJ : ∀ v, v < N → J v < N) (hu : u < N)
    (hstep : ∀ v, v < N → orb K L (embed v,p) = (embed (J v),p))
    (j : Nat) :
    orb K (L*j) (embed u,p) = (embed (iter J j u),p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Nat.mul_succ, orb_add, ih]
    exact hstep _ (iter_lt hJ hu j)

theorem period_return {K L p N u q : Nat} {J embed : Nat → Nat}
    (hJ : ∀ v, v < N → J v < N) (hu : u < N)
    (hstep : ∀ v, v < N → orb K L (embed v,p) = (embed (J v),p))
    (hcycle : iter J q u = u) :
    orb K (L*q) (embed u,p) = (embed u,p) := by
  rw [block_orbit hJ hu hstep q, hcycle]

theorem exceptional_residues {K S L p N u q : Nat}
    {J embed : Nat → Nat} {E : Nat → Prop}
    (hL : 0 < L) (hLe : L%2 = 0)
    (hJ : ∀ v, v < N → J v < N) (hu : u < N)
    (hstep : ∀ v, v < N → orb K L (embed v,p) = (embed (J v),p))
    (hchecks : ∀ j, j < q → ∀ e, e < L → e%2 = 1-p → E e →
      sig (S+1) (L*j+e) (orb K e (embed (iter J j u),p)).1 = true)
    (r : Nat) (hr : r < L*q) (hp : r%2 = 1-p) (he : E (r%L)) :
    sig (S+1) r (orb K r (embed u,p)).1 = true := by
  let j := r/L
  let e := r%L
  have hj : j < q := by dsimp [j]; exact (Nat.div_lt_iff_lt_mul hL).mpr (by simpa [Nat.mul_comm] using hr)
  have hel : e < L := Nat.mod_lt r hL
  have hm : e%2 = r%2 := Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hLe)
  have hd : r = L*j+e := (Nat.div_add_mod r L).symm
  have hs := hchecks j hj e hel (hm.trans hp) he
  rw [hd, orb_add, block_orbit hJ hu hstep j]
  exact hs

/-- The lower cycle may have exceptional residues. Check them only on the
finite upper return-map orbit. This theorem assumes, rather than asserts,
the needed finite return-map cycle and the exceptional white witnesses. -/
theorem return_map_cycle_lift
    {Klo Khi Slo Shi B p L N u q : Nat}
    {J embed : Nat → Nat} {E : Nat → Prop}
    (hK : Slo+1 ≤ Klo) (hwidth : Klo ≤ Khi) (hS : Slo ≤ Shi)
    (hp : p < 2) (hinit : LowEq Klo (embed u) B)
    (hL : 0 < L) (hLe : L%2 = 0) (hLo : orb Klo L (B,p) = (B,p))
    (hgood : ∀ r, r < L → r%2 = 1-p → ¬ E r →
      sig (Slo+1) r (orb Klo r (B,p)).1 = true)
    (hJ : ∀ v, v < N → J v < N) (hu : u < N)
    (hstep : ∀ v, v < N → orb Khi L (embed v,p) = (embed (J v),p))
    (hq : 0 < q) (hcycle : iter J q u = u)
    (hchecks : ∀ j, j < q → ∀ e, e < L → e%2 = 1-p → E e →
      sig (Shi+1) (L*j+e) (orb Khi e (embed (iter J j u),p)).1 = true) :
    Cycle Khi Shi (embed u) p (L*q) := by
  exact punctured_cycle_lift hK hwidth hS hp hinit hL hLe hLo
    (Nat.mul_pos hL hq) (by simp [Nat.mul_mod,hLe])
    (period_return hJ hu hstep hcycle) E hgood
    (exceptional_residues hL hLe hJ hu hstep hchecks)

/-! ### Modulo-`2^n` characterization of `LowEq`, multi-period universal front returns, and `iter` additivity -/

/-- **Equivalence Laws and Exact Modulo-`2^n` Characterization of `LowEq` (`lowEq_equiv_and_mod_two_pow_iff`).** -/
theorem lowEq_equiv_and_mod_two_pow_iff (n a b c : Nat) :
    LowEq n a a ∧
    (LowEq n a b → LowEq n b a) ∧
    (LowEq n a b → LowEq n b c → LowEq n a c) ∧
    (LowEq n a b ↔ a % 2 ^ n = b % 2 ^ n) := by
  refine ⟨fun _ _ => rfl,
          fun h i hi => (h i hi).symm,
          fun h1 h2 i hi => (h1 i hi).trans (h2 i hi),
          ⟨fun h => ?_, fun heq i hi => ?_⟩⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < n
    · simp [hi, h i hi]
    · simp [hi]
  · have hbit := congrArg (fun x => x.testBit i) heq
    simpa [Nat.testBit_mod_two_pow, hi] using hbit

/-- **Multi-Period Universal Front Orbit Invariance and `iter J` Additivity (`universal_front_period_mul_and_iter_add`).** -/
theorem universal_front_period_mul_and_iter_add (K a p t m : Nat) (J : Nat → Nat) (x y u : Nat)
    (ha : a < 2 ^ (K + 1)) (hp : p < 2) :
    Rule30ZeroBoundaryStripeFront.orb (K + 1) (t + m * 2 ^ (K + 1)) (a, p) =
      Rule30ZeroBoundaryStripeFront.orb (K + 1) t (a, p) ∧
    iter J (x + y) u = iter J y (iter J x u) := by
  refine ⟨?_, ?_⟩
  · induction m with
    | zero => simp
    | succ m ih =>
      rw [show t + (m + 1) * 2 ^ (K + 1) = (t + m * 2 ^ (K + 1)) + 2 ^ (K + 1) by
            rw [Nat.succ_mul]; omega,
          Rule30ZeroBoundaryStripeFront.orb_add, ih]
      have hbound : (Rule30ZeroBoundaryStripeFront.orb (K + 1) t (a, p)).1 < 2 ^ (K + 1) :=
        orbit_bound ha t
      have hph : (Rule30ZeroBoundaryStripeFront.orb (K + 1) t (a, p)).2 < 2 :=
        orbit_phase_lt (K + 1) a p t hp
      exact universal_front_period K _ _ hbound hph
  · induction y with
    | zero => rfl
    | succ y ih => exact congrArg J ih

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

