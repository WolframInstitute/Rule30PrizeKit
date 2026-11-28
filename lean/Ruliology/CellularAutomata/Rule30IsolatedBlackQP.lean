module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryPeriodLanes
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# `QP P` excludes every period-`P` word without two adjacent black cells

`Rule30ZeroBoundaryPeriodLanes.not_eventually_oneBlack_of_QP` excludes the word `0^(P-1) 1` from
`QP P`. The same argument needs only that the eventual center word never has two consecutive black
cells: at a black center step the next center cell is white, so the left neighbour must be black,
and the effective boundary `center t && center (t + 1)` of `Rule30DrivenLeft.cell_eq_L_effective`
is constantly white. A black step `t0` then repeats at `t0 + P * k`, which gives a finitely
supported zero-boundary start keeping column `-1` black at every `P`-th step.

* `not_eventually_isolated_of_QP`: if from some `T` on the center column is `P`-periodic, has no
  two consecutive black cells and has a black cell at some `t0 ≥ T`, then `QP P` fails.
* `not_eventuallyWord_isolated_of_QP`: the same for `Rule30StripCertificates.EventuallyWord w`, for
  every word `w` of length `P ≥ 2` with a black letter and no two cyclically adjacent black letters.

With `Rule30ZeroBoundaryPeriodLanes.QP_of_dvd`, `QP (N !)` for every `N` would exclude all such
words of every period. Nothing here proves any `QP P`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30IsolatedBlackQP

open Rule30Jen Rule30Prize Rule30DrivenLeft Rule30ZeroBoundaryPeriodLanes

/-- **Isolated black cells.** If the center column is `P`-periodic from `T` on, never has two
consecutive black cells from `T` on, and is black at some `t0 ≥ T`, then `QP P` fails. -/
theorem not_eventually_isolated_of_QP {P : Nat} (hP : 2 ≤ P) (hQ : QP P) :
    ¬ ∃ T t0, T ≤ t0 ∧ center t0 = true ∧ (∀ t, T ≤ t → center (t + P) = center t) ∧
      (∀ t, T ≤ t → (center t && center (t + 1)) = false) := by
  rintro ⟨T, t0', ht0', hb', hper, hiso⟩
  -- one period later, so that the start time is positive
  let t0 := t0' + P
  have ht0 : T ≤ t0 := by simp only [t0]; omega
  have hb : center t0 = true := by simp only [t0]; rw [hper t0' ht0']; exact hb'
  have hperk : ∀ k, center (t0 + P * k) = true := by
    intro k; induction k with
    | zero => simpa using hb
    | succ k ih =>
      rw [show t0 + P * (k + 1) = (t0 + P * k) + P by rw [Nat.mul_succ]; omega,
        hper _ (by omega)]; exact ih
  have hfun : (fun k => center (t0 + k) && center (t0 + k + 1)) = fun _ => false := by
    funext k; exact hiso _ (by omega)
  refine hQ t0 (fun p => cell t0 p) (by simp only [t0]; omega)
    (fun p hp => cell_eq_false_of_lt t0 p hp) (cell_left_edge t0) (fun k => ?_)
  have e := cell_eq_L_effective t0 (P * k) (-1) (by omega)
  rw [hfun] at e
  rw [e]
  have c0 : cell (t0 + P * k) 0 = true := hperk k
  have c1 : cell (t0 + P * k + 1) 0 = false := by
    have h := hiso (t0 + P * k) (by omega)
    rw [hperk k] at h
    have h' : center (t0 + P * k + 1) = false := by simpa using h
    exact h'
  have := cell_left (t0 + P * k) 0
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl, c0, c1] at this
  rw [this]; rfl

/-- **The reduction, as an eventual word.** For a word `w` of length `P ≥ 2` with a black letter
and no two cyclically adjacent black letters, `QP P` excludes
`Rule30StripCertificates.EventuallyWord w`. -/
theorem not_eventuallyWord_isolated_of_QP {P : Nat} (hP : 2 ≤ P) (hQ : QP P) {w : List Bool}
    (hlen : w.length = P) (hblack : ∃ i, i < P ∧ w.getD i false = true)
    (hiso : ∀ i, i < P → (w.getD i false && w.getD ((i + 1) % P) false) = false) :
    ¬ Rule30StripCertificates.EventuallyWord w := by
  rintro ⟨T, hT⟩
  rw [hlen] at hT
  obtain ⟨i, hi, hwi⟩ := hblack
  have hc : ∀ t, T ≤ t → center t = w.getD ((t - T) % P) false := fun t ht => hT t ht
  refine not_eventually_isolated_of_QP hP hQ ⟨T, T + i, by omega, ?_, fun t ht => ?_,
    fun t ht => ?_⟩
  · rw [hc _ (by omega), show T + i - T = i by omega, Nat.mod_eq_of_lt hi]; exact hwi
  · rw [hc _ (by omega), hc _ ht, show t + P - T = (t - T) + P by omega, Nat.add_mod_right]
  · rw [hc _ ht, hc _ (by omega), show t + 1 - T = (t - T) + 1 by omega,
      Nat.add_mod (t - T) 1 P, Nat.mod_eq_of_lt (show 1 < P by omega)]
    have h := hiso ((t - T) % P) (Nat.mod_lt _ (by omega))
    by_cases hlt : (t - T) % P + 1 < P
    · exact h
    · rw [show (t - T) % P + 1 = P by have := Nat.mod_lt (t - T) (show 0 < P by omega); omega,
        Nat.mod_self] at h ⊢
      exact h

/-! ### All-period `ThetaP` forced-row bijection, `2^((P-1)*n)` survivor law, Lucas word count -/

private theorem lev_mod_ne_and_fidx_lev {P : Nat} (hP : 2 ≤ P) (s : Nat) :
    (lev P s) % P ≠ 0 ∧ fidx P (lev P s) = s := by
  unfold lev fidx
  let q := s / (P - 1)
  let r := s % (P - 1)
  have hs : s = (P - 1) * q + r := (Nat.div_add_mod s (P - 1)).symm
  have hr : r < P - 1 := Nat.mod_lt s (by omega)
  have hmulP : (P - 1) * q + q = P * q := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left q (by omega))]
  have hlev : s + q + 1 = P * q + (r + 1) := by omega
  have hdiv : (s + q + 1) / P = q := by
    rw [hlev, Nat.add_comm (P * q) (r + 1), Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hmod : (s + q + 1) % P = r + 1 := by
    rw [hlev, Nat.add_comm (P * q) (r + 1), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_⟩
  · change (s + q + 1) % P ≠ 0; rw [hmod]; omega
  · change s + q + 1 - (s + q + 1) / P - 1 = s; rw [hdiv]; omega

/-- Column-`-1` sequence of a `QP P`-admissible zero-boundary evolution with free bits `f`. -/
def altP (P : Nat) (f : Nat → Bool) (t : Nat) : Bool :=
  if t % P = 0 then true else f (fidx P t)

/-- All-period forced-row reconstruction `ThetaP P f` generalizing `Rule30ZeroBoundary.Theta` (`P = 2`). -/
def ThetaP (P : Nat) (f : Nat → Bool) : Nat → Bool := Rule30ZeroBoundary.lam (altP P f)

/-- Constrained zero-boundary starts keeping depth `1` black at every `P`-th step. -/
def InXP (P : Nat) (L : Nat → Bool) : Prop := ∀ s, Rule30ZeroBoundary.zrow L (P * s) 1 = true

theorem ThetaP_col (P : Nat) (f : Nat → Bool) (t : Nat) :
    Rule30ZeroBoundary.zrow (ThetaP P f) t 1 = altP P f t :=
  (Rule30ZeroBoundary.realization (altP P f)).1 t

theorem ThetaP_inXP (P : Nat) (f : Nat → Bool) : InXP P (ThetaP P f) := by
  intro s; rw [ThetaP_col]; unfold altP
  rw [ite_eq_left (by simp [Nat.mul_mod_right])]

theorem ThetaP_free {P : Nat} (hP : 2 ≤ P) (f : Nat → Bool) (s : Nat) :
    Rule30ZeroBoundary.zrow (ThetaP P f) (lev P s) 1 = f s := by
  rw [ThetaP_col]; unfold altP
  obtain ⟨hne, hinv⟩ := lev_mod_ne_and_fidx_lev hP s
  rw [ite_eq_right hne, hinv]

/-- **Headline 1 (`inXP_iff_ThetaP`):** For every `P ≥ 2`, the starts keeping depth `1` black at all
multiples of `P` are **exact images of `ThetaP P`**, with free bits read at `lev P s`. -/
theorem inXP_iff_ThetaP {P : Nat} (hP : 2 ≤ P) (L : Nat → Bool) :
    InXP P L ↔ ∃ f : Nat → Bool, Rule30ZeroBoundary.zrow L 0 = ThetaP P f := by
  constructor
  · intro hX
    refine ⟨fun s => Rule30ZeroBoundary.zrow L (lev P s) 1, ?_⟩
    refine (Rule30ZeroBoundary.realization (altP P (fun s => Rule30ZeroBoundary.zrow L (lev P s) 1))).2 L fun t => ?_
    unfold altP
    by_cases ht : t % P = 0
    · rw [ite_eq_left ht]
      have hmul : P * (t / P) = t := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ht)
      rw [← hmul]; exact hX (t / P)
    · rw [ite_eq_right ht]; dsimp only; rw [lev_fidx hP ht]
  · rintro ⟨f, hf⟩ s
    rw [← Rule30ZeroBoundary.zrow_zero_run, hf]
    exact ThetaP_inXP P f s

/-- **Headline 2 (`QP_iff_ThetaP`):** All-period generalization of `Q01_iff_Theta`: for every `P ≥ 2`,
`QP P` holds if and only if `ThetaP P f` has infinite support for every free-bit stream `f`. -/
theorem QP_iff_ThetaP {P : Nat} (hP : 2 ≤ P) :
    QP P ↔ ∀ f : Nat → Bool, ¬ Rule30ZeroBoundary.FinSupp (ThetaP P f) := by
  rw [QP_iff_zrow P]
  constructor
  · intro hQ f hfin
    exact hQ (ThetaP P f) hfin (ThetaP_inXP P f)
  · intro hno L ⟨W, hW⟩ hX
    obtain ⟨f, hf⟩ := (inXP_iff_ThetaP hP L).mp hX
    refine hno f ⟨W, fun k hk => ?_⟩
    rw [← hf, Rule30ZeroBoundary.zrow_zero_of_pos L (by omega)]
    exact hW k hk

/-! ### Exact `2^((P - 1) * n)` survivor count across `P * n`-width zero-boundary seeds -/

def fitsQPBit (P t Y : Nat) : Bool :=
  (t % P != 0) || (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t Y).testBit 0

def qpExpandStep (P t : Nat) : List Nat → List Nat
  | [] => []
  | Y :: Ys =>
    let rest := qpExpandStep P t Ys
    let r1 := if fitsQPBit P t (Y + 2 ^ t) then (Y + 2 ^ t) :: rest else rest
    if fitsQPBit P t Y then Y :: r1 else r1

def qpSurvPrefixes (P : Nat) : Nat → List Nat
  | 0 => [0]
  | t + 1 => qpExpandStep P t (qpSurvPrefixes P t)

private theorem mem_qpExpandStep (P t : Nat) (xs : List Nat) (Z : Nat) :
    Z ∈ qpExpandStep P t xs ↔
      (Z ∈ xs ∧ fitsQPBit P t Z = true) ∨ (∃ X ∈ xs, Z = X + 2 ^ t ∧ fitsQPBit P t Z = true) := by
  induction xs with
  | nil => simp [qpExpandStep]
  | cons Y Ys ih =>
    unfold qpExpandStep
    cases h0 : fitsQPBit P t Y <;> cases h1 : fitsQPBit P t (Y + 2 ^ t)
    · simp only [Bool.false_eq_true, ite_false, List.mem_cons, ih]
      constructor
      · rintro (⟨hz, hfz⟩ | ⟨X, hX, rfl, hfz⟩)
        · exact Or.inl ⟨Or.inr hz, hfz⟩
        · exact Or.inr ⟨X, Or.inr hX, rfl, hfz⟩
      · rintro (⟨rfl | hz, hfz⟩ | ⟨X, rfl | hX, rfl, hfz⟩)
        · rw [h0] at hfz; exact Bool.noConfusion hfz
        · exact Or.inl ⟨hz, hfz⟩
        · rw [h1] at hfz; exact Bool.noConfusion hfz
        · exact Or.inr ⟨X, hX, rfl, hfz⟩
    · simp only [Bool.false_eq_true, ite_true, ite_false, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hz, hfz⟩ | ⟨X, hX, rfl, hfz⟩)
        · exact Or.inr ⟨Y, Or.inl rfl, rfl, h1⟩
        · exact Or.inl ⟨Or.inr hz, hfz⟩
        · exact Or.inr ⟨X, Or.inr hX, rfl, hfz⟩
      · rintro (⟨rfl | hz, hfz⟩ | ⟨X, rfl | hX, rfl, hfz⟩)
        · rw [h0] at hfz; exact Bool.noConfusion hfz
        · exact Or.inr (Or.inl ⟨hz, hfz⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨X, hX, rfl, hfz⟩)
    · simp only [Bool.false_eq_true, ite_true, ite_false, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hz, hfz⟩ | ⟨X, hX, rfl, hfz⟩)
        · exact Or.inl ⟨Or.inl rfl, h0⟩
        · exact Or.inl ⟨Or.inr hz, hfz⟩
        · exact Or.inr ⟨X, Or.inr hX, rfl, hfz⟩
      · rintro (⟨rfl | hz, hfz⟩ | ⟨X, rfl | hX, rfl, hfz⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hz, hfz⟩)
        · rw [h1] at hfz; exact Bool.noConfusion hfz
        · exact Or.inr (Or.inr ⟨X, hX, rfl, hfz⟩)
    · simp only [ite_true, List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | ⟨hz, hfz⟩ | ⟨X, hX, rfl, hfz⟩)
        · exact Or.inl ⟨Or.inl rfl, h0⟩
        · exact Or.inr ⟨Y, Or.inl rfl, rfl, h1⟩
        · exact Or.inl ⟨Or.inr hz, hfz⟩
        · exact Or.inr ⟨X, Or.inr hX, rfl, hfz⟩
      · rintro (⟨rfl | hz, hfz⟩ | ⟨X, rfl | hX, rfl, hfz⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨hz, hfz⟩))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr ⟨X, hX, rfl, hfz⟩))

private theorem qpSurvPrefixes_lt (P : Nat) : ∀ (t Y : Nat), Y ∈ qpSurvPrefixes P t → Y < 2 ^ t
  | 0, Y, h => by simp [qpSurvPrefixes] at h; omega
  | t + 1, Y, h => by
    change Y ∈ qpExpandStep P t (qpSurvPrefixes P t) at h
    rw [mem_qpExpandStep] at h
    rcases h with ⟨hY, _⟩ | ⟨X, hX, rfl, _⟩
    · have := qpSurvPrefixes_lt P t Y hY; rw [Nat.pow_succ]; omega
    · have := qpSurvPrefixes_lt P t X hX; rw [Nat.pow_succ]; omega

private theorem iterF_flip_top (t Y : Nat) (hY : Y < 2 ^ t) :
    (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t (Y + 2 ^ t)).testBit 0 =
      !((Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t Y).testBit 0) := by
  rw [← Rule30ZeroBoundary.IntegerForm.zrow_rowOfNat_col1,
      ← Rule30ZeroBoundary.IntegerForm.zrow_rowOfNat_col1]
  have haff := Rule30ZeroBoundary.zrow_aff t
    (Rule30ZeroBoundary.IntegerForm.rowOfNat (Y + 2 ^ t))
    (Rule30ZeroBoundary.IntegerForm.rowOfNat Y) 1 (by omega) (fun i hi1 hi2 => ?_)
  · rw [show 1 + t = t + 1 by omega] at haff
    have htop1 : Rule30ZeroBoundary.IntegerForm.rowOfNat (Y + 2 ^ t) (t + 1) = true := by
      change (Y + 2 ^ t).testBit t = true
      rw [← Nat.or_two_pow_eq_add_of_lt hY, Nat.testBit_or, Nat.testBit_two_pow]
      simp [Nat.testBit_lt_two_pow hY]
    have htop2 : Rule30ZeroBoundary.IntegerForm.rowOfNat Y (t + 1) = false :=
      Nat.testBit_lt_two_pow hY
    rw [htop1, htop2] at haff
    revert haff
    cases Rule30ZeroBoundary.zrow (Rule30ZeroBoundary.IntegerForm.rowOfNat (Y + 2 ^ t)) t 1 <;>
      cases Rule30ZeroBoundary.zrow (Rule30ZeroBoundary.IntegerForm.rowOfNat Y) t 1 <;> decide
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Rule30ZeroBoundary.IntegerForm.rowOfNat]
    rw [← Nat.or_two_pow_eq_add_of_lt hY, Nat.testBit_or, Nat.testBit_two_pow]
    simp [show t ≠ j by omega]

private theorem iterF_local (t W Y1 Y2 : Nat) (ht : t < W) (hmod : Y1 % 2 ^ W = Y2 % 2 ^ W) :
    (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t Y1).testBit 0 =
      (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t Y2).testBit 0 := by
  rw [← Rule30ZeroBoundary.IntegerForm.zrow_rowOfNat_col1,
      ← Rule30ZeroBoundary.IntegerForm.zrow_rowOfNat_col1]
  refine Rule30ZeroBoundary.zrow_light_cone t 1 (fun i hi1 hi2 => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Rule30ZeroBoundary.IntegerForm.rowOfNat]
  have hjW : j < W := by omega
  have h1 := Nat.testBit_mod_two_pow Y1 W j
  have h2 := Nat.testBit_mod_two_pow Y2 W j
  simp only [hjW, decide_true, Bool.true_and] at h1 h2
  rw [← h1, ← h2, hmod]

private theorem mem_qpSurvPrefixes_iff (P : Nat) : ∀ (W Y : Nat),
    Y ∈ qpSurvPrefixes P W ↔ Y < 2 ^ W ∧ ∀ t, t < W → fitsQPBit P t Y = true
  | 0, Y => by simp [qpSurvPrefixes]
  | t + 1, Y => by
    change Y ∈ qpExpandStep P t (qpSurvPrefixes P t) ↔ _
    rw [mem_qpExpandStep]
    constructor
    · rintro (⟨hY, hft⟩ | ⟨X, hX, rfl, hft⟩)
      · obtain ⟨hYlt, hall⟩ := (mem_qpSurvPrefixes_iff P t Y).mp hY
        refine ⟨by rw [Nat.pow_succ]; omega, fun k hk => if hkt : k = t then hkt ▸ hft else hall k (by omega)⟩
      · obtain ⟨hXlt, hall⟩ := (mem_qpSurvPrefixes_iff P t X).mp hX
        refine ⟨by rw [Nat.pow_succ]; omega, fun k hk => ?_⟩
        by_cases hkt : k = t
        · subst hkt; exact hft
        · unfold fitsQPBit
          rw [iterF_local k t (X + 2 ^ t) X (by omega) (by rw [Nat.add_mod_right])]
          exact hall k (by omega)
    · rintro ⟨hlt, hall⟩
      let X := Y % 2 ^ t
      have hXlt : X < 2 ^ t := Nat.mod_lt Y (Nat.two_pow_pos t)
      have hXmem : X ∈ qpSurvPrefixes P t := by
        refine (mem_qpSurvPrefixes_iff P t X).mpr ⟨hXlt, fun k hk => ?_⟩
        unfold fitsQPBit
        rw [iterF_local k t X Y hk (Nat.mod_mod Y (2 ^ t))]
        exact hall k (by omega)
      have hq2 : Y / 2 ^ t < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos t)).mpr
        (by rw [Nat.mul_comm, ← Nat.pow_succ]; exact hlt)
      have hsplit : 2 ^ t * (Y / 2 ^ t) + X = Y := Nat.div_add_mod Y (2 ^ t)
      rcases hq_eq : Y / 2 ^ t with _ | _ | k
      · rw [hq_eq, Nat.mul_zero, Nat.zero_add] at hsplit
        exact Or.inl ⟨hsplit ▸ hXmem, hall t (by omega)⟩
      · rw [hq_eq, Nat.mul_one, Nat.add_comm] at hsplit
        exact Or.inr ⟨X, hXmem, hsplit.symm, hall t (by omega)⟩
      · rw [hq_eq] at hq2; omega

private theorem qpExpandStep_len_free (P t : Nat) (hne : t % P ≠ 0) : ∀ xs : List Nat,
    (qpExpandStep P t xs).length = 2 * xs.length
  | [] => rfl
  | Y :: Ys => by
    have hb : (t % P != 0) = true := bne_iff_ne.mpr hne
    have hf0 : fitsQPBit P t Y = true := by simp [fitsQPBit, hb]
    have hf1 : fitsQPBit P t (Y + 2 ^ t) = true := by simp [fitsQPBit, hb]
    simp only [qpExpandStep, hf0, hf1, ite_true, List.length_cons, qpExpandStep_len_free P t hne Ys]
    omega

private theorem qpExpandStep_len_pin (P t : Nat) (h0 : t % P = 0) :
    ∀ xs : List Nat, (∀ Y ∈ xs, Y < 2 ^ t) → (qpExpandStep P t xs).length = xs.length
  | [], _ => rfl
  | Y :: Ys, hlt => by
    have hYlt : Y < 2 ^ t := hlt Y (List.mem_cons_self ..)
    have hflip : fitsQPBit P t (Y + 2 ^ t) = !(fitsQPBit P t Y) := by
      simp [fitsQPBit, h0, iterF_flip_top t Y hYlt]
    have ih := qpExpandStep_len_pin P t h0 Ys (fun X hX => hlt X (List.mem_cons_of_mem Y hX))
    unfold qpExpandStep
    rw [hflip]
    cases fitsQPBit P t Y <;> simp [ih]

private theorem qpSurvPrefixes_step_len (P t : Nat) :
    (qpSurvPrefixes P (t + 1)).length =
      if t % P = 0 then (qpSurvPrefixes P t).length else 2 * (qpSurvPrefixes P t).length := by
  change (qpExpandStep P t (qpSurvPrefixes P t)).length = _
  by_cases h0 : t % P = 0
  · rw [ite_eq_left h0]; exact qpExpandStep_len_pin P t h0 _ (qpSurvPrefixes_lt P t)
  · rw [ite_eq_right h0]; exact qpExpandStep_len_free P t h0 _

private theorem qpSurvPrefixes_block_len {P : Nat} (_hP : 1 ≤ P) (base : Nat) (hbase : base % P = 0) :
    ∀ r : Nat, r ≤ P →
      (qpSurvPrefixes P (base + r)).length =
        if r = 0 then (qpSurvPrefixes P base).length else 2 ^ (r - 1) * (qpSurvPrefixes P base).length
  | 0, _ => by simp
  | 1, _ => by
    rw [show base + 1 = base + 0 + 1 by omega, Nat.add_zero, qpSurvPrefixes_step_len P base, ite_eq_left hbase]
    simp
  | r + 2, hr => by
    have ih := qpSurvPrefixes_block_len _hP base hbase (r + 1) (by omega)
    rw [show base + (r + 2) = (base + (r + 1)) + 1 by omega, qpSurvPrefixes_step_len P (base + (r + 1))]
    have hmod : (base + (r + 1)) % P ≠ 0 := by
      rw [Nat.add_mod, hbase, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]; omega
    rw [ite_eq_right hmod, ih, ite_eq_right (by omega), ite_eq_right (by omega)]
    show 2 * (2 ^ r * (qpSurvPrefixes P base).length) = 2 ^ (r + 1) * (qpSurvPrefixes P base).length
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc]

/-- **Headline 3 (`qp_survivor_count_exact`):** For every period `P ≥ 1` and horizon `n : Nat`,
out of all `2^(P * n)` zero-boundary prefixes `Y < 2^(P * n)`, **exact count `2^((P - 1) * n)`**
satisfy the `QP P` constraint across the first `n` multiples of `P`. -/
theorem qp_survivor_count_exact {P : Nat} (hP : 1 ≤ P) (n : Nat) :
    (qpSurvPrefixes P (P * n)).length = 2 ^ ((P - 1) * n) ∧
    ∀ Y : Nat, Y ∈ qpSurvPrefixes P (P * n) ↔ Y < 2 ^ (P * n) ∧ ∀ t, t < P * n → fitsQPBit P t Y = true := by
  refine ⟨?_, fun Y => mem_qpSurvPrefixes_iff P (P * n) Y⟩
  induction n with
  | zero => simp [qpSurvPrefixes]
  | succ n ih =>
    rw [Nat.mul_succ]
    have hblk := qpSurvPrefixes_block_len hP (P * n) (Nat.mul_mod_right P n) P (Nat.le_refl P)
    rw [hblk, ite_eq_right (by omega), ih, ← Nat.pow_add]
    congr 1; rw [Nat.mul_succ]; omega

/-! ### Exact Lucas count `lucasQP P - 1` of isolated-black periodic words -/

def fibQP : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibQP (n + 1) + fibQP n

def lucasQP : Nat → Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => lucasQP (n + 1) + lucasQP n

private theorem lucasQP_eq_fib_pair (n : Nat) :
    lucasQP (n + 1) = fibQP (n + 2) + fibQP n ∧ lucasQP (n + 2) = fibQP (n + 3) + fibQP (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h1 := ih.1; have h2 := ih.2
    show lucasQP (n + 2) + lucasQP (n + 1) = (fibQP (n + 3) + fibQP (n + 2)) + (fibQP (n + 1) + fibQP n)
    omega

private theorem nodup_map_of_inj {α β : Type} {f : α → β} {xs : List α}
    (hnd : xs.Nodup) (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hnd
    refine ⟨?_, ih hnd.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨b, hb, hfb⟩ := hmem
    have hab := hinj b (List.mem_cons_of_mem a hb) a (List.mem_cons_self ..) hfb
    exact hnd.1 (hab ▸ hb)

def linIsoWords : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | n + 2 => (linIsoWords (n + 1)).map (false :: ·) ++ (linIsoWords n).map (fun w => true :: false :: w)

private theorem linIsoWords_len (n : Nat) : (linIsoWords n).length = fibQP (n + 2) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | m
    · rfl
    · rfl
    · simp [linIsoWords, ih (m + 1) (by omega), ih m (by omega), fibQP]

def cycIsoWords (P : Nat) : List (List Bool) :=
  match P with
  | 0 => [[]]
  | 1 => [[false]]
  | 2 => [[false, false], [false, true], [true, false]]
  | m + 3 =>
    (linIsoWords (m + 2)).map (false :: ·) ++
    (linIsoWords m).map (fun w => true :: false :: (w ++ [false]))

def hasBlack (w : List Bool) : Bool := w.any (· == true)

def isolatedBlackWords (P : Nat) : List (List Bool) :=
  (cycIsoWords P).filter hasBlack

private theorem replicate_false_mem_lin : ∀ n : Nat, List.replicate n false ∈ linIsoWords n
  | 0 => by simp [linIsoWords]
  | 1 => by simp [linIsoWords]
  | n + 2 => by
    simp only [List.replicate_succ, linIsoWords, List.mem_append, List.mem_map]
    exact Or.inl ⟨List.replicate (n + 1) false, replicate_false_mem_lin (n + 1), rfl⟩

private theorem linIsoWords_nodup : ∀ n : Nat, (linIsoWords n).Nodup
  | 0 => by simp [linIsoWords]
  | 1 => by decide
  | n + 2 => by
    unfold linIsoWords
    rw [List.nodup_append]
    refine ⟨nodup_map_of_inj (linIsoWords_nodup (n + 1)) (fun _ _ _ _ h => (List.cons.inj h).2),
            nodup_map_of_inj (linIsoWords_nodup n) (fun _ _ _ _ h => (List.cons.inj (List.cons.inj h).2).2), ?_⟩
    intro x hx y hy hxy
    rw [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, rfl⟩ := hy
    exact Bool.noConfusion (List.cons.inj hxy).1

private theorem filter_comp_len {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [List.filter, hp] <;> omega

private theorem filter_hasBlack_len {xs : List (List Bool)} (hnd : xs.Nodup) {z : List Bool}
    (hz_mem : z ∈ xs) (hz_f : hasBlack z = false)
    (honly : ∀ w ∈ xs, hasBlack w = false → w = z) :
    (xs.filter hasBlack).length + 1 = xs.length := by
  have hsingle : xs.filter (fun w => !hasBlack w) = [z] := by
    induction xs with
    | nil => cases hz_mem
    | cons a as ih =>
      rw [List.nodup_cons] at hnd
      by_cases ha : a = z
      · subst ha
        have hall_nil : as.filter (fun w => !hasBlack w) = [] := by
          rw [List.filter_eq_nil_iff]
          intro w hw hnot
          have hwf : hasBlack w = false := by cases h : hasBlack w <;> simp_all
          exact hnd.1 (honly w (List.mem_cons_of_mem a hw) hwf ▸ hw)
        simp only [List.filter, hz_f, Bool.not_false, hall_nil]
      · have haf : hasBlack a = true := by
          cases hf : hasBlack a
          · exact absurd (honly a (List.mem_cons_self ..) hf) ha
          · rfl
        have hzm : z ∈ as := by cases hz_mem with | head => exact absurd rfl ha | tail _ hm => exact hm
        have hrec := ih hnd.2 hzm (fun w hw => honly w (List.mem_cons_of_mem a hw))
        rw [List.filter_cons_of_neg (by simp [haf])]
        exact hrec
  have hcomp := filter_comp_len xs hasBlack
  rw [hsingle] at hcomp; simp only [List.length_singleton] at hcomp; exact hcomp

private theorem linIsoWords_len_eq : ∀ {n : Nat} {w : List Bool}, w ∈ linIsoWords n → w.length = n
  | 0, w, h => by simp [linIsoWords] at h; subst h; rfl
  | 1, w, h => by simp [linIsoWords] at h; rcases h with rfl | rfl <;> rfl
  | n + 2, w, h => by
    simp only [linIsoWords, List.mem_append, List.mem_map] at h
    rcases h with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · simp [linIsoWords_len_eq hu]
    · simp [linIsoWords_len_eq hu]

private theorem all_false_eq_replicate : ∀ (w : List Bool), hasBlack w = false → w = List.replicate w.length false
  | [], _ => rfl
  | false :: ws, h => by
    have hws : hasBlack ws = false := h
    rw [List.length_cons, List.replicate_succ]
    exact congrArg (false :: ·) (all_false_eq_replicate ws hws)
  | true :: _, h => by unfold hasBlack at h; simp [List.any] at h

private theorem hasBlack_replicate_false : ∀ k : Nat, hasBlack (List.replicate k false) = false
  | 0 => rfl
  | k + 1 => hasBlack_replicate_false k

private theorem lin_no_adj : ∀ {n : Nat} {w : List Bool}, w ∈ linIsoWords n →
    ∀ i, i + 1 < n → (w.getD i false && w.getD (i + 1) false) = false
  | 0, _, _, _, hi => by omega
  | 1, _, _, _, hi => by omega
  | n + 2, _, h, i, hi => by
    simp only [linIsoWords, List.mem_append, List.mem_map] at h
    rcases h with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · cases i with
      | zero => simp [List.getD]
      | succ j => exact lin_no_adj hu j (by omega)
    · rcases i with _ | _ | j
      · rfl
      · simp [List.getD]
      · exact lin_no_adj hu j (by omega)

private theorem getD_snoc_false : ∀ (u : List Bool) (idx : Nat),
    (u ++ [false]).getD idx false = if idx < u.length then u.getD idx false else false
  | [], idx => by cases idx <;> rfl
  | _ :: _, 0 => rfl
  | _ :: bs, idx + 1 => by
    show (bs ++ [false]).getD idx false = if idx + 1 < bs.length + 1 then bs.getD idx false else false
    rw [getD_snoc_false bs idx]
    by_cases h : idx < bs.length
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- **Headline 4 (`isolatedBlackWords_count_eq_lucas`):** For every period `P ≥ 2`, `isolatedBlackWords P`
contains exact count `lucasQP P - 1` words, and every word `w ∈ isolatedBlackWords P` satisfies the
hypotheses of `not_eventuallyWord_isolated_of_QP` (so `QP P` excludes all `lucasQP P - 1` of them). -/
theorem isolatedBlackWords_count_eq_lucas {P : Nat} (hP : 2 ≤ P) :
    (isolatedBlackWords P).length = lucasQP P - 1 ∧
    ∀ w ∈ isolatedBlackWords P, w.length = P ∧
      (∃ i, i < P ∧ w.getD i false = true) ∧
      (∀ i, i < P → (w.getD i false && w.getD ((i + 1) % P) false) = false) := by
  obtain ⟨d, rfl⟩ : ∃ d, P = d + 2 := ⟨P - 2, by omega⟩
  cases d with
  | zero => decide
  | succ m =>
    rw [show m + 1 + 2 = m + 3 by omega]
    refine ⟨?_, ?_⟩
    · have htot : (cycIsoWords (m + 3)).length = lucasQP (m + 3) := by
        simp only [cycIsoWords, List.length_append, List.length_map, linIsoWords_len]
        exact ((lucasQP_eq_fib_pair (m + 1)).2).symm
      have hnd : (cycIsoWords (m + 3)).Nodup := by
        unfold cycIsoWords
        rw [List.nodup_append]
        refine ⟨nodup_map_of_inj (linIsoWords_nodup (m + 2)) (fun _ _ _ _ h => (List.cons.inj h).2),
                nodup_map_of_inj (linIsoWords_nodup m) (fun _ _ _ _ h => ?_), ?_⟩
        · have h2 := (List.cons.inj (List.cons.inj h).2).2
          exact List.append_inj_left' h2 rfl
        · intro x hx y hy hxy
          rw [List.mem_map] at hx hy
          obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, rfl⟩ := hy
          exact Bool.noConfusion (List.cons.inj hxy).1
      have hz_mem : List.replicate (m + 3) false ∈ cycIsoWords (m + 3) := by
        simp only [List.replicate_succ, cycIsoWords, List.mem_append, List.mem_map]
        exact Or.inl ⟨List.replicate (m + 2) false, replicate_false_mem_lin (m + 2), rfl⟩
      have hz_f : hasBlack (List.replicate (m + 3) false) = false := hasBlack_replicate_false (m + 3)
      have honly : ∀ w ∈ cycIsoWords (m + 3), hasBlack w = false → w = List.replicate (m + 3) false := by
        intro w hw hf
        have hlen : w.length = m + 3 := by
          simp only [cycIsoWords, List.mem_append, List.mem_map] at hw
          rcases hw with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> simp [linIsoWords_len_eq hu]
        rw [← hlen]; exact all_false_eq_replicate w hf
      have hflen := filter_hasBlack_len hnd hz_mem hz_f honly
      unfold isolatedBlackWords
      omega
    · intro w hw
      unfold isolatedBlackWords at hw
      rw [List.mem_filter] at hw
      obtain ⟨hw_cyc, hw_any⟩ := hw
      have hlen : w.length = m + 3 := by
        simp only [cycIsoWords, List.mem_append, List.mem_map] at hw_cyc
        rcases hw_cyc with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> simp [linIsoWords_len_eq hu]
      have hblk : ∃ i, i < m + 3 ∧ w.getD i false = true := by
        unfold hasBlack at hw_any
        rw [List.any_eq_true] at hw_any
        obtain ⟨b, hb_mem, hb_eq⟩ := hw_any
        simp at hb_eq; subst hb_eq
        obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hb_mem
        refine ⟨i, hlen ▸ hi, ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hget]
      refine ⟨hlen, hblk, ?_⟩
      simp only [cycIsoWords, List.mem_append, List.mem_map] at hw_cyc
      rcases hw_cyc with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · intro i hi
        by_cases hlast : i = m + 2
        · subst hlast
          have hmod0 : (m + 2 + 1) % (m + 3) = 0 := Nat.mod_self (m + 3)
          rw [hmod0]; simp [List.getD]
        · rw [Nat.mod_eq_of_lt (by omega)]
          cases i with
          | zero => simp [List.getD]
          | succ j => exact lin_no_adj hu j (by omega)
      · intro i hi
        have hulen : u.length = m := linIsoWords_len_eq hu
        by_cases hlast : i = m + 2
        · subst hlast
          have hget_end : (true :: false :: (u ++ [false])).getD (m + 2) false = false := by
            change (u ++ [false]).getD m false = false
            rw [getD_snoc_false, hulen, ite_eq_right (by omega)]
          rw [hget_end]; rfl
        · rw [Nat.mod_eq_of_lt (by omega)]
          rcases i with _ | _ | j
          · rfl
          · simp [List.getD]
          · change ((u ++ [false]).getD j false && (u ++ [false]).getD (j + 1) false) = false
            rw [getD_snoc_false, getD_snoc_false, hulen]
            by_cases hjm : j + 1 < m
            · rw [ite_eq_left (by omega), ite_eq_left hjm]; exact lin_no_adj hu j hjm
            · rw [ite_eq_right hjm, Bool.and_false]

end Rule30IsolatedBlackQP
end Ruliology.CellularAutomata
