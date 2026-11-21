module

public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30DrivenLeftWindows

/-!
# Early repetitions in the readings beside a proposed periodic center

For the singleton and any proposed period, read column +1 only when the
center is white. Repetition of whole cycles of these readings and periodicity
of the center imply a repeated interval in column -1. The finite-window bound
in Rule30DrivenLeftWindows, based on David Condrey's quantitative form of
Jen's argument, then bounds the length of the repeated interval.

There is also an unconditional three-letter observation of the singleton.
Record a black center as one letter and distinguish the two right-neighbor
colors at a white center. From any positive age T, the second occurrence of
a length-n block starts at j with n ≤ T + j. Theorem 1.4 of Bugeaud, Kaneko
and Kim (https://arxiv.org/html/2510.17177v3) implies on paper that the
limsup of factor complexity divided by n is at least 4/3. The same conclusion
holds for the masked cycle letters of any proposed periodic center. Neither
assertion bounds the complexity of the center column alone.

For a constrained zero-boundary row the even wall readings are fixed. A
repeat of W consecutive odd readings therefore determines an interval of
the row at two different times. If that interval reaches the later left
edge, the same cell would be white in the earlier row and black in the later.

For kick gaps 3 and 5 with no adjacent 3s, n consecutive gaps last at least
4n−1 white slots. This converts the spatial test to a bound on repeats in
the gap *order*, independently of the order's periodicity or frequencies.
The hypotheses allow any finite delay before the first observed kick.

For r(n) the first prefix containing two equal length-n factors, the second
occurrence starts at j = r(n) - n. The gap inequality implies liminf r(n)/n
is at least 9/5 for any such finite left start. Bugeaud and Kim, Theorems 3.4
and 3.6 (https://arxiv.org/abs/1510.00279), bound this exponent by
sqrt(10) - 3/2 for Sturmian and quasi-Sturmian words. The resulting exclusion
uses their published theorem externally. Whether a given driven right half
has sufficiently early repetitions requires a separate argument.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30GapRepetitions

open Rule30ZeroBoundary
open Rule30PeriodTwoSideways (Psi u Psi_free Psi_inX)

/-- A kick is a black right-neighbor reading on a white phase. On the
compatible left half it is the complement of the odd depth-one reading. -/
def kicks (L : Nat → Bool) (s : Nat) := !(zrow L (2 * s + 1) 1)

def BlockEq {α : Type} (v : Nat → α) (i j n : Nat) : Prop :=
  ∀ k, k < n → v (i + k) = v (j + k)

/-- At a black center the right-hand reading is masked by the OR. -/
def freeRight (t : Nat) : Bool := !(Rule30Jen.cell t 0) && Rule30Jen.cell t 1

/-- Two windows of the genuine singleton with the same center readings
and the same unmasked right readings cannot reach the later edge. -/
theorem singleton_mask_window {s t w : Nat} (hs : 0 < s) (st : s < t)
    (center : ∀ k, k ≤ w → Rule30Jen.cell (s + k) 0 = Rule30Jen.cell (t + k) 0)
    (right : BlockEq freeRight s t w) : w < t := by
  let c := fun k => Rule30Jen.cell (s + k) 0
  let row := Rule30Jen.cell s
  have bound := Rule30DrivenLeftWindows.column_neg_one_period_window_bound_local c row
    (P := t - s) (m := s) (T := 0) (N := w) (by omega) hs (by
      intro k _ hk
      simpa only [c, show s + (k + (t - s)) = t + k by omega] using (center k (by omega)).symm)
    (Rule30Jen.cell_eq_false_of_lt s) (Rule30Jen.cell_left_edge s) (by
      intro k _ hk
      change Rule30DrivenLeft.L (fun k => Rule30Jen.cell (s + k) 0) (Rule30Jen.cell s) _ (-1) = _
      rw [Rule30DrivenLeft.cell_eq_L s _ _ (by decide)]
      change _ = Rule30DrivenLeft.L (fun k => Rule30Jen.cell (s + k) 0) (Rule30Jen.cell s) _ (-1)
      rw [Rule30DrivenLeft.cell_eq_L s _ _ (by decide), show s + (k + (t - s)) = t + k by omega]
      rw [show (-1 : Int) = 0 - 1 by decide, Rule30Jen.cell_left (t + k) 0,
        Rule30Jen.cell_left (s + k) 0]
      have a := center k (by omega)
      have b := center (k + 1) (by omega)
      have r := right k (by omega)
      simp only [freeRight] at r
      rw [Nat.add_assoc, Nat.add_assoc, ← b, ← a]
      cases h : Rule30Jen.cell (s + k) 0 <;> simp [h, ← a] at r ⊢
      rw [r])
  omega

/-- The actual singleton gives three possible letters: black center, or white
center with a white or black right neighbor. -/
def observed (t : Nat) : Bool × Bool := (Rule30Prize.center t, freeRight t)

/-- Unconditional repetition bound for this three-letter trace from any
positive age. An n-letter match supplies n center readings and n-1 usable
updates. In particular the earliest second start is at least n-T. -/
theorem singleton_observed_repeat_bound {T i j n : Nat} (age : 0 < T)
    (ij : i < j) (eq : BlockEq (fun k => observed (T + k)) i j n) : n ≤ T + j := by
  cases n with
  | zero => omega
  | succ n =>
    have bound := singleton_mask_window (s := T + i) (t := T + j) (w := n)
      (by omega) (by omega) (by
        intro k hk
        simpa only [observed, Rule30Prize.center, Nat.add_assoc] using
          congrArg Prod.fst (eq k (by omega))) (by
        intro k hk
        simpa only [observed, Nat.add_assoc] using congrArg Prod.snd (eq k (by omega)))
    omega

/-- One letter per proposed center cycle, retaining exactly the free right readings. -/
def cycleRight (T P i : Nat) (phase : Fin P) := freeRight (T + i * P + phase.val)

/-- For any period of the actual singleton center, two equal blocks of cycle
letters of length n at i < j must satisfy nP < T+jP. The onset can always
be chosen positive. There is no hypothesis on the rest of the right half. -/
theorem singleton_cycle_repeat_bound {T P i j n : Nat} (hT : 0 < T) (hp : 0 < P)
    (per : ∀ t, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t)
    (ij : i < j) (eq : BlockEq (cycleRight T P) i j n) : n * P < T + j * P := by
  have mul_lt := Nat.mul_lt_mul_of_pos_right ij hp
  apply singleton_mask_window (s := T + i * P) (by omega) (by omega)
  · have periodic (a k : Nat) :
        Rule30Prize.center (T + a * P + k) = Rule30Prize.center (T + k) := by
      induction a with
      | zero => simp
      | succ a ih =>
        rw [Nat.succ_mul, show T + (a * P + P) + k = (T + a * P + k) + P by omega, per _ (by omega), ih]
    exact fun k _ => (periodic i k).trans (periodic j k).symm
  · intro k hk
    have q : k / P < n := (Nat.div_lt_iff_lt_mul hp).mpr hk
    have part := congrFun (eq (k / P) q) (⟨k % P, Nat.mod_lt _ hp⟩ : Fin P)
    have unroll (a : Nat) : T + (a + k / P) * P + k % P = T + a * P + k := by
      rw [Nat.add_mul]
      have h := Nat.mod_add_div k P
      rw [Nat.mul_comm P (k / P)] at h
      omega
    simpa only [cycleRight, unroll] using part

/-- The time of each successive kick and the full contents of each gap. -/
structure KickClock (v : Nat → Bool) where
  time : Nat → Nat
  gap : Nat → Nat
  next : ∀ i, time (i + 1) = time i + gap i
  lengths : ∀ i, gap i = 3 ∨ gap i = 5
  readGap : ∀ i k, k < gap i → v (time i + k) = decide (k = 0)

def duration (g : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => g i + duration g (i + 1) n

private theorem same_samples {v : Nat → Bool} (c : KickClock v) (i j n : Nat)
    (eq : BlockEq c.gap i j n) : BlockEq v (c.time i) (c.time j) (duration c.gap i n) := by
  induction n generalizing i j with
  | zero => intro k hk; simp [duration] at hk
  | succ n ih =>
    have first : c.gap i = c.gap j := by simpa using eq 0 (by omega)
    have tail : BlockEq c.gap (i + 1) (j + 1) n := by
      intro k hk
      simpa only [show i + 1 + k = i + (k + 1) by omega, show j + 1 + k = j + (k + 1) by omega] using eq (k + 1) (by omega)
    intro k hk
    by_cases small : k < c.gap i
    · rw [c.readGap i k small, c.readGap j k (by omega)]
    · simp only [duration] at hk
      have h := ih (i + 1) (j + 1) tail (k - c.gap i) (by omega)
      rw [c.next, c.next] at h
      simpa only [show c.time i + c.gap i + (k - c.gap i) = c.time i + k by omega,
        show c.time j + c.gap j + (k - c.gap i) = c.time j + k by omega] using h

private theorem time_strict {v : Nat → Bool} (c : KickClock v) (i j : Nat) (lt : i < j) :
    c.time i < c.time j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [c.next]
    have := c.lengths j
    by_cases h : i = j
    · subst i; omega
    · have := ih (by omega); omega

private theorem time_upper {v : Nat → Bool} (c : KickClock v) (j : Nat) :
    c.time j ≤ c.time 0 + 5 * j := by
  induction j with
  | zero => simp
  | succ j ih => rw [c.next]; have := c.lengths j; omega

private theorem span_lower {v : Nat → Bool} (c : KickClock v)
    (sep : ∀ i, c.gap i = 3 → c.gap (i + 1) ≠ 3) :
    ∀ n i, 4 * n ≤ duration c.gap i n + 1
  | 0, _ => by simp
  | 1, i => by simp only [duration]; have := c.lengths i; omega
  | n + 2, i => by
    have := span_lower c sep n (i + 1 + 1)
    have a := c.lengths i
    have b := c.lengths (i + 1)
    have h := sep i
    simp only [duration]
    omega

/-- Equal kick windows must end their reconstruction short of the later edge. -/
theorem repeat_before_edge {L : Nat → Bool} (hX : InX L) {m : Nat}
    (hm : 1 ≤ m) (black : L m = true) (white : ∀ k, m < k → L k = false)
    {s t w : Nat} (st : s < t) (eq : BlockEq (kicks L) s t w) :
    2 * w + 1 < m + 2 * t := by
  have bound := jen_clock hm black white (T := 2 * s) (P := 2 * (t - s))
    (ℓ := 2 * (t - s) + 2 * w) (by omega) (by
      intro tick start stop
      by_cases even : tick % 2 = 0
      · rw [show tick + 2 * (t - s) = 2 * (tick / 2 + (t - s)) by omega, hX,
            show tick = 2 * (tick / 2) by omega, hX]
      · have h := congrArg Bool.not (eq (tick / 2 - s) (by omega))
        simp only [kicks, Bool.not_not] at h
        rw [show tick = 2 * (s + (tick / 2 - s)) + 1 by omega,
          show 2 * (s + (tick / 2 - s)) + 1 + 2 * (t - s) = 2 * (t + (tick / 2 - s)) + 1 by omega]
        exact h.symm)
  omega

/-- A finite-width obstruction measured in gap symbols. The clock times
are counted in white slots, so time 0 of the gap list can come after startup. -/
theorem gap_repeat_bound {L : Nat → Bool} (hX : InX L) {m : Nat}
    (hm : 1 ≤ m) (black : L m = true) (white : ∀ k, m < k → L k = false)
    (c : KickClock (kicks L)) (sep : ∀ i, c.gap i = 3 → c.gap (i + 1) ≠ 3)
    {i j n : Nat} (ij : i < j) (eq : BlockEq c.gap i j n) :
    8 * n < 10 * j + m + 2 * c.time 0 + 2 := by
  have weighted := repeat_before_edge hX hm black white (time_strict c i j ij)
    (same_samples c i j n eq)
  have lower := span_lower c sep n i
  have upper := time_upper c j
  omega

private theorem kicks_Psi (R : Nat → Bool) : kicks (Psi R) = u R := by
  funext s
  simp only [kicks, Psi_free, Bool.not_not]
  rfl

/-- Clock-free form for the actual white-phase readings of column +1.
Repeats exceeding their later start by unbounded amounts already exclude
a finite compatible left row. No gap length or trap hypothesis enters. -/
theorem psi_not_finite_of_sample_repeats (R : Nat → Bool)
    (h : ∀ K, ∃ s t w, s < t ∧ BlockEq (u R) s t w ∧ t + K ≤ w) :
    ¬ FinSupp (Psi R) := by
  intro fin
  obtain ⟨width, beyond⟩ := fin
  obtain ⟨m, hm, b, z⟩ := last_black (show Psi R 1 = true from Psi_inX R 0) width beyond
  obtain ⟨s, t, w, st, eq, large⟩ := h m
  rw [← kicks_Psi] at eq
  have := repeat_before_edge (Psi_inX R) hm b z st eq
  omega

/-- An asymptotic condition stated without real numbers. Early equal blocks
have arbitrarily large excess 4*n - 5*j over their second starting index. -/
def EarlyRepeats (g : Nat → Nat) : Prop :=
  ∀ K, ∃ i j n, i < j ∧ BlockEq g i j n ∧ 5 * j + K ≤ 4 * n

/-- Overlapping occurrences are allowed. A second copy beginning at most
two thirds of its length into the word, at unbounded lengths, suffices.
In the notation of Bugeaud and Kim, this holds when rep(g) < 5/3. -/
theorem early_of_two_thirds {g : Nat → Nat}
    (h : ∀ N, ∃ i j n, N ≤ n ∧ i < j ∧ BlockEq g i j n ∧ 3 * j ≤ 2 * n) :
    EarlyRepeats g := by
  intro K
  obtain ⟨i, j, n, hn, ij, eq, hj⟩ := h (2 * K)
  exact ⟨i, j, n, ij, eq, by omega⟩

theorem not_finite_of_early {L : Nat → Bool} (hX : InX L)
    (c : KickClock (kicks L)) (sep : ∀ i, c.gap i = 3 → c.gap (i + 1) ≠ 3)
    (early : EarlyRepeats c.gap) : ¬ FinSupp L := by
  intro fin
  obtain ⟨width, beyond⟩ := fin
  obtain ⟨m, hm, b, tail⟩ := last_black (show L 1 = true from hX 0) width beyond
  obtain ⟨i, j, n, ij, eq, large⟩ := early (m + 2 * c.time 0 + 2)
  have := gap_repeat_bound hX hm b tail c sep ij eq
  omega

/-- The test applies directly to the actual white-tick column +1 under
alternating drive, with no restriction on the part of the right half farther out. -/
theorem psi_not_finite_of_early (R : Nat → Bool)
    (c : KickClock (u R)) (sep : ∀ i, c.gap i = 3 → c.gap (i + 1) ≠ 3)
    (early : EarlyRepeats c.gap) : ¬ FinSupp (Psi R) := by
  have result := not_finite_of_early (Psi_inX R)
  rw [kicks_Psi] at result
  exact result c sep early

end Ruliology.CellularAutomata.Rule30GapRepetitions
