module

public import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Five readings determine a three-tick population two sites west

Wherever a Rule 30 column reads 10010 or 11011, the three readings starting at the
same time two sites west have respectively two black cells or one. This uses the
local update and the white-center OR latch. Consecutive aligned triples telescope
to the exact count in `block_weight` for finite episodes.

For the single seed, use the existing phase-zero skeleton for 001. A permanent
001 then excludes late white pairs at column -2, and 011 excludes black pairs.
Either clock excludes late monochrome four-tick windows there. Thus four equal
readings at arbitrarily late ages in this one column would exclude all eventual
center periods of three. Recurrence of that event is open.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30WestTripleWeight
open Rule30Jen Rule30Prize Rule30EtherThree

/-- Rule 30 on the full line. -/
def Valid (F : Nat → Int → Bool) : Prop :=
  ∀ t i, F (t+1) i = rule (F t (i-1)) (F t i) (F t (i+1))

private def back2 (a b c u v : Bool) := rule (rule c b v) (rule b a u) a

private theorem inv {F} (h : Valid F) (t : Nat) (i : Int) :
    F t (i-1) = rule (F (t+1) i) (F t i) (F t (i+1)) := by
  rw [h]
  unfold rule
  cases F t (i-1) <;> cases (F t i || F t (i+1)) <;> rfl

private theorem west {F} (h : Valid F) (t : Nat) (i : Int) :
    F t (i-2) = back2 (F t i) (F (t+1) i) (F (t+2) i) (F t (i+1)) (F (t+1) (i+1)) := by
  rw [show i-2=i-1-1 by omega, inv h t (i-1), show i-1+1=i by omega,
      inv h (t+1) i, inv h t i]
  rfl

/-- The middle bit distinguishes center words 10010 and 11011.
Only the white-center OR latch is used to discard one possible input. -/
private theorem table : ∀ h a b c d : Bool, (h=false → b=true → c=true) →
    (back2 true h false a b).toNat + (back2 h false true b c).toNat +
      (back2 false true h c d).toNat = (if h then 1 else 2) := by decide

/-- Five readings of a column determine the population of three readings two
sites west. This holds wherever these words occur, even on a nonperiodic orbit. -/
theorem five_readings {F} (evol : Valid F) (t : Nat) (i : Int) (h : Bool)
    (a : F t i = true) (b : F (t+1) i = h) (c : F (t+2) i = false)
    (d : F (t+3) i = true) (e : F (t+4) i = h) :
    (F t (i-2)).toNat + (F (t+1) (i-2)).toNat + (F (t+2) (i-2)).toNat =
      (if h then 1 else 2) := by
  have latch (hh : h=false) (rb : F (t+1) (i+1)=true) : F (t+2) (i+1)=true := by
    rw [evol (t+1) (i+1), show i+1-1=i by omega, b, hh, rb]
    rfl
  rw [west evol t i, west evol (t+1) i, west evol (t+2) i]
  rw [a,b,c,d,e]
  exact table h _ _ _ _ latch

def count (f : Nat → Bool) (t : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => count f t n + (f (t+n)).toNat

/-- Exact Western population for any finite chain of the five-letter observations. -/
theorem block_weight {F} (evol : Valid F) (t : Nat) (i : Int) (h : Bool) (n : Nat)
    (word : ∀ k, k<n → F (t+3*k) i=true ∧ F (t+3*k+1) i=h ∧ F (t+3*k+2) i=false ∧
      F (t+3*k+3) i=true ∧ F (t+3*k+4) i=h) :
    count (fun j => F j (i-2)) t (3*n) = n*(if h then 1 else 2) := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    obtain ⟨a,b,c,d,e⟩ := word n (by omega)
    have tri := five_readings evol _ i h a b c d e
    have prev := ih (fun k hk => word k (by omega))
    rw [show 3*(n+1)=3*n+2+1 by omega, count, count, count, prev, Nat.succ_mul n (if h then 1 else 2)]
    simp only [← Nat.add_assoc] at tri ⊢
    omega


private theorem cell_back2 (t : Nat) :
    cell t (-2) = back2 (cell t 0) (cell (t+1) 0) (cell (t+2) 0) (cell t 1) (cell (t+1) 1) :=
  west (F := cell) (fun _ _ => rfl) t 0

private theorem back2_congr {a b c d e A B C D E : Bool}
    (ha : a=A) (hb : b=B) (hc : c=C) (hd : d=D) (he : e=E) :
    back2 a b c d e = back2 A B C D E := by rw [ha,hb,hc,hd,he]

private def clockWord (hi : Bool) := if hi then w011 else w001
private def clock (hi : Bool) (p : Nat) := wordAt3 (clockWord hi) p
private def observed (hi : Bool) (p : Nat) (r : Bool) : Bool :=
  if hi = false ∧ p%3 = 0 then false else r
private def model (hi : Bool) (p : Nat) (a b : Bool) :=
  back2 (clock hi p) (clock hi (p+1)) (clock hi (p+2)) (observed hi p a) (observed hi (p+1) b)

private theorem truth_table : ∀ (hi : Bool) (p : Fin 3) (a b c : Bool),
    ¬ (model hi p.val a b = hi ∧ model hi (p.val+1) b c = hi) := by decide

private theorem model_at {hi : Bool} {T U : Nat}
    (period : ∀ t, T ≤ t → cell t 0 = clock hi (t-T))
    (sk : ∀ t, U ≤ t → hi = false → (t-T)%3=0 → cell t 1=false)
    {t p : Nat} (ht : T ≤ t) (hu : U ≤ t) (phase : (t-T)%3=p%3) :
    cell t (-2) = model hi p (cell t 1) (cell (t+1) 1) := by
  have cc (k : Nat) : cell (t+k) 0 = clock hi (p+k) := by
    rw [period _ (by omega)]
    unfold clock wordAt3
    rw [show (t+k-T)%3=(p+k)%3 by omega]
  have rr (k : Nat) : cell (t+k) 1 = observed hi (p+k) (cell (t+k) 1) := by
    unfold observed
    split
    · rename_i h
      exact sk _ (by omega) h.1 (by omega)
    · rfl
  rw [cell_back2]
  unfold model
  exact back2_congr (cc 0) (cc 1) (cc 2) (rr 0) (rr 1)

private theorem mature (hi : Bool) (T : Nat)
    (period : ∀ t, T ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t-T)) :
    ∃ U, T ≤ U ∧ ∀ t, U ≤ t → hi=false → (t-T)%3=0 → cell t 1=false := by
    cases hi with
    | false =>
      obtain ⟨U,hu,h⟩ := skeleton_001 T period
      exact ⟨U,hu,fun t ht _ => h t ht⟩
    | true => exact ⟨T,by omega,by simp⟩

/-- A 001 tail forbids late consecutive whites at -2. A 011 tail forbids
consecutive blacks there. In the latter case the conclusion starts at onset. -/
theorem avoids_pair (hi : Bool) (T : Nat)
    (period : ∀ t, T ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t-T)) :
    ∃ U, T ≤ U ∧ ∀ t, U ≤ t → ¬ (cell t (-2) = hi ∧ cell (t+1) (-2) = hi) := by
  obtain ⟨U,hu,sk⟩ := mature hi T period
  refine ⟨U,hu,?_⟩
  intro t ht
  let p : Fin 3 := ⟨(t-T)%3,by omega⟩
  have phase : (t-T)%3 = p.val := rfl
  have a := model_at (hi:=hi) period sk (t:=t) (p:=p.val) (by omega) ht (by omega)
  have b := model_at (hi:=hi) period sk (t:=t+1) (p:=p.val+1) (by omega) (by omega) (by omega)
  rw [a,b]
  exact truth_table hi p _ _ _

/-- A fixed-column recurrence condition sufficient to exclude the entire period
three, including both rotation families. The two pairs may occur at different ages. -/
theorem no_period_three_of_both_pairs
    (pairs : ∀ (b : Bool) (U : Nat), ∃ t, U ≤ t ∧ cell t (-2) = b ∧ cell (t+1) (-2) = b) :
    ¬ ∃ T, ∀ t, T ≤ t → center (t+3) = center t := by
  rintro ⟨T,h⟩
  have kill (hi : Bool) (t0 : Nat)
      (word : ∀ t, t0 ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t-t0)) : False := by
    obtain ⟨U,_,avoids⟩ := avoids_pair hi t0 word
    obtain ⟨t,ht,a,b⟩ := pairs hi U
    exact avoids t ht ⟨a,b⟩
  rcases normalize_period_three h with ⟨t0,_,h0⟩ | ⟨t0,_,h1⟩
  · exact kill false t0 h0
  · exact kill true t0 h1


private theorem four_table : ∀ (hi : Bool) (p : Fin 3) (a b c d e v : Bool),
    ¬ (model hi p.val a b = v ∧ model hi (p.val+1) b c = v ∧
       model hi (p.val+2) c d = v ∧ model hi (p.val+3) d e = v) := by decide

/-- Under either normalized clock, a late four-tick window at -2 cannot be monochrome. -/
theorem forbids_four (hi : Bool) (T : Nat)
    (period : ∀ t, T ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t-T)) :
    ∃ U, ∀ t, U ≤ t → ∀ v, ¬ (∀ j : Fin 4, cell (t+j.val) (-2) = v) := by
  obtain ⟨U,hu,sk⟩ := mature hi T period
  refine ⟨U,?_⟩
  intro t ht v flat
  let p : Fin 3 := ⟨(t-T)%3,by omega⟩
  have phase : (t-T)%3 = p.val := rfl
  have atj (j : Fin 4) : model hi (p.val+j.val) (cell (t+j.val) 1) (cell (t+j.val+1) 1) = v :=
    (model_at (hi:=hi) period sk (t:=t+j.val) (p:=p.val+j.val) (by omega) (by omega) (by omega)).symm.trans (flat j)
  exact four_table hi p _ _ _ _ _ v ⟨atj 0,atj 1,atj 2,atj 3⟩

/-- A single four-reading recurrence target for the singleton rules out every
period-three phase and both nonconstant period-three necklaces. -/
theorem no_period_three_of_four_runs
    (runs : ∀ U, ∃ t v, U ≤ t ∧ ∀ j : Fin 4, cell (t+j.val) (-2) = v) :
    ¬ ∃ T, ∀ t, T ≤ t → center (t+3) = center t := by
  rintro ⟨T,h⟩
  have kill (hi : Bool) (t0 : Nat)
      (word : ∀ t, t0 ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t-t0)) : False := by
    obtain ⟨U,avoid⟩ := forbids_four hi t0 word
    obtain ⟨t,v,ht,flat⟩ := runs U
    exact avoid t ht v flat
  rcases normalize_period_three h with ⟨t0,_,h0⟩ | ⟨t0,_,h1⟩
  · exact kill false t0 h0
  · exact kill true t0 h1

/-! ## Additivity of `count`, explicit-onset aligned triple weights, and `±2` sliding-window bounds at column `-2` -/

/-- **Additivity and upper bound of `count` (`count_add_and_le`).** -/
theorem count_add_and_le (f : Nat → Bool) (t m n : Nat) :
    count f t (m + n) = count f t m + count f (t + m) n ∧ count f t n ≤ n := by
  constructor
  · induction n with
    | zero => simp [count]
    | succ n ih =>
      rw [Nat.add_succ, count, count, ih, Nat.add_assoc, Nat.add_assoc]
  · induction n with
    | zero => simp [count]
    | succ n ih =>
      rw [count]
      cases f (t + n) <;> simp <;> omega

/-- **Explicit-onset aligned triple-weight law at column `-2` (`period_three_aligned_block_weight_m2`):**
under normalized clock `hi` from `T`, starting directly at `s0 = T + (if hi then 1 else 2)` (with
no `skeleton_001` wait), `count (col -2) s0 (3 * n) = n * (if hi then 1 else 2)`. -/
theorem period_three_aligned_block_weight_m2 (hi : Bool) (T n : Nat)
    (period : ∀ t, T ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t - T)) :
    count (fun j => cell j (-2)) (T + (if hi then 1 else 2)) (3 * n) =
      n * (if hi then 1 else 2) := by
  have hevol : Valid cell := fun _ _ => rfl
  apply block_weight hevol (T + (if hi then 1 else 2)) 0 hi n
  intro k _
  cases hi with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h0 := period (T + 2 + 3 * k) (by omega)
    have h1 := period (T + 2 + 3 * k + 1) (by omega)
    have h2 := period (T + 2 + 3 * k + 2) (by omega)
    have h3 := period (T + 2 + 3 * k + 3) (by omega)
    have h4 := period (T + 2 + 3 * k + 4) (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte, wordAt3_001] at h0 h1 h2 h3 h4
    exact ⟨by simpa [show (T + 2 + 3 * k - T) % 3 = 2 by omega] using h0,
           by simpa [show (T + 2 + 3 * k + 1 - T) % 3 = 0 by omega] using h1,
           by simpa [show (T + 2 + 3 * k + 2 - T) % 3 = 1 by omega] using h2,
           by simpa [show (T + 2 + 3 * k + 3 - T) % 3 = 2 by omega] using h3,
           by simpa [show (T + 2 + 3 * k + 4 - T) % 3 = 0 by omega] using h4⟩
  | true =>
    simp only [↓reduceIte]
    have h0 := period (T + 1 + 3 * k) (by omega)
    have h1 := period (T + 1 + 3 * k + 1) (by omega)
    have h2 := period (T + 1 + 3 * k + 2) (by omega)
    have h3 := period (T + 1 + 3 * k + 3) (by omega)
    have h4 := period (T + 1 + 3 * k + 4) (by omega)
    simp only [↓reduceIte, wordAt3_011] at h0 h1 h2 h3 h4
    exact ⟨by simpa [show (T + 1 + 3 * k - T) % 3 = 1 by omega] using h0,
           by simpa [show (T + 1 + 3 * k + 1 - T) % 3 = 2 by omega] using h1,
           by simpa [show (T + 1 + 3 * k + 2 - T) % 3 = 0 by omega] using h2,
           by simpa [show (T + 1 + 3 * k + 3 - T) % 3 = 1 by omega] using h3,
           by simpa [show (T + 1 + 3 * k + 4 - T) % 3 = 2 by omega] using h4⟩

/-- **Uniform `±2` sliding-window black-population bounds at column `-2`
(`period_three_sliding_count_bounds_m2`):** for every start `t ≥ T + 2` and every `n : Nat`,
`count (col -2) t (3 * n)` lies within `±2` of `n * (if hi then 1 else 2)`. -/
theorem period_three_sliding_count_bounds_m2 (hi : Bool) (T t n : Nat)
    (period : ∀ s, T ≤ s → cell s 0 = wordAt3 (if hi then w011 else w001) (s - T))
    (ht : T + 2 ≤ t) :
    let w := if hi then 1 else 2
    n * w ≤ count (fun j => cell j (-2)) t (3 * n) + 2 ∧
      count (fun j => cell j (-2)) t (3 * n) ≤ n * w + 2 := by
  dsimp only
  let s0 := T + (if hi then 1 else 2)
  have hs0 : s0 ≤ t := by cases hi <;> simp [s0] <;> omega
  let q := (t - s0) / 3
  let r := (t - s0) % 3
  have htr : t = s0 + 3 * q + r := by dsimp [q, r]; omega
  have hrlt : r < 3 := by dsimp [r]; omega
  have hal (m : Nat) : count (fun j => cell j (-2)) (s0 + 3 * m) 3 = (if hi then 1 else 2) := by
    have h1 := period_three_aligned_block_weight_m2 hi T (m + 1) period
    have h0 := period_three_aligned_block_weight_m2 hi T m period
    change count (fun j => cell j (-2)) s0 (3 * (m + 1)) = _ at h1
    change count (fun j => cell j (-2)) s0 (3 * m) = _ at h0
    have hsp := (count_add_and_le (fun j => cell j (-2)) s0 (3 * m) 3).1
    rw [show 3 * (m + 1) = 3 * m + 3 by omega, hsp, h0, Nat.succ_mul m] at h1
    exact Nat.add_left_cancel h1
  have halN (m k : Nat) : count (fun j => cell j (-2)) (s0 + 3 * m) (3 * k) =
      k * (if hi then 1 else 2) := by
    induction k with
    | zero => simp [count]
    | succ k ih =>
      rw [show 3 * (k + 1) = 3 * k + 3 by omega,
          (count_add_and_le (fun j => cell j (-2)) (s0 + 3 * m) (3 * k) 3).1, ih,
          show s0 + 3 * m + 3 * k = s0 + 3 * (m + k) by omega, hal (m + k), Nat.succ_mul]
  cases n with
  | zero => simp [count]
  | succ n =>
    -- Decompose `s0 + 3 * q` .. `s0 + 3 * (q + n + 2)` of length `3 * (n + 2) = r + 3 * (n + 1) + (3 - r)`
    have htot := halN q (n + 2)
    have hsp1 := (count_add_and_le (fun j => cell j (-2)) (s0 + 3 * q) r (3 * (n + 1) + (3 - r))).1
    have hsp2 := (count_add_and_le (fun j => cell j (-2)) (s0 + 3 * q + r) (3 * (n + 1)) (3 - r)).1
    have hlen : 3 * (n + 2) = r + (3 * (n + 1) + (3 - r)) := by omega
    rw [hlen, hsp1, hsp2, ← htr] at htot
    have hb1 := (count_add_and_le (fun j => cell j (-2)) (s0 + 3 * q) 0 r).2
    have hb2 := (count_add_and_le (fun j => cell j (-2)) (t + 3 * (n + 1)) 0 (3 - r)).2
    -- Also compare with `3 * n` inside `t`: `r + (3 - r) = 3` and the single block `hal q` has sum `w`!
    have hfirst := hal q
    have hfirst_sp := (count_add_and_le (fun j => cell j (-2)) (s0 + 3 * q) r (3 - r)).1
    rw [show r + (3 - r) = 3 by omega] at hfirst_sp
    have hcr_le_w : count (fun j => cell j (-2)) (s0 + 3 * q) r ≤ (if hi then 1 else 2) := by omega
    have htail := hal (q + n + 1)
    have htail_sp := (count_add_and_le (fun j => cell j (-2)) (s0 + 3 * (q + n + 1)) r (3 - r)).1
    rw [show r + (3 - r) = 3 by omega,
        show s0 + 3 * (q + n + 1) + r = t + 3 * (n + 1) by omega] at htail_sp
    have htail_le_w : count (fun j => cell j (-2)) (t + 3 * (n + 1)) (3 - r) ≤ (if hi then 1 else 2) := by omega
    cases hi <;> simp only [↓reduceIte, Bool.false_eq_true] at htot hcr_le_w htail_le_w ⊢ <;> omega

/-- **Density-escape exclusion of period 3 at column `-2` (`no_period_three_of_density_escape_m2`):**
if for each `w ∈ {1, 2}` and every `U`, some late `3 * n`-window at column `-2` deviates from
`n * w` by more than `2`, then center is not eventually period-3. -/
theorem no_period_three_of_density_escape_m2
    (esc : ∀ (hi : Bool) (U : Nat), ∃ t n, U ≤ t ∧
      (count (fun j => cell j (-2)) t (3 * n) + 2 < n * (if hi then 1 else 2) ∨
       n * (if hi then 1 else 2) + 2 < count (fun j => cell j (-2)) t (3 * n))) :
    ¬ ∃ T, ∀ t, T ≤ t → center (t + 3) = center t := by
  rintro ⟨T, h⟩
  rcases normalize_period_three h with ⟨t0, _, h0⟩ | ⟨t0, _, h1⟩
  · obtain ⟨t, n, ht, hbad⟩ := esc false (t0 + 2)
    have hb := period_three_sliding_count_bounds_m2 false t0 t n h0 ht
    dsimp only at hb
    omega
  · obtain ⟨t, n, ht, hbad⟩ := esc true (t0 + 2)
    have hb := period_three_sliding_count_bounds_m2 true t0 t n h1 ht
    dsimp only at hb
    omega

/-- **Phase-wise aligned-triple deviation exclusion of period 3 (`no_period_three_of_phase_triple_deviations_m2`):**
if at every phase `r : Fin 3` and each target weight `w ∈ {1, 2}`, column `-2` has arbitrarily late
triples `3 * k + r.val` of weight `≠ w`, then center is not eventually period-3. -/
theorem no_period_three_of_phase_triple_deviations_m2
    (dev : ∀ (r : Fin 3) (hi : Bool) (K : Nat), ∃ k, K ≤ k ∧
      count (fun j => cell j (-2)) (3 * k + r.val) 3 ≠ (if hi then 1 else 2)) :
    ¬ ∃ T, ∀ t, T ≤ t → center (t + 3) = center t := by
  rintro ⟨T, h⟩
  have kill (hi : Bool) (t0 : Nat)
      (period : ∀ t, t0 ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t - t0)) : False := by
    let s0 := t0 + (if hi then 1 else 2)
    let r : Fin 3 := ⟨s0 % 3, by omega⟩
    obtain ⟨k, hk, hne⟩ := dev r hi (s0 / 3 + 1)
    have hm : ∃ m, 3 * k + r.val = s0 + 3 * m := ⟨k - s0 / 3, by dsimp [r]; omega⟩
    obtain ⟨m, heq⟩ := hm
    have h1 := period_three_aligned_block_weight_m2 hi t0 (m + 1) period
    have h0 := period_three_aligned_block_weight_m2 hi t0 m period
    change count (fun j => cell j (-2)) s0 (3 * (m + 1)) = _ at h1
    change count (fun j => cell j (-2)) s0 (3 * m) = _ at h0
    have hsp := (count_add_and_le (fun j => cell j (-2)) s0 (3 * m) 3).1
    rw [show 3 * (m + 1) = 3 * m + 3 by omega, hsp, h0, Nat.succ_mul m] at h1
    rw [heq] at hne
    exact hne (Nat.add_left_cancel h1)
  rcases normalize_period_three h with ⟨t0, _, h0⟩ | ⟨t0, _, h1⟩
  · exact kill false t0 h0
  · exact kill true t0 h1

end Ruliology.CellularAutomata.Rule30WestTripleWeight
