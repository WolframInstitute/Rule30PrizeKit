module

public import Ruliology.CellularAutomata.Rule30RecurrentStrip
public import Ruliology.CellularAutomata.Rule30EveryKInverse

/-! Uniform reset depth on periodic finite bands, from unbounded closed runs on
each pointed recurrent strip. All widths count wheels starting at wheel zero. -/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ResetCompactness
open Ruliology.CellularAutomata
open Rule30AgedLeftDiagonals Rule30UniversalLeftSide Rule30EveryKStatement
open Ruliology.CellularAutomata.Rule30RecurrentStrip (Clock Reset)

/-- The strip and clock hypotheses are those of the three-phase theorem.
Here the prescribed phase itself must have arbitrarily deep closed runs. -/
def LInfinity : Prop := ∀ (d : Nat → Nat → Bool), Recurrence d → d 0 0 = true →
  (∀ m, ∃ p, 0 < p ∧ Clock d m p) →
  ∀ s lo, ∃ j n, lo ≤ j ∧ Reset (fun i => d i s) j n

private def Often (P : Nat → Prop) := ∀ bound, ∃ i, bound ≤ i ∧ P i

private theorem split_often {P : Nat → Prop} (h : Often P) (f : Nat → Bool) :
    ∃ b, Often (fun i => P i ∧ f i = b) := by
  classical
  by_cases ht : Often (fun i => P i ∧ f i = true)
  · exact ⟨true, ht⟩
  · simp only [Often, Classical.not_forall, not_exists, not_and] at ht
    obtain ⟨u, hu⟩ := ht
    refine ⟨false, fun bound => ?_⟩
    obtain ⟨i, hi, pi⟩ := h (max bound u)
    exact ⟨i, by omega, pi, Bool.eq_false_iff.mpr (hu i (by omega) pi)⟩

private structure Pool where
  pred : Nat → Prop
  often : Often pred

private noncomputable def pools (bits : Nat → Nat → Bool) : Nat → Pool
  | 0 => ⟨fun _ => True, fun n => ⟨n, Nat.le_refl _, trivial⟩⟩
  | n+1 =>
    let p := pools bits n
    let pick := split_often p.often (fun i => bits i n)
    ⟨_, pick.choose_spec⟩

private theorem limit_prefix (bits : Nat → Nat → Bool) :
    ∃ x : Nat → Bool, ∀ n, Often (fun i => ∀ j, j < n → bits i j = x j) := by
  let x := fun n => (split_often (pools bits n).often (fun i => bits i n)).choose
  have matchBits (n i) (h : (pools bits n).pred i) : ∀ j, j < n → bits i j = x j := by
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      change (pools bits n).pred i ∧ bits i n = x n at h
      intro j hj
      by_cases eq : j = n
      · exact eq ▸ h.2
      · exact ih h.1 j (by omega)
  exact ⟨x, fun n bound => by
    obtain ⟨i,hi,h⟩ := (pools bits n).often bound
    exact ⟨i,hi,matchBits n i h⟩⟩

private def orbit (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => x
  | t+1 => fun | 0 => orbit x t 0
               | 1 => orbit x t 0 || orbit x t 1
               | j+2 => xor (orbit x t j) (orbit x t (j+1) || orbit x t (j+2))

private theorem orbit_prefix {x v w n} (hn : n ≤ w)
    (bits : ∀ j, j < n → v.testBit j = x j) (t : Nat) :
    ∀ j, j < n → (bandAt w v t).testBit j = orbit x t j := by
  induction t with
  | zero => exact bits
  | succ t ih =>
    intro j hj
    cases j with
    | zero => exact (stepK_bit_zero (by omega) _).trans (ih 0 hj)
    | succ j =>
      cases j with
      | zero => rw [bandAt, rowAt, stepK_bit_one (by omega), ih 0 (by omega), ih 1 hj]; rfl
      | succ j => rw [bandAt, rowAt, stepK_bit_step (by omega), ih j (by omega), ih (j+1) (by omega), ih (j+2) hj]; rfl

/-- At each desired cut depth there is one window containing a complete
factor for every periodic odd band of at least that width. -/
theorem uniform_factor (deep : LInfinity) (lo : Nat) :
    ∃ b, ∀ w v p, b ≤ w → OddBand w v → 0 < p → bandAt w v p = v →
      ∃ j m, lo ≤ j ∧ j + 3*m + 4 ≤ b ∧ resetAt v j m = true := by
  classical
  apply Classical.byContradiction
  intro fail
  simp only [not_exists, Classical.not_forall] at fail
  let w := fun i => (fail i).choose
  let vs := fun i => (fail i).choose_spec
  let v := fun i => (vs i).choose
  let ps := fun i => (vs i).choose_spec
  let p := fun i => (ps i).choose
  let data := fun i => (ps i).choose_spec
  have wide (i) : i ≤ w i := (data i).1
  have odd (i) : OddBand (w i) (v i) := (data i).2.1
  have pos (i) : 0 < p i := (data i).2.2.1
  have cyc (i) : bandAt (w i) (v i) (p i) = v i := (data i).2.2.2.1
  have bad := fun i => (data i).2.2.2.2
  obtain ⟨x, approx⟩ := limit_prefix (fun i j => (v i).testBit j)
  let d := fun j t => orbit x t j
  have recurrence : Recurrence d := ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  have edge : d 0 0 = true := by
    obtain ⟨i, _, hx⟩ := approx 1 1
    exact (hx 0 (by decide)).symm.trans (odd i).2
  have clocks (m) : ∃ q, 0 < q ∧ Clock d m q := by
    obtain ⟨i,hi,hx⟩ := approx (m+1) (m+1)
    have agree := orbit_prefix (Nat.le_trans hi (wide i)) hx
    refine ⟨p i, pos i, fun j hj t _ => ?_⟩
    change orbit x (t+p i) j = orbit x t j
    rw [← agree _ j (by omega), ← agree _ j (by omega), bandAt, rowAt_add_period (cyc i)]
  obtain ⟨a,n,ha,hn,hleft,hones,hright⟩ := deep d recurrence edge clocks 0 (lo+1)
  let m := n / 3
  have len : n = 3*m + 1 := by dsimp [m]; omega
  let j := a-1
  have start : j+1 = a := by dsimp [j]; omega
  let b := j+3*m+4
  obtain ⟨i,hi,hx⟩ := approx b b
  have bit (l) (hl : l < b) : (v i).testBit l = d l 0 := hx l hl
  have reset : resetAt (v i) j m = true := by
    simp only [resetAt, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range]
    refine ⟨⟨(bit _ (by dsimp [b]; omega)).trans (start.symm ▸ hleft), ?_⟩, ?_⟩
    · rw [bit _ (by dsimp [b]; omega), show j+3*m+3 = a+1+n by omega]; exact hright
    · intro k hk
      rw [bit _ (by dsimp [b]; omega), show j+2+k = a+1+k by omega]; exact hones k (by omega)
  exact bad i j m ⟨by omega,hi,reset⟩


/-- Searching in descending depth returns a cut at least as deep as any
given witness. The predicate is fixed even as the search list shrinks. -/
private theorem descending_find (test : Nat → Bool) {j : Nat} (ok : test j = true)
    (n : Nat) (inside : j < n) :
    ∃ cut, (List.range n).reverse.find? test = some cut ∧ j ≤ cut := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.find?_cons]
    split <;> rename_i h
    · exact ⟨n, rfl, by omega⟩
    · exact ih (by apply Nat.lt_of_le_of_ne (by omega); intro eq; subst j; simp [h] at ok)

private theorem find_cut {v j m a : Nat} (fits : j+3*m+4 ≤ a) (reset : resetAt v j m = true) :
    ∃ cut, firstReset v a = some cut ∧ j ≤ cut := by
  apply descending_find _ _ a (by omega)
  apply List.any_eq_true.mpr
  exact ⟨m, List.mem_range.mpr (by omega), by simp [fits, reset]⟩

private theorem advance (w v t q : Nat) :
    bandAt w (bandAt w v t) q = bandAt w v (q+t) := by
  induction q with
  | zero => simp [bandAt, rowAt]
  | succ q ih => rw [Nat.succ_add]; exact congrArg (bandStep w) ih

private theorem phase_odd {w v} (odd : OddBand w v) (hw : 0 < w) (t : Nat) :
    OddBand w (bandAt w v t) := by
  induction t with
  | zero => exact odd
  | succ t ih => exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), (stepK_bit_zero hw _).trans ih.2⟩

/-- Any free entrance and any starting layer are allowed. A window for k+1
layers leaves at least the entire k-layer window after the first cut. -/
private theorem uniform_schedule (deep : LInfinity) (k : Nat) :
    ∃ u, ∀ w v p fuel d a, u ≤ a → a ≤ w → k ≤ fuel → 0 < w →
      OddBand w v → 0 < p → bandAt w v p = v → k ≤ schedule w v p fuel d a := by
  induction k with
  | zero => exact ⟨0, by intros; exact Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨u, smaller⟩ := ih
    obtain ⟨b, window⟩ := uniform_factor deep u
    refine ⟨b, ?_⟩
    intro w v p fuel d a ba aw kf hw odd hp cyc
    cases fuel with
    | zero => omega
    | succ fuel =>
      let t := (p - d%p)%p
      have returns : bandAt w (bandAt w v t) p = bandAt w v t := by
        rw [advance, Nat.add_comm p t]; exact rowAt_add_period cyc t
      obtain ⟨j,m,uj,fit,reset⟩ := window w _ p (by omega) (phase_odd odd hw t) hp returns
      obtain ⟨cut,hcut,jcut⟩ := find_cut (a := a) (by omega : j+3*m+4 ≤ a) reset
      obtain ⟨n, bound, _⟩ := Rule30EveryKCascade.firstReset_spec hcut
      have next := smaller w v p fuel (d+1) cut (by omega) (by omega) (by omega) hw odd hp cyc
      rw [schedule, hcut]
      change k+1 ≤ 1 + schedule w v p fuel (d+1) cut
      omega

private theorem walk_sound (w v fuel t q : Nat)
    (h : returnPeriod.walk w v fuel (bandAt w v t) t = some q) :
    0 < q ∧ bandAt w v q = v := by
  induction fuel generalizing t with
  | zero => simp [returnPeriod.walk] at h
  | succ fuel ih =>
    rw [returnPeriod.walk] at h
    split at h <;> rename_i eq
    · cases h; exact ⟨by omega, eq⟩
    · exact ih (t+1) h

private theorem fold_floor (step : Nat → Nat → Nat) (xs : List Nat) {k : Nat}
    (preserves : ∀ i ∈ xs, ∀ acc, k ≤ acc → k ≤ step acc i) (acc : Nat) (h : k ≤ acc) :
    k ≤ xs.foldl step acc := by
  induction xs generalizing acc with
  | nil => exact h
  | cons i xs ih =>
    exact ih (fun j hj => preserves j (by simp [hj])) _ (preserves i (by simp) acc h)

/-- Unbounded resets in every phase of every pointed recurrent strip suffice
for the kit's worst-phase, worst-cycle capacity to reach every depth. -/
theorem cap_of_unbounded_resets (deep : LInfinity) : CAP := by
  intro k
  obtain ⟨u, bound⟩ := uniform_schedule deep k
  let n := max k u
  refine ⟨n+1, by omega, ?_⟩
  unfold K1
  apply fold_floor
  · intro i hi acc hacc
    have small := List.mem_range.mp hi
    dsimp only
    split <;> rename_i h
    · exact hacc
    · rename_i p
      obtain ⟨hp,cyc⟩ := walk_sound (n+1) (2*i+1) (2^n) 0 p h
      apply Nat.le_min.mpr
      refine ⟨hacc, bound (n+1) (2*i+1) p (n+1) 0 (n+1) (by dsimp [n]; omega)
        (by omega) (by dsimp [n]; omega) (by omega) ?_ hp cyc⟩
      constructor
      · rw [Nat.pow_succ]; omega
      · simp [Nat.testBit_zero]
  · dsimp [n]; omega

/-- With the kit's conditional every-k theorem, the same hypothesis gives the inverse-tick target for every k. -/
theorem every_k_of_unbounded_resets (deep : LInfinity) : ∀ k, ∃ age, TargetAt k age :=
  fun k => ⟨_, Rule30EveryKInverse.conditional_every_k (cap_of_unbounded_resets deep) k⟩

end Ruliology.CellularAutomata.Rule30ResetCompactness
