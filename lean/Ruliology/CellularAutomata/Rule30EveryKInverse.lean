module

public import Ruliology.CellularAutomata.Rule30EveryKCascade

/-!
# The conditional inverse-tick theorem at a uniform age

Attach the minimum over edge cycles to the physical cascade and to
finite rows at a fixed white wall. All widths and tick counts are natural numbers.
-/

set_option Elab.async false

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EveryKInverse

open Rule30EveryKStatement Rule30EveryKCascade Rule30ZeroBoundary
open Rule30ZeroBoundary.IntegerForm Rule30UniversalLeftSide

private theorem top_log {Y : Nat} (h : Y ≠ 0) : Top Y Y.log2 :=
  ⟨Nat.testBit_log2 h, fun i hi => Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) hi))⟩

private theorem log_of_top {Y i : Nat} (h : Top Y i) : Y.log2 = i := by
  have nz : Y ≠ 0 := by intro e; simpa [e] using h.1
  have t := top_log nz
  rcases Nat.lt_trichotomy Y.log2 i with hl | he | hg
  · exact absurd h.1 (by rw [t.2 i hl]; decide)
  · exact he
  · exact absurd t.1 (by rw [h.2 _ hg]; decide)

private theorem forward_top {Y m : Nat} (h : Top Y m) : Top (F Y) (m+1) := by
  refine ⟨testBit_F_succ_of_top h.1 h.2, fun i hi => ?_⟩
  obtain ⟨j,rfl⟩ : ∃ j, i = j+1 := ⟨i-1, by omega⟩
  rw [testBit_F_succ, h.2 (j+2) (by omega), h.2 (j+1) (by omega), h.2 j (by omega)]
  rfl

private theorem orbit_top {Y : Nat} (h : Y ≠ 0) (t : Nat) :
    Top (iter F t Y) (Y.log2+t) := by
  induction t with
  | zero => exact top_log h
  | succ t ih => exact forward_top ih

private theorem band_succ (w Y : Nat) :
    topBand (w+1) Y = if w ≤ Y.log2 ∧ Y.testBit (Y.log2-w) = true
      then topBand w Y + 2^w else topBand w Y := by
  simp [topBand, List.range_succ, List.foldl_append]

theorem band_lt (w Y : Nat) : topBand w Y < 2^w := by
  induction w with
  | zero => simp [topBand]
  | succ w ih => rw [band_succ, Nat.pow_succ]; split <;> omega

theorem band_bit (w Y i : Nat) :
    (topBand w Y).testBit i = (decide (i < w ∧ i ≤ Y.log2) && Y.testBit (Y.log2-i)) := by
  induction w with
  | zero => simp [topBand]
  | succ w ih =>
    rw [band_succ]
    split <;> rename_i h
    · rw [← Nat.or_two_pow_eq_add_of_lt (band_lt w Y), Nat.testBit_or, Nat.testBit_two_pow, ih]
      by_cases eq : i = w
      · subst i; simp [h]
      · simp [Ne.symm eq, show (i < w+1) = (i < w) by apply propext; omega]
    · by_cases eq : i = w
      · subst i; simp [ih]; grind
      · simpa [show (i < w+1) = (i < w) by apply propext; omega] using ih

private theorem band_evolves {Y w : Nat} (nz : Y ≠ 0) (full : w ≤ Y.log2+1) :
    topBand w (F Y) = bandStep w (topBand w Y) := by
  let m := Y.log2
  have top := top_log nz
  have log := log_of_top (forward_top top)
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < w
  · have fit : i ≤ m := by omega
    rw [band_bit, log]
    simp only [inside, show i ≤ Y.log2+1 by omega, and_self, decide_true, Bool.true_and]
    cases i with
    | zero =>
      rw [stepK_bit_zero (by omega), band_bit]
      simp [inside, top.1, (forward_top top).1]
    | succ i =>
      cases i with
      | zero =>
        rw [stepK_bit_one (by omega), band_bit, band_bit]
        have hm : 1 ≤ m := by omega
        let z := m-1
        have hz : m = z+1 := by dsimp [z]; omega
        change (F Y).testBit (m+1-1) = _
        rw [show m+1-1 = z+1 by omega, testBit_F_succ,
          top.2 (z+2) (by omega), show z+1 = Y.log2 by omega]
        simp [inside, show 0 < w by omega, show 1 ≤ Y.log2 by omega, top.1]
      | succ i =>
        rw [stepK_bit_step inside, band_bit, band_bit, band_bit]
        let z := m-(i+2)
        have idx : m+1-(i+2) = z+1 := by dsimp [z]; omega
        change (F Y).testBit (m+1-(i+2)) = _
        rw [idx, testBit_F_succ]
        simp [inside, show i < w by omega, show i+1 < w by omega, show i ≤ Y.log2 by omega,
          show i+1 ≤ Y.log2 by omega, show i+2 ≤ Y.log2 by omega,
          show z+2 = Y.log2-i by dsimp [z]; omega,
          show z+1 = Y.log2-(i+1) by dsimp [z]; omega, z, m]
  · have h1 := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (band_lt w (F Y))
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : w ≤ i)))
    have h2 : bandStep w (topBand w Y) < 2^w := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [h1, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega : w ≤ i)))]


private theorem collision (N : Nat) (a : Nat → Nat) (h : ∀ t, a t < N) :
    ∃ i j, i < j ∧ j ≤ N ∧ a i = a j := by
  apply Classical.byContradiction
  intro hn
  have nd := Rule30Jen.nodup_map_of_inj a (List.nodup_range (n := N+1)) (by
    intro i hi j hj e
    simp only [List.mem_range] at hi hj
    rcases Nat.lt_trichotomy i j with lt | eq | gt
    · exact (hn ⟨i,j,lt,by omega,e⟩).elim
    · exact eq
    · exact (hn ⟨j,i,gt,by omega,e.symm⟩).elim)
  have size := Rule30Jen.length_le_of_subset (l₂ := List.range N) nd (by
    intro x hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (h t))
  simp at size
  omega

private theorem orbit_add (w v i n : Nat) :
    bandAt w v (i+n) = bandAt w (bandAt w v i) n := by
  induction n with
  | zero => rfl
  | succ n ih => change bandStep w (bandAt w v (i+n)) = bandStep w (bandAt w (bandAt w v i) n); rw [ih]

private theorem push_eq {w v i j : Nat} (eq : bandAt w v i = bandAt w v j) (n : Nat) :
    bandAt w v (i+n) = bandAt w v (j+n) := by rw [orbit_add, orbit_add w v j, eq]

private theorem band_at_odd {n v : Nat} (odd : OddBand (n+1) v) (t : Nat) :
    OddBand (n+1) (bandAt (n+1) v t) := by
  induction t with
  | zero => exact odd
  | succ t ih => exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), (stepK_bit_zero (by omega) _).trans ih.2⟩

/-- A periodic odd word returns within the exact fuel used by `returnPeriod`'s search.
Dividing an odd word by two codes the 2^n words at width n+1 injectively. -/
private theorem short_return {n v q : Nat} (odd : OddBand (n+1) v) (hq : 0 < q)
    (cycle : bandAt (n+1) v q = v) :
    ∃ p, 0 < p ∧ p ≤ 2^n ∧ bandAt (n+1) v p = v := by
  let a := bandAt (n+1) v
  obtain ⟨i,j,lt,bound,eq⟩ := collision (2^n) (fun t => a t / 2) (by
    intro t
    have h := (band_at_odd odd t).1
    rw [Nat.pow_succ] at h
    dsimp [a]; omega)
  have parity (t) : a t % 2 = 1 := by simpa [a, Nat.testBit_zero] using (band_at_odd odd t).2
  have same : a i = a j := by have := parity i; have := parity j; omega
  let b := (i+1)*q
  have le : i ≤ b := Nat.le_trans (by omega : i ≤ i+1) (Nat.le_mul_of_pos_right _ hq)
  have translated := push_eq same (b-i)
  have ix : i+(b-i) = 0+(i+1)*q := by dsimp [b]; omega
  have jx : j+(b-i) = (j-i)+(i+1)*q := by dsimp [b] at *; omega
  rw [ix, jx] at translated
  unfold bandAt at translated
  rw [rowAt_add_mul cycle, rowAt_add_mul cycle] at translated
  exact ⟨j-i,by omega,by omega,translated.symm⟩

private theorem walk_finds (w v fuel elapsed : Nat)
    (h : ∃ p, elapsed < p ∧ p ≤ elapsed+fuel ∧ bandAt w v p = v) :
    ∃ q, returnPeriod.walk w v fuel (bandAt w v elapsed) elapsed = some q ∧
      0 < q ∧ bandAt w v q = v := by
  induction fuel generalizing elapsed with
  | zero => obtain ⟨_,_,_,_⟩ := h; omega
  | succ fuel ih =>
    rw [returnPeriod.walk]
    split <;> rename_i eq
    · exact ⟨elapsed+1,rfl,by omega,eq⟩
    · apply ih (elapsed+1)
      obtain ⟨p,lo,hi,hp⟩ := h
      have ne : p ≠ elapsed+1 := by rintro rfl; exact eq hp
      exact ⟨p,by omega,by omega,hp⟩


private theorem fold_bound (step : Nat → Nat → Nat) (lower : ∀ b i, step b i ≤ b)
    (xs : List Nat) (b : Nat) : xs.foldl step b ≤ b := by
  induction xs generalizing b with
  | nil => exact Nat.le_refl _
  | cons a xs ih => exact Nat.le_trans (ih _) (lower b a)

private theorem fold_hit (step : Nat → Nat → Nat) (lower : ∀ b i, step b i ≤ b)
    {i limit : Nat} (hit : ∀ a, step a i ≤ limit) (xs : List Nat) (b : Nat) (mem : i ∈ xs) :
    xs.foldl step b ≤ limit := by
  induction xs generalizing b with
  | nil => simp at mem
  | cons a xs ih =>
    rcases List.mem_cons.mp mem with rfl | hm
    · exact Nat.le_trans (fold_bound step lower xs _) (hit b)
    · exact ih _ hm

private def entry (w b i : Nat) := match returnPeriod w (2*i+1) with
  | none => b
  | some p => min b (phaseCapacity w (2*i+1) p)

private theorem entry_le (w b i : Nat) : entry w b i ≤ b := by
  unfold entry; split
  · exact Nat.le_refl _
  · exact Nat.min_le_left ..

theorem capacity_on_cycle {w v : Nat} (hw : 0 < w) (odd : OddBand w v)
    (cycle : ∃ q, 0 < q ∧ bandAt w v q = v) :
    ∃ q, 0 < q ∧ bandAt w v q = v ∧ K1 w ≤ phaseCapacity w v q := by
  obtain ⟨n,rfl⟩ : ∃ n, w = n+1 := ⟨w-1,by omega⟩
  obtain ⟨q,hq,period⟩ := cycle
  obtain ⟨p,hp,bound,ret⟩ := short_return odd hq period
  obtain ⟨q',got,pos,period'⟩ := walk_finds (n+1) v (2^n) 0 ⟨p,hp,by omega,ret⟩
  have found : returnPeriod (n+1) v = some q' := got
  have lo := odd.1
  rw [Nat.pow_succ] at lo
  have parity : v%2 = 1 := by simpa [Nat.testBit_zero] using odd.2
  have eq : 2*(v/2)+1 = v := by omega
  refine ⟨q',pos,period',fold_hit (entry (n+1)) (entry_le _) (i := v/2) ?_ _ _ ?_⟩
  · intro a; simp only [entry,eq,found]; exact Nat.min_le_right ..
  · apply List.mem_range.mpr; omega

/-- A full physical band evolves autonomously from age w-1. Finite-state
pigeonhole gives the seed-independent age in the statement. -/
theorem uniform_settling {w : Nat} (hw : 0 < w) : Settled w (settlingBound w) := by
  intro Y t nz aged
  let s := w-1
  let a (i : Nat) := topBand w (iter F (s+i) Y)
  have log (i : Nat) := log_of_top (orbit_top nz i)
  have positive (i : Nat) : iter F i Y ≠ 0 := by
    intro z; simpa [z] using (orbit_top nz i).1
  have step (i : Nat) : a (i+1) = bandStep w (a i) := by
    dsimp only [a]
    rw [← Nat.add_assoc, iter]
    exact band_evolves (w := w) (positive (s+i)) (by rw [log]; dsimp [s]; omega)
  have advanceOrbit (i n : Nat) : bandAt w (a i) n = a (i+n) := by
    induction n with
    | zero => rfl
    | succ n ih => exact (congrArg (bandStep w) ih).trans (step (i+n)).symm
  obtain ⟨i,j,lt,bound,eq⟩ := collision (2^w) a fun _ => band_lt _ _
  have st : s+2^w ≤ t := aged
  let l := t-s
  have li : i ≤ l := by dsimp [l]; omega
  have cyc := congrArg (fun x => bandAt w x (l-i)) eq
  change bandAt w (a i) (l-i) = bandAt w (a j) (l-i) at cyc
  rw [advanceOrbit, advanceOrbit, show i+(l-i) = l by omega,
    show j+(l-i) = l+(j-i) by omega] at cyc
  have tl : s+l = t := by dsimp [l]; omega
  have per : bandAt w (a l) (j-i) = a l := (advanceOrbit l _).trans cyc.symm
  dsimp only [a] at per
  rw [tl] at per
  refine ⟨by rw [log]; dsimp [s] at st; omega, ⟨band_lt _ _, ?_⟩, j-i, by omega, per⟩
  rw [band_bit]; simp [hw, Nat.testBit_log2 (positive t)]


private theorem matches_band {P : Row} {t Y w : Nat} (nz : Y ≠ 0) (full : w ≤ Y.log2+1)
    (hpre : ∀ x, 1 ≤ x → zrow P t x = rowOfNat Y x) :
    Matches (zrow P t) (Y.log2+1) (topBand w Y) w := by
  constructor
  · simpa only [hpre _ (by omega : 1 ≤ Y.log2+1), rowOfNat] using (top_log nz).1
  · intro x hx
    obtain ⟨i,rfl⟩ : ∃ i, x = i+1 := ⟨x-1,by omega⟩
    rw [hpre _ (by omega)]
    change Y.testBit i = reference (Y.log2+1) (topBand w Y) (i+1)
    by_cases hi : i ≤ Y.log2
    · have idx : Y.log2+1-(i+1) = Y.log2-i := by omega
      simp [reference,hi,band_bit,idx,show Y.log2-i < w by omega,
        show Y.log2-(Y.log2-i) = i by omega]
    · rw [(top_log nz).2 i (by omega)]
      simp [reference,hi]

private theorem integer_edge {k w age Y t : Nat} {P : Row} (hw : 0 < w) (cap : k ≤ K1 w)
    (settled : Settled w age) (nz : Y ≠ 0) (aged : age ≤ t)
    (pre : ∀ x, 1 ≤ x → zrow P k x = rowOfNat (iter F t Y) x) :
    0 < Y.log2+t+1-k ∧ P (Y.log2+t+1-k) = true ∧ ∀ x, Y.log2+t+1-k < x → P x = false := by
  let Z := iter F t Y
  have top := orbit_top nz t
  have zn : Z ≠ 0 := by intro h; have z : Z.testBit (Y.log2+t) = true := top.1; simp [h] at z
  obtain ⟨full,odd,cycle⟩ := settled Y t nz aged
  obtain ⟨q,pos,ret,bound⟩ := capacity_on_cycle hw odd cycle
  have ma := matches_band zn full pre
  have ed := scheduled_edge pos ret w 0 w k (Z.log2+1) P (Nat.le_refl _) full
    (by simpa [earlier, rowAt] using ma) (Nat.le_trans cap bound)
  have log : Z.log2 = Y.log2+t := log_of_top top
  rw [log] at ed
  have posEdge : 1 ≤ Y.log2+t+1-k := by
    apply Classical.byContradiction
    intro h
    have z : Y.log2+t+1-k = 0 := by omega
    have bad := ed.1
    rw [z,zrow_wall] at bad
    contradiction
  exact ⟨posEdge,(zrow_zero_of_pos P posEdge).symm.trans ed.1, fun x hx =>
    (zrow_zero_of_pos P (by omega : 1 ≤ x)).symm.trans (ed.2 x hx)⟩

private theorem physical_clause {k w age : Nat} (hw : 0 < w) (cap : k ≤ K1 w)
    (settled : Settled w age) : PhysicalEdge k age := by
  intro L m t hm edge finite aged P pre
  let Y := natOfRow L m
  have top : Top Y (m-1) := by
    constructor
    · simpa [Y,testBit_natOfRow,show m-1 < m by omega,show m-1+1=m by omega] using edge
    · intro i hi; simp [Y,testBit_natOfRow,show ¬ i<m by omega]
  have nz : Y ≠ 0 := by intro z; simpa [z] using top.1
  have log := log_of_top top
  have rep := rowOfNat_natOfRow finite
  have ed := integer_edge hw cap settled nz aged (P := P) (fun x hx =>
    (pre x hx).trans ((zrow_congr (fun j hj => (rep j hj).symm) t x).trans (zrow_rowOfNat Y t x)))
  simpa only [log,show m-1+t+1 = m+t by omega] using ed.2

private theorem finite_clause {k w age : Nat} (hw : 0 < w) (cap : k ≤ K1 w)
    (settled : Settled w age) : FinitePredecessor k age := by
  intro Y t nz aged L pre
  obtain ⟨positive,edge,tail⟩ := integer_edge hw cap settled nz aged pre
  let e := Y.log2+t+1-k
  let A := natOfRow L e
  have rep : ∀ x, 1 ≤ x → rowOfNat A x = L x := rowOfNat_natOfRow tail
  have image : iter F k A = iter F t Y := by
    apply Nat.eq_of_testBit_eq
    intro i
    exact (zrow_rowOfNat A k (i+1)).symm.trans ((zrow_congr rep k _).trans (pre _ (by omega)))
  refine ⟨A,rep,image,?_,?_⟩
  · have ha := rep e positive
    obtain ⟨i,hi⟩ : ∃ i, e = i+1 := ⟨e-1,by omega⟩
    rw [hi] at ha
    change A.testBit i = L (i+1) at ha
    have eq : Y.log2+t-k = i := by dsimp [e] at hi; omega
    rw [eq, ha, ← hi]; exact edge
  · intro i hi
    have ht : e < i+1 := by dsimp [e]; omega
    exact (rep (i+1) (by omega)).trans (tail _ ht)

/-- Build a physical history with prescribed cell-1 bits in forward order,
allowing arbitrary support until the physical edge theorem is applied. -/
private theorem history (k : Nat) (E : Row) (bits : Fin k → Bool) :
    ∃ L : Row, (∀ x, 1 ≤ x → zrow L k x = E x) ∧
      ∀ i : Fin k, zrow L i.val 1 = bits i := by
  induction k with
  | zero => exact ⟨E,fun _ => zrow_zero_of_pos E,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨P,endP,wall⟩ := ih (fun i => bits i.succ)
    let L := back (bits 0) P
    have shift (i x : Nat) : zrow L (i+1) x = zrow P i x := by
      rw [Nat.add_comm i 1,zrow_shift]
      exact zrow_congr (zrow_back (bits 0) P) i x
    refine ⟨L,fun x hx => (shift k x).trans (endP x hx),?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact (shift j.val 1).trans (wall j)

theorem capacity_at_settling_age : CapacityAtSettlingAge := by
  intro k w age hw cap settled
  have finite := finite_clause hw cap settled
  refine ⟨physical_clause hw cap settled,finite,?_⟩
  intro Y t nz aged bits
  obtain ⟨L,pre,trace⟩ := history k (rowOfNat (iter F t Y)) bits
  obtain ⟨A,rep,image,top⟩ := finite Y t nz aged L pre
  exact ⟨A,image,top,fun i => (zrow_rowOfNat A i.val 1).symm.trans
    ((zrow_congr rep i.val 1).trans (trace i))⟩

theorem conditional_every_k : ConditionalEveryK := by
  intro capacity k
  have spec : 0 < widthFor capacity k ∧ k ≤ K1 (widthFor capacity k) := by
    unfold widthFor
    dsimp only
    cases h : (List.range (capacity k).choose).find? (fun w => decide (0 < w ∧ k ≤ K1 w)) with
    | none => exact (capacity k).choose_spec
    | some w =>
      have found := List.find?_some h
      exact of_decide_eq_true found
  exact capacity_at_settling_age k _ _ spec.1 spec.2 (uniform_settling spec.1)

/-! ## Universal 16-Phase Collapse of `K1` Through Width `53,208` and Unconditional `TargetAt` Milestones (`periodic_oddBand_eq_bPhase_of_le_53208`, `K1_eq_universalK1_of_le_53208`, `K1_values_and_unconditional_targetAt_w300`) -/

/-- Phase `r` of the universal 16-periodic left strip truncated to band width `w`. -/
def bPhase (w r : Nat) : Nat := rowAt w (B % 2 ^ w) r

/-- 16-phase exact formula for `K1 w` on the universal left-side range `1 ≤ w ≤ 53208`. -/
def universalK1 (w : Nat) : Nat :=
  (List.range 16).foldl (fun worst r => min worst (phaseCapacity w (bPhase w r) 16)) w

theorem stepK_mod_eq {w K : Nat} (hwK : w ≤ K) (v : Nat) :
    stepK w (v % 2 ^ w) = stepK K v % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · have hjK : j < K := by omega
    rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
    cases j with
    | zero =>
      rw [stepK_bit_zero (by omega), stepK_bit_zero (by omega),
        Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
    | succ j1 =>
      cases j1 with
      | zero =>
        rw [stepK_bit_one (by omega), stepK_bit_one (by omega),
          Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_true (by omega : 0 < w), decide_eq_true hj, Bool.true_and, Bool.true_and]
      | succ i =>
        rw [stepK_bit_step hj, stepK_bit_step hjK,
          Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_true (by omega : i < w), decide_eq_true (by omega : i + 1 < w),
          decide_eq_true hj, Bool.true_and, Bool.true_and, Bool.true_and]
  · have hlt1 : stepK w (v % 2 ^ w) < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have hlt2 : stepK K v % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have hge : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt1 hge),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt2 hge)]

theorem rowAt_mod_eq {w K : Nat} (hwK : w ≤ K) (v : Nat) :
    ∀ t : Nat, rowAt w (v % 2 ^ w) t = rowAt K v t % 2 ^ w
  | 0 => rfl
  | t + 1 => by
    simp only [rowAt]
    rw [rowAt_mod_eq hwK v t, stepK_mod_eq hwK (rowAt K v t)]

theorem bPhase_eq_rowAt_B_mod {w : Nat} (hw : w ≤ 53209) (r : Nat) :
    bPhase w r = rowAt 53209 B r % 2 ^ w :=
  rowAt_mod_eq hw B r

theorem bPhase_add {w : Nat} (hw : w ≤ 53209) (r t : Nat) :
    bandAt w (bPhase w r) t = bPhase w (r + t) := by
  unfold bandAt
  rw [bPhase_eq_rowAt_B_mod hw r, rowAt_mod_eq hw (rowAt 53209 B r) t,
    bPhase_eq_rowAt_B_mod hw (r + t)]
  congr 1
  induction t with
  | zero => simp [rowAt]
  | succ t ih =>
    show stepK 53209 (rowAt 53209 (rowAt 53209 B r) t) = stepK 53209 (rowAt 53209 B (r + t))
    rw [ih]

theorem bPhase_period_16 {w : Nat} (hw : w ≤ 53209) (r : Nat) :
    bandAt w (bPhase w r) 16 = bPhase w r := by
  rw [bPhase_add hw r 16, bPhase_eq_rowAt_B_mod hw (r + 16), bPhase_eq_rowAt_B_mod hw r]
  have h16 : r + 16 = r + 1 * 16 := by omega
  rw [h16, rowAt_add_mul B_return r 1]

theorem bPhase_oddBand {w : Nat} (hw1 : 1 ≤ w) (hw : w ≤ 53209) (r : Nat) :
    OddBand w (bPhase w r) := by
  rw [bPhase_eq_rowAt_B_mod hw r]
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos w), ?_⟩
  rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega : 0 < w), Bool.true_and]
  exact C_zero r

/-- **Classification of All Periodic Odd Bands up to Width `53,208`
(`periodic_oddBand_eq_bPhase_of_le_53208`).**
Every odd band `v` of width `1 ≤ w ≤ 53208` on a periodic cycle of `bandStep w`
equals `bPhase w r` for some phase `r < 16`, and therefore has period dividing `16`
(`bandAt w v 16 = v`). -/
theorem periodic_oddBand_eq_bPhase_of_le_53208 {w v q : Nat}
    (hw1 : 1 ≤ w) (hw : w ≤ 53208) (hodd : OddBand w v)
    (hq : 0 < q) (hcyc : bandAt w v q = v) :
    (∃ r : Nat, r < 16 ∧ v = bPhase w r) ∧ bandAt w v 16 = v := by
  have hex : ∃ r : Nat, r < 16 ∧ v = bPhase w r := by
    by_cases hw_gt1 : 1 < w
    · obtain ⟨s, huniv⟩ := universal_left_side (x := ofRow v) (lo := 0) (ofRow_left v)
        (by simpa [ofRow] using hodd.2)
      have hunif : ∀ m : Nat, m ≤ w →
          ∃ T : Nat, ∀ j : Nat, j < m → ∀ t : Nat, T ≤ t →
            Rule30FiniteDiagonals.Ld (ofRow v) 0 j (t + s) = C j t := by
        intro m
        induction m with
        | zero => intro _; exact ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
        | succ m ih =>
          intro hmw
          obtain ⟨T1, hT1⟩ := ih (by omega)
          obtain ⟨T2, hT2⟩ := huniv m (by omega)
          refine ⟨max T1 T2, fun j hj t ht => ?_⟩
          by_cases hjm : j < m
          · exact hT1 j hjm t (Nat.le_trans (Nat.le_max_left T1 T2) ht)
          · have hjeq : j = m := by omega
            subst hjeq
            exact hT2 t (Nat.le_trans (Nat.le_max_right T1 T2) ht)
      obtain ⟨T, hT⟩ := hunif w (Nat.le_refl w)
      let t0 := (T + s + 1) * q - s
      have ht0_ge : T ≤ t0 := by
        have h1 : T + s + 1 ≤ (T + s + 1) * q := Nat.le_mul_of_pos_right _ hq
        dsimp [t0]; omega
      have ht0_add : t0 + s = 0 + (T + s + 1) * q := by
        have h1 : s ≤ (T + s + 1) * q :=
          Nat.le_trans (by omega : s ≤ T + s + 1) (Nat.le_mul_of_pos_right _ hq)
        dsimp [t0]; omega
      refine ⟨t0 % 16, Nat.mod_lt _ (by decide), ?_⟩
      rw [bPhase_eq_rowAt_B_mod (by omega)]
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hjw : j < w
      · have hLd := hT j hjw t0 ht0_ge
        rw [Ld_ofRow hw_gt1 v (t0 + s) j hjw, ht0_add,
          rowAt_add_mul hcyc 0 (T + s + 1)] at hLd
        dsimp only [rowAt] at hLd
        rw [hLd, C_mod j t0, Nat.testBit_mod_two_pow, decide_eq_true hjw, Bool.true_and]
        rfl
      · have hlt_v : v < 2 ^ j :=
          Nat.lt_of_lt_of_le hodd.1 (Nat.pow_le_pow_right (by decide) (by omega))
        have hlt_b : rowAt 53209 B (t0 % 16) % 2 ^ w < 2 ^ j :=
          Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w))
            (Nat.pow_le_pow_right (by decide) (by omega))
        rw [Nat.testBit_lt_two_pow hlt_v, Nat.testBit_lt_two_pow hlt_b]
    · have hw_eq1 : w = 1 := by omega
      subst hw_eq1
      have hv1 : v = 1 := by
        have hlt := hodd.1
        have hb0 := hodd.2
        rw [Nat.testBit_zero] at hb0
        have hb0' : v % 2 = 1 := of_decide_eq_true hb0
        omega
      refine ⟨0, by decide, ?_⟩
      rw [hv1, bPhase_eq_rowAt_B_mod (by decide)]
      dsimp only [rowAt]
      have hb := B_bit
      rw [Nat.testBit_zero] at hb
      have hb' : B % 2 = 1 := of_decide_eq_true hb
      omega
  refine ⟨hex, ?_⟩
  obtain ⟨r, _, rfl⟩ := hex
  exact bPhase_period_16 (by omega) r

theorem returnPeriod_walk_minimal (w v fuel elapsed p : Nat) :
    returnPeriod.walk w v fuel (bandAt w v elapsed) elapsed = some p →
      elapsed < p ∧ bandAt w v p = v ∧
      ∀ t : Nat, elapsed < t → t < p → bandAt w v t ≠ v := by
  induction fuel generalizing elapsed with
  | zero => simp [returnPeriod.walk]
  | succ fuel ih =>
    rw [returnPeriod.walk]
    change (if bandAt w v (elapsed + 1) = v then some (elapsed + 1)
      else returnPeriod.walk w v fuel (bandAt w v (elapsed + 1)) (elapsed + 1)) = some p → _
    split <;> rename_i heq
    · intro hs
      injection hs with hp
      subst hp
      exact ⟨by omega, heq, fun t h1 h2 => by omega⟩
    · intro hs
      obtain ⟨hlt, hret, hmin⟩ := ih (elapsed + 1) hs
      refine ⟨by omega, hret, fun t h1 h2 => ?_⟩
      by_cases ht1 : t = elapsed + 1
      · subst ht1; exact heq
      · exact hmin t (by omega) h2

theorem returnPeriod_minimal {w v p : Nat} (h : returnPeriod w v = some p) :
    0 < p ∧ bandAt w v p = v ∧ ∀ t : Nat, 0 < t → t < p → bandAt w v t ≠ v :=
  returnPeriod_walk_minimal w v (2 ^ (w - 1)) 0 p h

theorem returnPeriod_walk_isSome_of_hit (w v fuel elapsed : Nat)
    (h : ∃ p, elapsed < p ∧ p ≤ elapsed + fuel ∧ bandAt w v p = v) :
    ∃ q, returnPeriod.walk w v fuel (bandAt w v elapsed) elapsed = some q := by
  induction fuel generalizing elapsed with
  | zero => obtain ⟨_, _, _, _⟩ := h; omega
  | succ fuel ih =>
    rw [returnPeriod.walk]
    change ∃ q, (if bandAt w v (elapsed + 1) = v then some (elapsed + 1)
      else returnPeriod.walk w v fuel (bandAt w v (elapsed + 1)) (elapsed + 1)) = some q
    split <;> rename_i heq
    · exact ⟨elapsed + 1, rfl⟩
    · apply ih (elapsed + 1)
      obtain ⟨p, lo, hi, hp⟩ := h
      have hne : p ≠ elapsed + 1 := by rintro rfl; exact heq hp
      exact ⟨p, by omega, by omega, hp⟩

theorem returnPeriod_isSome_of_period_16 {n v : Nat}
    (hodd : OddBand (n + 1) v) (h16 : bandAt (n + 1) v 16 = v) :
    ∃ q, returnPeriod (n + 1) v = some q := by
  by_cases hn4 : 4 ≤ n
  · have h16_le : 16 ≤ 2 ^ n :=
      Nat.le_trans (by decide : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by decide) hn4)
    exact returnPeriod_walk_isSome_of_hit (n + 1) v (2 ^ n) 0 ⟨16, by omega, by omega, h16⟩
  · -- For n < 4 (w ∈ {1, 2, 3, 4}), check by pigeonhole on 2^n odd words:
    have hpig : ∃ i j : Nat, i < j ∧ j ≤ 2 ^ n ∧ bandAt (n + 1) v i = bandAt (n + 1) v j := by
      apply Classical.byContradiction
      intro hn
      have hodd_t : ∀ t : Nat, OddBand (n + 1) (bandAt (n + 1) v t) := by
        intro t
        induction t with
        | zero => exact hodd
        | succ t ih => exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), (stepK_bit_zero (by omega) _).trans ih.2⟩
      have nd := Rule30Jen.nodup_map_of_inj (fun t => bandAt (n + 1) v t / 2)
        (List.nodup_range (n := 2 ^ n + 1)) (by
          intro i hi j hj e
          simp only [List.mem_range] at hi hj
          have pi : bandAt (n + 1) v i % 2 = 1 := by simpa [Nat.testBit_zero] using (hodd_t i).2
          have pj : bandAt (n + 1) v j % 2 = 1 := by simpa [Nat.testBit_zero] using (hodd_t j).2
          have heq : bandAt (n + 1) v i = bandAt (n + 1) v j := by omega
          rcases Nat.lt_trichotomy i j with lt | eq | gt
          · exact (hn ⟨i, j, lt, by omega, heq⟩).elim
          · exact eq
          · exact (hn ⟨j, i, gt, by omega, heq.symm⟩).elim)
      have sz := Rule30Jen.length_le_of_subset (l₂ := List.range (2 ^ n)) nd (by
        intro x hx
        obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
        have hlt := (hodd_t t).1
        rw [Nat.pow_succ] at hlt
        exact List.mem_range.mpr (by omega))
      simp at sz; omega
    obtain ⟨i, j, hlt, hjle, heq⟩ := hpig
    let sh := (i + 1) * 16 - i
    have hi_le : i ≤ (i + 1) * 16 := by omega
    have hpush : bandAt (n + 1) v (i + sh) = bandAt (n + 1) v (j + sh) := by
      unfold bandAt at heq ⊢
      induction sh with
      | zero => simpa using heq
      | succ k ih => show stepK (n + 1) (rowAt (n + 1) v (i + k)) = stepK (n + 1) (rowAt (n + 1) v (j + k)); rw [ih]
    have h1 : i + sh = 0 + (i + 1) * 16 := by dsimp [sh]; omega
    have h2 : j + sh = (j - i) + (i + 1) * 16 := by dsimp [sh]; omega
    rw [h1, h2] at hpush
    unfold bandAt at h16 hpush
    rw [rowAt_add_mul h16, rowAt_add_mul h16] at hpush
    exact returnPeriod_walk_isSome_of_hit (n + 1) v (2 ^ n) 0
      ⟨j - i, by omega, by omega, hpush.symm⟩

theorem sixteen_mod_returnPeriod_eq_zero {w v p : Nat}
    (h16 : bandAt w v 16 = v) (hret : returnPeriod w v = some p) :
    16 % p = 0 := by
  obtain ⟨hp_pos, hp_cyc, hp_min⟩ := returnPeriod_minimal hret
  have hdiv : 16 = 16 % p + (16 / p) * p := by rw [Nat.mul_comm]; exact (Nat.mod_add_div 16 p).symm
  have hrem_cyc : bandAt w v (16 % p) = v := by
    have h := h16
    rw [hdiv] at h
    unfold bandAt at h hp_cyc ⊢
    rwa [rowAt_add_mul hp_cyc (16 % p) (16 / p)] at h
  have hrem_lt : 16 % p < p := Nat.mod_lt 16 hp_pos
  by_cases h0 : 16 % p = 0
  · exact h0
  · exact absurd hrem_cyc (hp_min (16 % p) (by omega) hrem_lt)

theorem schedule_eq_of_dvd_16 {w v p : Nat}
    (hp_pos : 0 < p) (hp_dvd : 16 % p = 0) (hp_cyc : bandAt w v p = v) :
    ∀ fuel d avail : Nat, schedule w v p fuel d avail = schedule w v 16 fuel d avail := by
  have hp_cases : p = 1 ∨ p = 2 ∨ p = 4 ∨ p = 8 ∨ p = 16 := by
    have hle : p ≤ 16 := by
      apply Nat.le_of_not_lt
      intro hgt
      rw [Nat.mod_eq_of_lt hgt] at hp_dvd
      omega
    have h16_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨
        p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 := by omega
    rcases h16_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hp_dvd ⊢
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro d avail
    simp only [schedule]
    have hphase_eq : bandAt w v ((p - d % p) % p) = bandAt w v ((16 - d % 16) % 16) := by
      let b := (16 - d % 16) % 16
      have hb_mod : b % p = (p - d % p) % p := by
        dsimp [b]
        rcases hp_cases with rfl | rfl | rfl | rfl | rfl <;> omega
      have hb_decomp : b = b % p + (b / p) * p := by
        rw [Nat.mul_comm]; exact (Nat.mod_add_div b p).symm
      change bandAt w v ((p - d % p) % p) = bandAt w v b
      rw [hb_decomp]
      unfold bandAt at hp_cyc ⊢
      rw [rowAt_add_mul hp_cyc (b % p) (b / p), hb_mod]
    rw [hphase_eq]
    cases firstReset (bandAt w v ((16 - d % 16) % 16)) avail with
    | none => rfl
    | some j => dsimp only; rw [ih (d + 1) j]

theorem phaseCapacity_eq_16_of_dvd_16 {w v p : Nat}
    (hp_pos : 0 < p) (hp_dvd : 16 % p = 0) (hp_cyc : bandAt w v p = v) :
    phaseCapacity w v p = phaseCapacity w v 16 :=
  schedule_eq_of_dvd_16 hp_pos hp_dvd hp_cyc w 0 w

theorem foldl_step_lower {α : Type} (step : Nat → α → Nat) (xs : List α) (init bound : Nat)
    (hinit : bound ≤ init) (hstep : ∀ acc x, x ∈ xs → bound ≤ acc → bound ≤ step acc x) :
    bound ≤ xs.foldl step init := by
  induction xs generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (step init x) (hstep init x (List.mem_cons_self ..) hinit)
      (fun acc y hy hacc => hstep acc y (List.mem_cons_of_mem x hy) hacc)

theorem foldl_step_upper_at {α : Type} (step : Nat → α → Nat)
    (hmono : ∀ acc x, step acc x ≤ acc)
    (xs : List α) (init : Nat) :
    xs.foldl step init ≤ init ∧
    ∀ x ∈ xs, ∀ bound, (∀ acc, step acc x ≤ bound) → xs.foldl step init ≤ bound := by
  induction xs generalizing init with
  | nil => exact ⟨Nat.le_refl init, fun _ h => by simp at h⟩
  | cons a xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (step init a)
    refine ⟨Nat.le_trans h1 (hmono init a), fun x hx bound hb => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Nat.le_trans h1 (hb init)
    · exact h2 x hmem bound hb

/-- **Exact Collapse of the `2 ^ (w - 1)`-State `K1 w` Fold to the 16-Phase `universalK1 w`
(`K1_eq_universalK1_of_le_53208`).**
For every band width `1 ≤ w ≤ 53208`, `Rule30EveryKStatement.K1 w = universalK1 w`. -/
theorem K1_eq_universalK1_of_le_53208 {w : Nat} (hw1 : 1 ≤ w) (hw : w ≤ 53208) :
    K1 w = universalK1 w := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  let stepFn : Nat → Nat → Nat := fun worst i =>
    let v := 2 * i + 1
    match returnPeriod (n + 1) v with
    | none => worst
    | some period => min worst (phaseCapacity (n + 1) v period)
  have hmono_K1 : ∀ acc i, stepFn acc i ≤ acc := by
    intro acc i; dsimp [stepFn]; split
    · exact Nat.le_refl acc
    · exact Nat.min_le_left ..
  let stepU : Nat → Nat → Nat := fun worst r =>
    min worst (phaseCapacity (n + 1) (bPhase (n + 1) r) 16)
  have hmono_U : ∀ acc r, stepU acc r ≤ acc := fun acc r => Nat.min_le_left ..
  apply Nat.le_antisymm
  · -- K1 (n + 1) ≤ universalK1 (n + 1)
    unfold universalK1
    refine foldl_step_lower stepU (List.range 16) (n + 1) (K1 (n + 1)) ?_ (fun acc r _ hacc => ?_)
    · exact (foldl_step_upper_at stepFn hmono_K1 (List.range (2 ^ n)) (n + 1)).1
    · dsimp [stepU]
      refine Nat.le_min.mpr ⟨hacc, ?_⟩
      have hodd := bPhase_oddBand (w := n + 1) hw1 (by omega) r
      have h16 := bPhase_period_16 (w := n + 1) (by omega) r
      obtain ⟨p, hret⟩ := returnPeriod_isSome_of_period_16 hodd h16
      obtain ⟨hp_pos, hp_cyc, _⟩ := returnPeriod_minimal hret
      have hp_dvd := sixteen_mod_returnPeriod_eq_zero h16 hret
      rw [← phaseCapacity_eq_16_of_dvd_16 hp_pos hp_dvd hp_cyc]
      let i0 := bPhase (n + 1) r / 2
      have hv_eq : 2 * i0 + 1 = bPhase (n + 1) r := by
        have hpar : bPhase (n + 1) r % 2 = 1 := by simpa [Nat.testBit_zero] using hodd.2
        dsimp [i0]; omega
      have hi0_mem : i0 ∈ List.range (2 ^ n) := by
        have hlt := hodd.1
        rw [Nat.pow_succ] at hlt
        exact List.mem_range.mpr (by dsimp [i0]; omega)
      exact (foldl_step_upper_at stepFn hmono_K1 (List.range (2 ^ n)) (n + 1)).2 i0 hi0_mem
        (phaseCapacity (n + 1) (bPhase (n + 1) r) p)
        (fun a => by dsimp [stepFn]; rw [hv_eq, hret]; exact Nat.min_le_right ..)
  · -- universalK1 (n + 1) ≤ K1 (n + 1)
    unfold K1
    refine foldl_step_lower stepFn (List.range (2 ^ n)) (n + 1) (universalK1 (n + 1)) ?_
      (fun acc i hi hacc => ?_)
    · exact (foldl_step_upper_at stepU hmono_U (List.range 16) (n + 1)).1
    · dsimp [stepFn]
      cases hret : returnPeriod (n + 1) (2 * i + 1) with
      | none => exact hacc
      | some p =>
        refine Nat.le_min.mpr ⟨hacc, ?_⟩
        obtain ⟨hp_pos, hp_cyc, _⟩ := returnPeriod_minimal hret
        have hi_lt : i < 2 ^ n := List.mem_range.mp hi
        have hodd_i : OddBand (n + 1) (2 * i + 1) := by
          refine ⟨by rw [Nat.pow_succ]; omega, ?_⟩
          rw [Nat.testBit_zero]; exact decide_eq_true (by omega)
        obtain ⟨⟨r, hr_lt, hv_eq⟩, h16⟩ :=
          periodic_oddBand_eq_bPhase_of_le_53208 hw1 hw hodd_i hp_pos hp_cyc
        have hp_dvd := sixteen_mod_returnPeriod_eq_zero h16 hret
        rw [phaseCapacity_eq_16_of_dvd_16 hp_pos hp_dvd hp_cyc, hv_eq]
        exact (foldl_step_upper_at stepU hmono_U (List.range 16) (n + 1)).2 r
          (List.mem_range.mpr hr_lt)
          (phaseCapacity (n + 1) (bPhase (n + 1) r) 16)
          (fun a => Nat.min_le_right ..)

def b300 : Nat := 0x1c63e4023be658e57fe944a96853a314f81afeaafaaafd974d21462e2bd062e7e17e2f1e713

theorem B_mod_300 : B % 2 ^ 300 = b300 := by decide +kernel

def universalK1From (w b0 : Nat) : Nat :=
  (List.range 16).foldl (fun worst r => min worst (phaseCapacity w (rowAt w b0 r) 16)) w

theorem universalK1_eq_from (w : Nat) : universalK1 w = universalK1From w (B % 2 ^ w) := rfl

theorem K1_300_eq_25 : K1 300 = 25 := by
  rw [K1_eq_universalK1_of_le_53208 (by decide) (by decide), universalK1_eq_from, B_mod_300]
  decide +kernel

/-- **Exact `K1` Milestones and Unconditional Inverse-Tick Theorem Through `k = 25`
(`K1_values_and_unconditional_targetAt_w300`).**
Without assuming `CAP`, proves `K1 8 = 1`, `K1 20 = 2`, `K1 100 = 6`, `K1 200 = 17`,
`K1 300 = 25`, and `TargetAt k (settlingBound 300)` (`PhysicalEdge k`, `FinitePredecessor k`,
and `AllHistories k`) for every `k ≤ 25`. -/
theorem K1_values_and_unconditional_targetAt_w300 :
    K1 8 = 1 ∧ K1 20 = 2 ∧ K1 100 = 6 ∧ K1 200 = 17 ∧ K1 300 = 25 ∧
    ∀ k : Nat, k ≤ 25 → TargetAt k (settlingBound 300) := by
  have h8 : K1 8 = 1 := by
    rw [K1_eq_universalK1_of_le_53208 (by decide) (by decide), universalK1_eq_from,
      show B % 2 ^ 8 = 0x13 by decide +kernel]
    decide +kernel
  have h20 : K1 20 = 2 := by
    rw [K1_eq_universalK1_of_le_53208 (by decide) (by decide), universalK1_eq_from,
      show B % 2 ^ 20 = 0x1e713 by decide +kernel]
    decide +kernel
  have h100 : K1 100 = 6 := by
    rw [K1_eq_universalK1_of_le_53208 (by decide) (by decide), universalK1_eq_from,
      show B % 2 ^ 100 = 0x21462e2bd062e7e17e2f1e713 by decide +kernel]
    decide +kernel
  have h200 : K1 200 = 17 := by
    rw [K1_eq_universalK1_of_le_53208 (by decide) (by decide), universalK1_eq_from,
      show B % 2 ^ 200 = 0x853a314f81afeaafaaafd974d21462e2bd062e7e17e2f1e713 by decide +kernel]
    decide +kernel
  refine ⟨h8, h20, h100, h200, K1_300_eq_25, fun k hk => ?_⟩
  refine capacity_at_settling_age k 300 (settlingBound 300) (by decide) ?_
    (uniform_settling (by decide))
  rw [K1_300_eq_25]
  exact hk

end Ruliology.CellularAutomata.Rule30EveryKInverse
