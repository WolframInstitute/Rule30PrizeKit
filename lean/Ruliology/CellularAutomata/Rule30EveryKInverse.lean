module

public import Ruliology.CellularAutomata.Rule30EveryKCascade

/-!
# The conditional inverse-tick theorem at a uniform age

Attach the minimum over edge cycles to the physical cascade and to
finite rows at a fixed white wall. All widths and tick counts are natural numbers.
-/

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

end Ruliology.CellularAutomata.Rule30EveryKInverse
