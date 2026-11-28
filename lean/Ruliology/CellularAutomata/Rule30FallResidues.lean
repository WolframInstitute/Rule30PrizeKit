module

public import Ruliology.CellularAutomata.Rule30Certificates.FallResidueStrip
public import Ruliology.CellularAutomata.Rule30Certificates.FallResidues3
public import Ruliology.CellularAutomata.Rule30Certificates.FallResidues4
public import Ruliology.CellularAutomata.Rule30Certificates.FallResidues5
public import Ruliology.CellularAutomata.Rule30Certificates.FallResidues7
public import Ruliology.CellularAutomata.Rule30Certificates.FallResidues11
public import Ruliology.CellularAutomata.Rule30Certificates.FallResidues13
public import Ruliology.CellularAutomata.Rule30Certificates.FallResidues17

/-!
# Two falling residues in every six columns of the single seed, at every modulus from three

A column of Rule 30 from a single black cell *falls* at tick `t` when it is black at `t` and white at `t + 1`
(`Fall`). `Cofinal i r` says that column `i` falls at ticks congruent to `r` modulo `m` after every cutoff.

* `two_cofinal_every_modulus`: for every modulus `m ≥ 3` and every integer `i`, one of the six columns
  `i, …, i + 5` has cofinal falls at two different residues modulo `m`. The column and the residues may depend on
  `m` and `i`.
* `not_good_parity`: a control at modulus two. A four-row loop of the six-cell strip with free exterior cells has
  every fall on an even tick, and every adjacent pair changes under the lag-two shift. So the strip argument does
  not reach parity.

The proof. Suppose each of the six columns kept its late falls to one residue. Then the six cells follow a strip
graph with both exterior cells free and a calendar of `m` slots (`Run`, in `Rule30Certificates.FallResidueStrip`).
If three successive updates are quiet, the first leaves the strip unchanged (`quiet_eq`), so one slot can be deleted
from every period and any modulus above 18 reduces to 18 (`good_of_small`). Divisibility leaves the moduli 3, 4, 5,
7, 11, 13 and 17 (`good_of_dvd`), where rank certificates show that some adjacent pair of columns repeats every
period (`good3`, …, `good17`, in `Rule30Certificates.FallResidues3` to `FallResidues17`). Jen's theorem forbids that
on the single seed (`two_cofinal_from_good`, with `Rule30Jen.not_adjacent`).

The trapped window with freely chosen exterior cells is KDRonald3 and Claude's method (Rule 30 Prize submission
R30-20261115-2d4add); here the graph carries a clock.
-/

@[expose] public section

/-! Coupling six observed columns to the graph with two free exterior bits.
Bit zero and ternary digit zero refer to the westernmost observed site. -/
namespace Ruliology.CellularAutomata.Rule30FallResidues.Six

open Ruliology.CellularAutomata Rule30Jen Rule30StripCertificates

def step (s : Nat) (w e : Bool) : Nat := stripStep 6 w e s

def row (T : Nat) (j : Int) : Nat := encRow T (j-1) 6

theorem row_lt (T : Nat) (j : Int) : row T j < 64 :=
  (enc_encRow 6 T (j-1)).1

theorem row_bit (T : Nat) (j : Int) (k : Nat) (hk : k<6) :
    (row T j).testBit k = cell T (j+k) := by
  simpa [row] using (enc_encRow 6 T (j-1)).2 k hk

theorem row_step (T : Nat) (j : Int) :
    row (T+1) j = step (row T j) (cell T (j-1)) (cell T (j+6)) := by
  have nxt := enc_step (enc_encRow 6 T (j-1))
  simp only [Int.sub_add_cancel] at nxt
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k<6
  · rw [row_bit _ _ k hk]
    simpa [step,row] using (nxt.2 k hk).symm
  · have cut : 2^6 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (row_lt _ _) cut)]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le nxt.1 cut)).symm

/-- In a permitted edge, every site falling now has its assigned time phase. -/
def allowed (a t s d : Nat) : Bool :=
  (List.range 6).all fun k => !(s.testBit k && !d.testBit k) || t == a / 3^k % 3

theorem allowed_succ (a t T : Nat) (j : Int)
    (h : ∀ k : Nat, k<6 → cell T (j+k) = true → cell (T+1) (j+k) = false →
      t = a / 3^k % 3) :
    allowed a t (row T j) (row (T+1) j) = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have bound := List.mem_range.mp hk
  simp only [row_bit _ _ k bound]
  cases on : cell T (j+k) <;> cases off : cell (T+1) (j+k) <;> try rfl
  simp [h k bound on off]

def encode (p : Nat → Nat) : Nat :=
  p 0 + 3 * p 1 + 9 * p 2 + 27 * p 3 + 81 * p 4 + 243 * p 5

theorem encode_lt (p : Nat → Nat) (hp : ∀ k, k<6 → p k<3) : encode p < 729 := by
  have := hp 0 (by decide)
  have := hp 1 (by decide)
  have := hp 2 (by decide)
  have := hp 3 (by decide)
  have := hp 4 (by decide)
  have := hp 5 (by decide)
  unfold encode
  omega

theorem encode_digit (p : Nat → Nat) (hp : ∀ k, k<6 → p k<3) (k : Nat) (hk : k<6) :
    encode p / 3^k % 3 = p k := by
  have := hp 0 (by decide)
  have := hp 1 (by decide)
  have := hp 2 (by decide)
  have := hp 3 (by decide)
  have := hp 4 (by decide)
  have := hp 5 (by decide)
  unfold encode
  rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reducePow] <;> omega

theorem encode_mod (p : Nat → Nat) (hp : ∀ k, k<6 → p k<3) (h0 : p 0=0) :
    encode p % 3 = 0 := by
  simpa [h0] using encode_digit p hp 0 (by decide)

end Ruliology.CellularAutomata.Rule30FallResidues.Six

namespace Ruliology.CellularAutomata.Rule30FallResidues

open Ruliology.CellularAutomata Rule30Jen

/-- Skip slot d in every round, keeping the row at the end of the idle update. -/
def insertSlot (d k : Nat) : Nat := if k < d then k else k+1

def deleteSlot (d k : Nat) : Nat := if k ≤ d then k else k-1

def expandTime (m d t : Nat) : Nat := (t/(m-1))*m + insertSlot d (t%(m-1))

def contractTime (m d t : Nat) : Nat := (t/m)*(m-1) + deleteSlot d (t%m)

theorem insert_bound {m d k : Nat} (hk : k < m-1) : insertSlot d k < m := by
  unfold insertSlot
  split <;> omega

private theorem not_insert {d k : Nat} : insertSlot d k ≠ d := by
  unfold insertSlot
  split <;> omega

theorem delete_bound {m d k : Nat} (hk : k < m) (hd : d+2 < m) :
    deleteSlot d k < m-1 := by
  unfold deleteSlot
  split <;> omega

private theorem phase_equiv {r k d : Nat} (hr : r ≠ d) :
    deleteSlot d r = k ↔ r = insertSlot d k := by
  unfold deleteSlot insertSlot
  split <;> split <;> omega

private theorem expand_phase {m d t : Nat} (hm : 1 < m) :
    expandTime m d t % m = insertSlot d (t%(m-1)) := by
  unfold expandTime
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
  exact insert_bound (Nat.mod_lt _ (by omega))

private theorem divMod_succ {t p : Nat} (hp : 0 < p) :
    (t+1)/p = (t%p+1)/p + t/p ∧ (t+1)%p = (t%p+1)%p := by
  have q : t+1 = t%p+1+p*(t/p) := by have := Nat.mod_add_div t p; omega
  conv => lhs; rw [q, Nat.add_mul_div_left _ _ hp]
  exact ⟨rfl, by conv => lhs; rw [q, Nat.add_mul_mod_self_left]⟩

private theorem expand_succ {m d t : Nat} (hd : 0 < d) (hb : d+2 < m) :
    expandTime m d (t+1) = expandTime m d t + (if t%(m-1)+1=d then 2 else 1) := by
  have hp : 0 < m-1 := by omega
  have hr := Nat.mod_lt t hp
  obtain ⟨dvd,mod⟩ := divMod_succ (t:=t) hp
  unfold expandTime
  rw [dvd,mod]
  by_cases c : t%(m-1)+1 < m-1
  · rw [Nat.div_eq_of_lt c, Nat.mod_eq_of_lt c, Nat.zero_add]
    unfold insertSlot
    split <;> split <;> split <;> omega
  · have e : t%(m-1)+1=m-1 := by omega
    rw [e, Nat.div_self hp, Nat.mod_self, ite_eq_right (show m-1≠d by omega)]
    simp only [insertSlot, ite_eq_left hd, ite_eq_right (show ¬ t%(m-1)<d by omega),
      Nat.add_zero, Nat.add_mul, Nat.one_mul]
    omega

private theorem expand_contract {m d t : Nat} (hb : d+2 < m) :
    expandTime m d (contractTime m d t) = t + (if t%m=d then 1 else 0) := by
  have hp : 0 < m-1 := by omega
  have hr := Nat.mod_lt t (show 0 < m by omega)
  have hsmall := delete_bound hr hb
  have div : contractTime m d t / (m-1) = t/m := by
    unfold contractTime
    rw [Nat.add_comm, Nat.mul_comm (t/m) (m-1), Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt hsmall, Nat.zero_add]
  have mod : contractTime m d t % (m-1) = deleteSlot d (t%m) := by
    unfold contractTime
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsmall]
  unfold expandTime
  rw [div,mod]
  have decom := Nat.div_add_mod t m
  rw [Nat.mul_comm (t/m) m]
  unfold insertSlot deleteSlot
  split <;> split <;> split <;> omega

private theorem quiet_idle {m d t : Nat} {a x : Nat → Nat} (h : Run 6 m a x)
    (hb : d+2 < m) (ht : t%m=d)
    (quiet : ∀ j, j < 6 → a j < d ∨ d+2 < a j) : x (t+1) = x t := by
  have zero (i : Nat) (hi : i ≤ 2) : permit 6 a ((t+i)%m) = 0 := by
    rw [Nat.add_mod t i m, ht, Nat.mod_eq_of_lt (show i < m by omega),
      Nat.mod_eq_of_lt (show d+i<m by omega)]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [permit_bit, Nat.zero_testBit]
    by_cases hj : j < 6
    · have := quiet j hj
      simp [show a j ≠ d+i by omega]
    · simp [hj]
  have h0 := h.edge t
  have h1 := h.edge (t+1)
  have h2 := h.edge (t+2)
  rw [show permit 6 a (t%m) = 0 by simpa using zero 0 (by decide)] at h0
  rw [zero 1 (by decide)] at h1
  rw [zero 2 (by decide)] at h2
  exact quiet_eq (h.bounded t) h0 h1 h2

/-- A gap of three quiet ticks can be shortened by a uniform deletion in each
period. A paired reading in the shorter calendar lifts to the original one. -/
theorem good_of_deleted {m d : Nat} {a : Nat → Nat} (hd : 0 < d) (hb : d+2 < m)
    (quiet : ∀ j, j < 6 → a j < d ∨ d+2 < a j)
    (good : Good 6 (m-1) (fun j => deleteSlot d (a j))) : Good 6 m a := by
  intro x h
  let y (t : Nat) := x (expandTime m d t)
  have hy : Run 6 (m-1) (fun j => deleteSlot d (a j)) y := by
    refine ⟨fun t => h.bounded _, fun t => ?_⟩
    have edge := h.edge (expandTime m d t)
    rw [expand_phase (show 1<m by omega)] at edge
    have same : permit 6 (fun j => deleteSlot d (a j)) (t%(m-1)) =
        permit 6 a (insertSlot d (t%(m-1))) := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [permit_bit, permit_bit]
      by_cases hj : j < 6
      · have hn := quiet j hj
        simp only [hj, true_and]
        rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
        exact phase_equiv (by omega)
      · simp [hj]
    rw [same]
    change Edge 6 _ (x (expandTime m d t)) (x (expandTime m d (t+1)))
    rw [expand_succ hd hb]
    by_cases cut : t%(m-1)+1=d
    · rw [ite_eq_left cut]
      have atCut : (expandTime m d t + 1)%m = d := by
        rw [Nat.add_mod, expand_phase (show 1<m by omega), Nat.mod_eq_of_lt (show 1<m by omega)]
        simp only [insertSlot, ite_eq_left (show t%(m-1)<d by omega)]
        exact (congrArg (fun r => r % m) cut).trans (Nat.mod_eq_of_lt (by omega))
      have eq := quiet_idle h hb atCut quiet
      rwa [show expandTime m d t + 2 = expandTime m d t + 1 + 1 by omega, eq]
    · rwa [ite_eq_right cut]
  obtain ⟨j,N,hj,per⟩ := good y hy
  refine ⟨j,N*m,hj,fun t ht => ?_⟩
  have reads (s : Nat) : y (contractTime m d s) = x s := by
    unfold y
    rw [expand_contract hb]
    by_cases atCut : s%m=d
    · simpa only [ite_eq_left atCut] using quiet_idle h hb atCut quiet
    · rw [ite_eq_right atCut, Nat.add_zero]
  have repr : contractTime m d (t+m) = contractTime m d t+(m-1) := by
    unfold contractTime
    rw [Nat.add_div_right _ (show 0<m by omega), Nat.add_mod_right, Nat.add_mul, Nat.one_mul]
    omega
  have age : N ≤ contractTime m d t := by
    have hdiv := (Nat.le_div_iff_mul_le (show 0<m by omega)).mpr ht
    have hmul : t/m ≤ (t/m)*(m-1) := by
      simpa using (Nat.mul_le_mul_left (t/m) (show 1 ≤ m-1 by omega))
    unfold contractTime
    omega
  simpa only [← repr, reads] using per (contractTime m d t) age

private theorem quiet_gap {m : Nat} (hm : 18 < m) {a : Nat → Nat} (zero : a 0 = 0) :
    ∃ d, 0 < d ∧ d+2 < m ∧ ∀ j, j < 6 → a j < d ∨ d+2 < a j := by
  apply Classical.byContradiction
  intro nh
  let hit := (List.range 6).map (fun j => (a j+2)/3)
  have covered : ∀ k ∈ List.range 7, k ∈ hit := by
    intro k hk
    have hk := List.mem_range.mp hk
    by_cases z : k=0
    · exact List.mem_map.mpr ⟨0,List.mem_range.mpr (by decide),by omega⟩
    · let d := 3*k-2
      have member : ∃ j, j < 6 ∧ d ≤ a j ∧ a j ≤ d+2 := by
        apply Classical.byContradiction
        intro absent
        exact nh ⟨d,by dsimp [d]; omega,by dsimp [d]; omega,fun j hj => by
          by_cases lo : a j < d
          · exact Or.inl lo
          · exact Or.inr (by
              apply Classical.byContradiction
              intro hi
              exact absent ⟨j,hj,by omega,by omega⟩)⟩
      obtain ⟨j,hj,lo,hi⟩ := member
      exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,by dsimp [d] at lo hi; omega⟩
  have bad := length_le_of_subset (List.nodup_range (n:=7)) covered
  simp [hit] at bad

/-- The six-site problem at every modulus reduces to moduli 3 through 18. -/
theorem good_of_small {m : Nat} {a : Nat → Nat} (hm : 3 ≤ m)
    (ha : ∀ j, j < 6 → a j < m)
    (small : ∀ m, 3 ≤ m → m ≤ 18 → ∀ a, (∀ j, j < 6 → a j < m) → Good 6 m a) :
    Good 6 m a := by
  induction m using Nat.strongRecOn generalizing a with
  | ind m ih =>
    by_cases short : m ≤ 18
    · exact small m hm short a ha
    · apply good_of_rotated (q:=a 0) (ha 0 (by decide)) ha
      let b (j : Nat) := rotate m (a 0) (a j)
      change Good 6 m b
      have b0 : b 0 = 0 := by simp [b,rotate]
      obtain ⟨d,hd,hb,quiet⟩ := quiet_gap (by omega : 18 < m) b0
      apply good_of_deleted hd hb quiet
      exact ih (m-1) (by omega) (by omega) (fun j hj =>
        delete_bound (rotate_lt (ha 0 (by decide)) (ha j hj)) hb)

end Ruliology.CellularAutomata.Rule30FallResidues

namespace Ruliology.CellularAutomata.Rule30FallResidues

open Ruliology.CellularAutomata.Rule30Jen

def Fall (i : Int) (t : Nat) : Prop := cell t i = true ∧ cell (t+1) i = false

def Cofinal {m : Nat} (i : Int) (r : Fin m) : Prop :=
  ∀ T, ∃ t, T ≤ t ∧ t%m = r.val ∧ Fall i t

private theorem escape {m : Nat} (hm : 0 < m) (i : Int) (a : Fin 6 → Fin m)
    (good : ∀ a, (∀ j, j < 6 → a j < m) → Good 6 m a) (T : Nat) :
    ∃ (j : Fin 6) (t : Nat), T ≤ t ∧ Fall (i+j.val) t ∧ t%m ≠ (a j).val := by
  apply Classical.byContradiction
  intro no
  let S := T*m
  have Slarge : T ≤ S := by
    simpa [S] using Nat.mul_le_mul_left T (show 1 ≤ m by omega)
  let phases (j : Nat) := if hj : j < 6 then (a ⟨j,hj⟩).val else 0
  let x (t : Nat) := Six.row (S+t) i
  have run : Run 6 m phases x := by
    refine ⟨fun t => Six.row_lt _ _,fun t => ?_⟩
    have adv := Six.row_step (S+t) i
    refine ⟨mem_successors.mpr ⟨_,_,by simpa [x,Nat.add_assoc,Six.step] using adv⟩,
      (fits_iff _ _ _).mpr ?_⟩
    intro j on off
    by_cases hj : j < 6
    · rw [permit_bit, decide_eq_true_eq]
      refine ⟨hj,?_⟩
      have b : Fall (i+j) (S+t) := by
        unfold x at on off
        rw [Six.row_bit _ _ _ hj] at on off
        exact ⟨on,by simpa only [Nat.add_assoc] using off⟩
      have eq : (S+t)%m = (a ⟨j,hj⟩).val := by
        apply Classical.byContradiction
        intro neq
        exact no ⟨⟨j,hj⟩,S+t,by omega,b,neq⟩
      simpa only [S,phases,dite_eq_left hj,Nat.add_comm _ t,Nat.add_mul_mod_self_right] using eq.symm
    · have hn : (x t).testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Six.row_lt _ _)
          (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 6 ≤ j)))
      simp [hn] at on
  have phasesBound (j : Nat) (hj : j < 6) : phases j < m := by
    simpa only [phases,dite_eq_left hj] using (a ⟨j,hj⟩).isLt
  obtain ⟨j,N,hj,per⟩ := good phases phasesBound x run
  apply not_adjacent (i+j)
  · refine ⟨S+N,m,hm,fun t ht => ?_⟩
    have left := (pair_bits (per (t-S) (by omega))).1
    unfold x at left
    rw [Six.row_bit _ _ _ (by omega),Six.row_bit _ _ _ (by omega),
      show S+(t-S+m)=t+m by omega,show S+(t-S)=t by omega] at left
    exact left
  · refine ⟨S+N,m,hm,fun t ht => ?_⟩
    have right := (pair_bits (per (t-S) (by omega))).2
    unfold x at right
    rw [Six.row_bit _ _ _ hj,Six.row_bit _ _ _ hj,
      show S+(t-S+m)=t+m by omega,show S+(t-S)=t by omega] at right
    simpa only [Int.natCast_add,Int.natCast_one,← Int.add_assoc] using right

private theorem common_bound {k : Nat} (f : Fin k → Nat) :
    ∃ B, ∀ i, f i ≤ B := by
  induction k with
  | zero => exact ⟨0,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨B,upper⟩ := ih (fun i => f i.succ)
    exact ⟨max (f 0) B, fun i => Fin.cases (Nat.le_max_left _ _)
      (fun j => Nat.le_trans (upper j) (Nat.le_max_right _ _)) i⟩

/-- Cofinality follows once each fixed one-phase assignment has an exception
after every starting time. The witnesses are fixed for the chosen modulus. -/
theorem two_cofinal_from_good {m : Nat} (hm : 0 < m) (i : Int)
    (good : ∀ a, (∀ j, j < 6 → a j < m) → Good 6 m a) :
    ∃ (j : Fin 6) (r q : Fin m), r ≠ q ∧ Cofinal (i+j.val) r ∧ Cofinal (i+j.val) q := by
  classical
  apply Classical.byContradiction
  intro no
  have single (j : Fin 6) : ∃ r : Fin m, ∀ q, q ≠ r → ¬ Cofinal (i+j.val) q := by
    by_cases h : ∃ r : Fin m, Cofinal (i+j.val) r
    · obtain ⟨r,hr⟩ := h
      exact ⟨r,fun q neq hq => no ⟨j,r,q,Ne.symm neq,hr,hq⟩⟩
    · exact ⟨⟨0,hm⟩,fun q _ hq => h ⟨q,hq⟩⟩
  let phase (j : Fin 6) := Classical.choose (single j)
  have cutoff (j : Fin 6) (q : Fin m) :
      ∃ B, ∀ t, B ≤ t → t%m=q.val → Fall (i+j.val) t → q=phase j := by
    by_cases eq : q = phase j
    · exact ⟨0,fun _ _ _ _ => eq⟩
    · have rare := Classical.choose_spec (single j) q eq
      apply Classical.byContradiction
      intro noBound
      apply rare
      intro T
      apply Classical.byContradiction
      intro absent
      exact noBound ⟨T,fun t ht htq hit => (absent ⟨t,ht,htq,hit⟩).elim⟩
  let B (j : Fin 6) (q : Fin m) := Classical.choose (cutoff j q)
  let C (j : Fin 6) := Classical.choose (common_bound (B j))
  obtain ⟨M,hm'⟩ := common_bound C
  obtain ⟨j,t,late,hit,off⟩ := escape hm i phase good M
  let q : Fin m := ⟨t%m,Nat.mod_lt t hm⟩
  have hq : B j q ≤ C j := Classical.choose_spec (common_bound (B j)) q
  have eq := Classical.choose_spec (cutoff j q) t (Nat.le_trans hq (Nat.le_trans (hm' j) late)) rfl hit
  exact off (congrArg Fin.val eq)

end Ruliology.CellularAutomata.Rule30FallResidues

namespace Ruliology.CellularAutomata.Rule30FallResidues

private def parityRow (t : Nat) : Nat := [3,36,63,1].getD (t%4) 0

private def parityEdges : Bool := (List.range 4).all fun t =>
  parityRow t < 64 &&
  (successors 6 (parityRow t)).contains (parityRow (t+1)) &&
  fits (permit 6 (fun _ => 0) (t%2)) (parityRow t) (parityRow (t+1))

private theorem parityEdges_ok : parityEdges = true := by decide +kernel

private theorem parity_run : Run 6 2 (fun _ => 0) parityRow := by
  have verify (p : Nat) (hp : p < 4) :=
    List.all_eq_true.mp parityEdges_ok p (List.mem_range.mpr hp)
  have data (t : Nat) :=
    verify (t%4) (Nat.mod_lt _ (by decide))
  refine ⟨fun t => ?_,fun t => ?_⟩
  · have fact := data t
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fact
    simpa only [parityRow, Nat.mod_mod] using fact.1.1
  · have fact := data t
    simp only [Bool.and_eq_true, List.contains_iff_mem] at fact
    have here : parityRow (t%4) = parityRow t := by simp [parityRow]
    have next : parityRow (t%4+1) = parityRow (t+1) := by
      unfold parityRow
      rw [show (t%4+1)%4=(t+1)%4 by omega]
    have phase : t%4%2=t%2 := by omega
    exact ⟨by simpa only [here,next] using fact.1.2,
      by simpa only [here,next,phase] using fact.2⟩

private theorem parity_bad : (List.range 5).all (fun j =>
    (parityRow ((if j=0 then 1 else 0)+2) >>> j)%4 !=
      (parityRow (if j=0 then 1 else 0) >>> j)%4) = true := by decide +kernel

/-- The four-row loop is an admissible free-exterior strip whose falls all
start on even ticks. Every adjacent pair changes under the lag-two shift. -/
theorem not_good_parity : ¬ Good 6 2 (fun _ => 0) := by
  intro h
  obtain ⟨j,N,hj,per⟩ := h parityRow parity_run
  let r := if j=0 then 1 else 0
  have bad := List.all_eq_true.mp parity_bad j (List.mem_range.mpr (by omega))
  have eq := per (4*N+r) (by omega)
  have here : parityRow (4*N+r) = parityRow r := by
    unfold parityRow
    rw [show (4*N+r)%4=r%4 by omega]
  have next : parityRow (4*N+r+2) = parityRow (r+2) := by
    unfold parityRow
    rw [show (4*N+r+2)%4=(r+2)%4 by omega]
  rw [here,next] at eq
  change ((parityRow (r+2) >>> j)%4 != (parityRow r >>> j)%4) = true at bad
  simp [eq] at bad

end Ruliology.CellularAutomata.Rule30FallResidues

namespace Ruliology.CellularAutomata.Rule30FallResidues

private def checkedDivisor (m : Nat) : Prop :=
  3 ∣ m ∨ 4 ∣ m ∨ 5 ∣ m ∨ 7 ∣ m ∨ 11 ∣ m ∨ 13 ∣ m ∨ 17 ∣ m

private instance (m : Nat) : Decidable (checkedDivisor m) := by
  unfold checkedDivisor
  infer_instance

private theorem checkedDivisors :
    (List.range 19).all (fun m => decide (m < 3 ∨ checkedDivisor m)) = true := by decide +kernel

theorem good_small (m : Nat) (hm : 3 ≤ m) (hb : m ≤ 18) (a : Nat → Nat)
    (_ : Valid 6 m a) : Good 6 m a := by
  have h := of_decide_eq_true (List.all_eq_true.mp checkedDivisors m (List.mem_range.mpr (by omega)))
  rcases h with h | h
  · omega
  rcases h with h | h | h | h | h | h | h
  · exact good_of_dvd h (good3 fun j _ => Nat.mod_lt _ (by decide))
  · exact good_of_dvd h (good4 fun j _ => Nat.mod_lt _ (by decide))
  · exact good_of_dvd h (good5 fun j _ => Nat.mod_lt _ (by decide))
  · exact good_of_dvd h (good7 fun j _ => Nat.mod_lt _ (by decide))
  · exact good_of_dvd h (good11 fun j _ => Nat.mod_lt _ (by decide))
  · exact good_of_dvd h (good13 fun j _ => Nat.mod_lt _ (by decide))
  · exact good_of_dvd h (good17 fun j _ => Nat.mod_lt _ (by decide))

/-- For each modulus at least three, every six consecutive singleton Rule 30
columns contain a fixed column with cofinal falls on two distinct residues. -/
theorem two_cofinal_every_modulus (m : Nat) (hm : 3 ≤ m) (i : Int) :
    ∃ (j : Fin 6) (r q : Fin m), r ≠ q ∧ Cofinal (i+j.val) r ∧ Cofinal (i+j.val) q :=
  two_cofinal_from_good (by omega : 0 < m) i fun _ ha => good_of_small hm ha good_small

end Ruliology.CellularAutomata.Rule30FallResidues
