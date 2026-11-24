module

public import Ruliology.CellularAutomata.Rule30LightCone
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30MarkedGaps
public import Ruliology.CellularAutomata.Rule30Window

/-!
# Center factors matching a different singleton column from its start

Under a proposed center period there is a single finite bound on the
length of every such match, across all starting ages and all nonzero
columns. A late black bounds the column's distance; Jen then supplies a
period violation in each of the finitely many remaining columns.
An expanding window that is white except for a possible off-center
singleton would give these matches by finite propagation. Existence of
arbitrarily long matches or of such windows is open.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30OffCenterEcho
open Rule30Jen Rule30Realization Rule30Diagonals

def Echo (s : Nat) (j : Int) (n : Nat) : Prop :=
  ∀ k, k≤n → cell (s+k) 0 = cell k j

theorem echo_bound {T P : Nat} (pos : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0) :
    ∃ n, ∀ s j, j≠0 → ¬Echo s j n := by
  have black : ∃ b, T≤b ∧ cell b 0=true := by
    apply Classical.byContradiction
    intro none
    apply Rule30Prize.center_not_eventually_constant
    refine ⟨T,false,fun t late => ?_⟩
    cases h : cell t 0 with
    | false => exact h
    | true => exact (none ⟨t,late,h⟩).elim
  obtain ⟨b,hb,on⟩ := black
  have escape (j : Int) (nz : j≠0) : ∃ t, T≤t ∧ cell (t+P) j≠cell t j := by
    apply Classical.byContradiction
    intro no
    apply (jen j 0 nz)
    exact ⟨⟨T,P,pos,fun t ht => Classical.byContradiction (fun h => no ⟨t,ht,h⟩)⟩,⟨T,P,pos,per⟩⟩
  have bound (m : Nat) : ∃ B, ∀ j : Int, j≠0 → -(m:Int)≤j → j≤m →
      ∃ t, T≤t ∧ t≤B ∧ cell (t+P) j≠cell t j := by
    induction m with
    | zero => exact ⟨0,by omega⟩
    | succ m ih =>
      obtain ⟨B,h⟩ := ih
      obtain ⟨a,ha,da⟩ := escape (-((m+1:Nat):Int)) (by omega)
      obtain ⟨d,hd,dd⟩ := escape ((m+1:Nat):Int) (by omega)
      refine ⟨B+a+d,fun j nz lo hi => ?_⟩
      by_cases left : j = -((m+1:Nat):Int)
      · exact ⟨a,ha,by omega,left ▸ da⟩
      by_cases right : j = ((m+1:Nat):Int)
      · exact ⟨d,hd,by omega,right ▸ dd⟩
      obtain ⟨t,late,small,bad⟩ := h j nz (by omega) (by omega)
      exact ⟨t,late,by omega,bad⟩
  obtain ⟨B,bad⟩ := bound (b+P)
  refine ⟨B+b+2*P, fun s j nz copy => ?_⟩
  let k := b+(P-s%P)
  have r := Nat.mod_lt s pos
  have cut := Nat.mod_add_div s P
  have atBlack := periodic_mul (f:=fun u => cell u 0) per (s/P+1) b hb
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (s/P) P] at atBlack
  have align : s+k = b+(P*(s/P)+P) := by dsimp [k]; omega
  have known : cell k j = true :=
    (copy k (by dsimp [k]; omega)).symm.trans (align ▸ atBlack.trans on)
  have lo : -((b+P:Nat):Int)≤j := by
    by_cases h : j < -(k:Int)
    · exact (by rw [cell_eq_false_of_lt _ _ h] at known; contradiction)
    · dsimp [k] at h; omega
  have hi : j≤((b+P:Nat):Int) := by
    by_cases h : (k:Int)<j
    · exact (by rw [cell_eq_false_of_gt _ _ h] at known; contradiction)
    · dsimp [k] at h; omega
  obtain ⟨t,late,small,neq⟩ := bad j nz lo hi
  apply neq
  rw [← copy (t+P) (by omega),← copy t (by omega),← Nat.add_assoc,per _ (by omega)]

theorem problem1_of_echo (h : ∀ n, ∃ s j, j≠0 ∧ Echo s j n) : Rule30Prize.Problem1 := by
  rintro ⟨T,P,pos,per⟩
  obtain ⟨n,forbid⟩ := echo_bound pos per
  obtain ⟨s,j,nz,copy⟩ := h n
  exact forbid s j nz copy

/-- A white window or one with its sole black away from the center is enough.
The position may vary with the radius and may lie outside the window. -/
theorem problem1_of_sparse_white_center
    (h : ∀ n : Nat, ∃ s : Nat, ∃ j : Int, j≠0 ∧
      ∀ q : Int, -(n:Int)≤q → q≤n → cell s q = decide (q=j)) : Rule30Prize.Problem1 := by
  apply problem1_of_echo
  intro n
  obtain ⟨s,j,nz,w⟩ := h n
  refine ⟨s,-j,by omega,fun k hk => ?_⟩
  have later := Rule30ZeroBoundaryBarriers.evol_restart seed s k 0
  simp only [evol_seed] at later
  rw [← later]
  let point := fun p : Int => decide (p=j)
  have cone : evol (fun q => cell s q) k 0 = evol point k 0 :=
    Rule30LightCone.evol_window (fun q lo hi => w q (by omega) (by omega))
  rw [cone]
  have shift := Rule30ZeroBoundaryBarriers.evol_shift_all (x:=seed) (x':=point) (d:=j)
    (fun q => by simp [point,seed,show q+j=j ↔ q=0 by omega]) k (-j)
  simpa [evol_seed,show -j+j=0 by omega] using shift

/-- A guaranteed right boundary of agreement. At a black boundary the
unknown right neighbor is masked for one tick. At a white boundary we
move the guarantee one site left. -/
def fence (a : Nat) (j b : Int) : Nat → Int
  | 0 => b
  | t+1 =>
    let q := fence a j b t
    if cell (a+t) (q+j) then q else q-1

/-- The left endpoint moves at full speed. The right endpoint follows
the colors along the reference history, so the initial agreement
interval may be much shorter on the right. -/
theorem guarded_window (x : Int → Bool) (a : Nat) (j lo hi : Int)
    (initial : ∀ q : Int, lo≤q → q≤hi → x q=cell a (q+j)) (t : Nat) :
    ∀ q : Int, lo+t≤q → q≤fence a j hi t → evol x t q=cell (a+t) (q+j) := by
  induction t with
  | zero => simpa [fence,evol] using initial
  | succ t ih =>
    intro q left right
    let b := fence a j hi t
    have step : fence a j hi (t+1) = (if cell (a+t) (b+j) then b else b-1) := rfl
    rw [step] at right
    have le : q≤b := by split at right <;> omega
    have l := ih (q-1) (by omega) (by change q-1≤b; omega)
    have m := ih q (by omega) le
    change rule (evol x t (q-1)) (evol x t q) (evol x t (q+1)) =
      rule (cell (a+t) (q+j-1)) (cell (a+t) (q+j)) (cell (a+t) (q+j+1))
    rw [l,m,show q-1+j=q+j-1 by omega]
    by_cases inside : q<b
    · rw [ih (q+1) (by omega) (by change q+1≤b; omega),show q+1+j=q+j+1 by omega]
    · have eq : q=b := by omega
      have on : cell (a+t) (q+j)=true := by
        subst q
        cases h : cell (a+t) (b+j) with
        | false => simp [h] at right; omega
        | true => rfl
      simp [rule,on]

private theorem fence_step_le (a : Nat) (j hi : Int) (t : Nat) :
    fence a j hi (t+1) ≤ fence a j hi t := by
  simp only [fence]
  split <;> omega

/-- A fixed right endpoint only buys a finite amount of time by this
argument. If it never moved again, one fixed singleton column would
stay black forever, contrary to the kit's no-constant-column theorem. -/
theorem fence_eventually_below (a : Nat) (j hi z : Int) :
    ∃ T, ∀ t, T≤t → fence a j hi t < z := by
  have mono (s t : Nat) (hst : s≤t) : fence a j hi t ≤ fence a j hi s := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hst
    induction d with
    | zero => exact Int.le_refl _
    | succ d ih => exact Int.le_trans (fence_step_le a j hi (s+d)) (ih (by omega))
  have drop (s : Nat) : ∃ t, s≤t ∧ fence a j hi t < fence a j hi s := by
    apply Classical.byContradiction
    intro none
    have same (t : Nat) (ht : s≤t) : fence a j hi t = fence a j hi s := by
      have m := mono s t ht
      exact Int.le_antisymm m (Int.not_lt.mp (fun h => none ⟨t,ht,h⟩))
    apply Rule30Prize.no_column_eventually_constant (fence a j hi s+j)
    refine ⟨a+s,true,fun u hu => ?_⟩
    let t := u-a
    have st : s≤t := by dsimp [t]; omega
    have eq := same (t+1) (by omega)
    rw [fence,same t st,show a+t=u by dsimp [t]; omega] at eq
    cases h : cell u (fence a j hi s+j) with
    | true => rfl
    | false => simp [h] at eq <;> omega
  have falls (d : Nat) : ∃ t, fence a j hi t ≤ hi-d := by
    induction d with
    | zero => exact ⟨0,by simp [fence]⟩
    | succ d ih =>
      obtain ⟨s,le⟩ := ih
      obtain ⟨t,_,lt⟩ := drop s
      exact ⟨t,by omega⟩
  obtain ⟨T,h⟩ := falls (hi-z+1).toNat
  exact ⟨T,fun t ht => by have := mono T t ht; omega⟩

/-- A finite patch from the age-one row of the seed shifted one place
right forces the next 18 center observations, for every completion.
Only eight positive sites are inspected. -/
theorem eighteen_readings (x : Int → Bool)
    (patch : ∀ q : Int, -17≤q → q≤8 → x q=cell 1 (q-1)) :
    ∀ t : Fin 18, evol x t.val 0 = cell (1+t.val) (-1) := by
  have checked : ∀ t : Fin 18, 0 ≤ fence 1 (-1) 8 t.val := by decide +kernel
  intro t
  have e := guarded_window x 1 (-1) (-17) 8 (fun q l h => patch q l h) t.val 0
    (by have := t.isLt; omega) (checked t)
  exact e

/-! ### A singleton witness and the end of its match -/

open Rule30Window (row stepRow row_testBit)

-- Evaluate a long orbit tail-recursively and retain only the local snapshot.
private def march : Nat → Nat → Nat
  | 0, r => r
  | n+1, r =>
    let z := stepRow r
    if Nat.ble 0 z then march n z else 0

private theorem march_row (K n t : Nat) : march n (row K t) = row K (t+n) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [march,Nat.ble_eq_true_of_le (Nat.zero_le _)]
    simpa [row,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

-- Bits 0 through 50 represent positions -25 through 25 at tick 34428.
private def shortRow : Nat → Nat
  | 0 => 1919669892022269
  | n+1 => stepRow (shortRow n)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem snapshot :
    ((march 34428 (2^34428)) >>> (34428-25)) % 2^51 = shortRow 0 := by decide +kernel

set_option exponentiation.threshold 35000 in
private theorem shortRow_bit (t i : Nat) (lo : t≤i) (hi : i+t≤50) :
    (shortRow t).testBit i = cell (34428+t) ((i:Int)-25) := by
  induction t generalizing i with
  | zero =>
    have h := snapshot
    rw [show 2^34428 = row 34428 0 from rfl,march_row] at h
    rw [← h,Nat.testBit_mod_two_pow,decide_eq_true (by omega : i<51),Bool.true_and,
      Nat.testBit_shiftRight,row_testBit _ _ (by decide)]
    exact Rule30Window.cell_congr' (by omega)
  | succ t ih =>
    have pos : 1≤i := by omega
    have l := ih (i-1) (by omega) (by omega)
    have m := ih i (by omega) (by omega)
    have r := ih (1+i) (by omega) (by omega)
    rw [shortRow,stepRow,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight,decide_eq_true pos,Bool.true_and,l,m,r]
    rw [show ((i-1:Nat):Int)-25=(i:Int)-25-1 by omega,
      show ((1+i:Nat):Int)-25=(i:Int)-25+1 by omega]
    rfl

private theorem short_restriction (q : Int) (lo : -17≤q) (hi : q≤8) :
    cell 34429 q = cell 1 (q-1) := by
  let i : Fin 26 := ⟨(q+17).toNat,by omega⟩
  have e : ((i.val+8:Nat):Int)-25=q := by dsimp [i]; omega
  have bit := shortRow_bit 1 (i.val+8) (by omega) (by have := i.isLt; omega)
  have all : ∀ j : Fin 26, (shortRow 1).testBit (j.val+8) = cell 1 ((j.val:Int)-18) := by decide +kernel
  rw [← e,← bit]
  exact (all i).trans (by congr 1; omega)

/-- At age 34428 the actual singleton center begins a 19-tick match
with the initial column at -1. The following tick breaks the match.
One tick into the match there is a marked gap of length 22. -/
theorem singleton_mark_and_echo :
    Rule30MarkedGaps.Mark 34429 22 ∧ Echo 34428 (-1) 18 ∧ ¬ Echo 34428 (-1) 19 := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro q lo hi
      let i : Fin 22 := ⟨(q+22).toNat,by omega⟩
      have e : ((i.val+3:Nat):Int)-25=q := by dsimp [i]; omega
      have bit := shortRow_bit 1 (i.val+3) (by omega) (by have := i.isLt; omega)
      have whites : ∀ j : Fin 22, (shortRow 1).testBit (j.val+3)=false := by decide +kernel
      rw [← e,← bit]
      exact whites i
    · exact (shortRow_bit 1 2 (by decide) (by decide)).symm.trans (by decide +kernel)
    · exact (shortRow_bit 23 25 (by decide) (by decide)).symm.trans (by decide +kernel)
  constructor
  · intro k hk
    cases k with
    | zero => exact (shortRow_bit 0 25 (by decide) (by decide)).symm.trans (by decide +kernel)
    | succ k =>
      let i : Fin 18 := ⟨k,by omega⟩
      have obs := eighteen_readings (cell 34429) short_restriction i
      have restart := Rule30ZeroBoundaryBarriers.evol_restart seed 34429 k 0
      simp only [evol_seed] at restart
      rw [restart] at obs
      simpa [i,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using obs
  · intro copy
    have h := copy 19 (by decide)
    have bit := shortRow_bit 19 25 (by decide) (by decide)
    have early := row_testBit 19 19 (by decide) 18
    have late : (shortRow 19).testBit 25 ≠ (row 19 19).testBit 18 := by decide +kernel
    exact late (bit.trans (h.trans early.symm))

end Ruliology.CellularAutomata.Rule30OffCenterEcho
