module

public import Ruliology.CellularAutomata.Rule30ControlledResponse
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# An eight-periodic infinite-tail obstruction to OR-only reconstruction

The two explicit right halves have identical nonconstant head/neighbor OR
observations and different head traces. Both full diagonal orbits have period
dividing eight. A third example has head period two and full-state least
period eight. None is finitely supported: these are not counterexamples
to the finite-tail conjectures and prove no prize result.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodicProfileCounter

open Rule30ControlledResponse

def key (k : Nat) : Nat := if k<4 then k else 4+(k-4)%4
def nextKey (i : Nat) : Nat := if i<7 then i+1 else 4

theorem key_lt (k : Nat) : key k<8 := by
  unfold key
  split <;> omega

theorem key_succ (k : Nat) : key (k+1)=nextKey (key k) := by
  unfold key nextKey
  split <;> split <;> split <;> omega

def profile (which : Bool) (i : Nat) : Nat :=
  (if which then [45,43,186,166,101,149,86,89]
   else [42,45,51,170,170,85,170,85]).getD i 0

def frame (which : Bool) (t k : Nat) : Bool := (profile which (key k)).testBit (t%8)
def initial (which : Bool) : State := frame which 0

theorem profile_step_table : ∀ which : Bool, ∀ t i : Fin 8,
    (profile which i.val).testBit ((t.val+1)%8)=
      xor ((profile which i.val).testBit t.val)
        ((profile which (nextKey i.val)).testBit t.val ||
         (profile which (nextKey (nextKey i.val))).testBit t.val) := by decide

theorem frame_step (which : Bool) (t : Nat) : diagonal (frame which t)=frame which (t+1) := by
  funext k
  have h := profile_step_table which ⟨t%8,Nat.mod_lt _ (by decide)⟩ ⟨key k,key_lt k⟩
  simpa only [diagonal,frame,key_succ,show k+2=(k+1)+1 by omega,
    show (t+1)%8=(t%8+1)%8 by omega] using h.symm

theorem iterate_frame (which : Bool) : ∀ t, iterate (initial which) t=frame which t
  | 0 => rfl
  | t+1 => by rw [iterate,iterate_frame,frame_step]

theorem full_period_eight (which : Bool) (t : Nat) :
    iterate (initial which) (t+8)=iterate (initial which) t := by
  rw [iterate_frame,iterate_frame]
  funext k
  simp [frame]

theorem same_OR_table : ∀ t : Fin 8,
    ((profile true 0).testBit t.val || (profile true 1).testBit t.val)=
    ((profile false 0).testBit t.val || (profile false 1).testBit t.val) := by decide

theorem same_OR (t : Nat) :
    (iterate (initial true) t 0 || iterate (initial true) t 1)=
    (iterate (initial false) t 0 || iterate (initial false) t 1) := by
  simpa only [iterate_frame,frame,key,show 0<4 by decide,show 1<4 by decide,
    ite_true] using same_OR_table ⟨t%8,Nat.mod_lt _ (by decide)⟩

theorem OR_nonconstant :
    (iterate (initial true) 0 0 || iterate (initial true) 0 1)=true ∧
    (iterate (initial true) 4 0 || iterate (initial true) 4 1)=false := by
  rw [iterate_frame,iterate_frame]
  decide

theorem heads_differ : initial true 0≠initial false 0 := by decide

theorem tail_OR_different :
    (iterate (initial true) 2 1 || iterate (initial true) 2 2)≠
    (iterate (initial false) 2 1 || iterate (initial false) 2 2) := by
  rw [iterate_frame,iterate_frame]
  decide

theorem infinite_true : ¬Rule30ZeroBoundary.FinSupp (initial true) := by
  rintro ⟨W,hW⟩
  have h := hW (4*(W+1)+4) (by omega)
  have hk : key (4*(W+1)+4)=4 := by
    unfold key
    rw [ite_eq_right (by omega)]
    omega
  change (profile true (key (4*(W+1)+4))).testBit 0=false at h
  rw [hk] at h
  contradiction

theorem infinite_false : ¬Rule30ZeroBoundary.FinSupp (initial false) := by
  rintro ⟨W,hW⟩
  have h := hW (4*(W+1)+5) (by omega)
  have hk : key (4*(W+1)+5)=5 := by
    unfold key
    rw [ite_eq_right (by omega)]
    omega
  change (profile false (key (4*(W+1)+5))).testBit 0=false at h
  rw [hk] at h
  contradiction

/-- A third infinite right half: the head has period two but its neighbor
and full diagonal state have least period eight. -/
def lossProfile (i : Nat) : Nat := [85,87,168,212,172,178,202,43].getD i 0
def lossFrame (t k : Nat) : Bool := (lossProfile (key k)).testBit (t%8)
def lossInitial : State := lossFrame 0

theorem loss_step_table : ∀ t i : Fin 8,
    (lossProfile i.val).testBit ((t.val+1)%8)=
      xor ((lossProfile i.val).testBit t.val)
        ((lossProfile (nextKey i.val)).testBit t.val ||
         (lossProfile (nextKey (nextKey i.val))).testBit t.val) := by decide

theorem loss_frame_step (t : Nat) : diagonal (lossFrame t)=lossFrame (t+1) := by
  funext k
  have h := loss_step_table ⟨t%8,Nat.mod_lt _ (by decide)⟩ ⟨key k,key_lt k⟩
  simpa only [diagonal,lossFrame,key_succ,show k+2=(k+1)+1 by omega,
    show (t+1)%8=(t%8+1)%8 by omega] using h.symm

theorem loss_iterate_frame : ∀ t, iterate lossInitial t=lossFrame t
  | 0 => rfl
  | t+1 => by rw [iterate,loss_iterate_frame,loss_frame_step]

theorem loss_full_period_eight (t : Nat) : iterate lossInitial (t+8)=iterate lossInitial t := by
  rw [loss_iterate_frame,loss_iterate_frame]
  funext k
  simp [lossFrame]

theorem loss_head_period_two (t : Nat) : iterate lossInitial (t+2) 0=iterate lossInitial t 0 := by
  have h : ∀ t : Fin 8, (lossProfile 0).testBit ((t.val+2)%8)=(lossProfile 0).testBit t.val := by decide
  simpa only [loss_iterate_frame,lossFrame,key,show 0<4 by decide,ite_true,
    show (t+2)%8=(t%8+2)%8 by omega] using h ⟨t%8,Nat.mod_lt _ (by decide)⟩

theorem loss_neighbor_short_table : ∀ P : Fin 8, 0<P.val → ∃ t : Fin 8,
    (lossProfile 1).testBit ((t.val+P.val)%8)≠(lossProfile 1).testBit t.val := by decide

theorem loss_full_period_lower_bound (P : Nat) (hP : 0<P)
    (hp : ∀ t, iterate lossInitial (t+P)=iterate lossInitial t) : 8≤P := by
  by_cases hbig : 8≤P
  · exact hbig
  · obtain ⟨t,ht⟩ := loss_neighbor_short_table ⟨P,by omega⟩ hP
    have h := congrFun (hp t.val) 1
    simp only [loss_iterate_frame,lossFrame,key,show 1<4 by decide,ite_true,
      Nat.mod_eq_of_lt t.isLt] at h
    exact False.elim (ht h)

theorem loss_not_head_period_one : ¬∀ t, iterate lossInitial (t+1) 0=iterate lossInitial t 0 := by
  intro h
  have hh := h 0
  rw [loss_iterate_frame,loss_iterate_frame] at hh
  contradiction

theorem loss_infinite : ¬Rule30ZeroBoundary.FinSupp lossInitial := by
  rintro ⟨W,hW⟩
  have h := hW (4*(W+1)+7) (by omega)
  have hk : key (4*(W+1)+7)=7 := by
    unfold key
    rw [ite_eq_right (by omega)]
    omega
  change (lossProfile (key (4*(W+1)+7))).testBit 0=false at h
  rw [hk] at h
  contradiction

/-! ## Multi-period temporal invariance (`8 * m`) and spatial period-`4` tail (`k ≥ 4`) for all three counterexamples -/

/-- **Multi-Period Temporal Invariance and Spatial Period-`4` Tail (`k ≥ 4`) for `initial` and `lossInitial` (`counterexamples_temporal_and_spatial_periods`).** -/
theorem counterexamples_temporal_and_spatial_periods (which : Bool) (t m k : Nat) (hk : 4 ≤ k) :
    iterate (initial which) (t + m * 8) = iterate (initial which) t ∧
    iterate lossInitial (t + m * 8) = iterate lossInitial t ∧
    iterate (initial which) t (k + 4) = iterate (initial which) t k ∧
    iterate lossInitial t (k + 4) = iterate lossInitial t k := by
  have hkey : key (k + 4) = key k := by
    unfold key
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hm : (k + 4 - 4) % 4 = (k - 4) % 4 := by
      rw [show k + 4 - 4 = (k - 4) + 4 by omega, Nat.add_mod_right]
    rw [hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · induction m with
    | zero => simp
    | succ m ih =>
      rw [show t + (m + 1) * 8 = (t + m * 8) + 8 by rw [Nat.succ_mul]; omega,
          full_period_eight, ih]
  · induction m with
    | zero => simp
    | succ m ih =>
      rw [show t + (m + 1) * 8 = (t + m * 8) + 8 by rw [Nat.succ_mul]; omega,
          loss_full_period_eight, ih]
  · rw [iterate_frame]
    unfold frame
    rw [hkey]
  · rw [loss_iterate_frame]
    unfold lossFrame
    rw [hkey]

end Ruliology.CellularAutomata.Rule30PeriodicProfileCounter
