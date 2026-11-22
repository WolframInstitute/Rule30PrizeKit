module

public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# What the right half determines at age twice the support radius

At time `h` a full right half determines the starting row if the latter
was supported in `[-h,h]`. The first bit beyond the allowed left boundary
measures exactly the next center discrepancy.

Shortening the observation to a growing strip can leave the next center bit
undetermined. Two finite rows of radius `336*q+97` enter a common alternating
pattern on that strip. Both carry genuine singleton edge data. The proof tracks
two spatially 28-periodic reference rows up to a moving cutoff. A black cell
at the cutoff masks the unknown neighbor on its right. Cutting off the left
end produces a discrepancy that moves at unit speed and eventually reaches
the center. The starting rows need only have the stated edge data.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30HalfAgeOrigin
open Rule30Jen Rule30Realization

private abbrev Phase := Fin 60
private abbrev State := Phase × Int

-- States 0–27 and 28–55 are the two transients. States 56–59 form their common cycle.
private def code (v : Phase) :=
  #[
    264086941, 8699108, 30377790, 40946115, 261717605, 15664060, 18973830,
    66244555, 203321465, 102996110, 192212435, 152511580, 263323335, 10093160,
    32180140, 36276390, 124706235, 19022985, 200798175, 135274560, 205025505,
    105683250, 200798175, 135274560, 205025505, 105683250, 200798175, 135274560,
    230553614, 75762706, 265164351, 7549760, 10345824, 31737136, 37678552,
    121775180, 157777654, 255394322, 30377790, 40946115, 261717605, 15664060,
    18973830, 66244555, 203321465, 102996110, 192212435, 152511580, 263323335,
    10093160, 32180140, 36276390, 124706235, 19022985, 200798175, 135274560,
    205025505, 105683250, 200798175, 135274560][v.val]!

private def next (v : Phase) : Phase :=
  if h : v.val=27 ∨ v.val=55 ∨ v.val=59 then 56 else ⟨v.val+1, by omega⟩

private def pix (v : Phase) (p : Int) := (code v).testBit (p % 28).toNat

private theorem pix_congr (v : Phase) {i j : Int} (h : i % 28 = j % 28) :
    pix v i = pix v j := by simp only [pix, h]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 4000000 in
private theorem ring (v : Phase) (p : Int) :
    pix (next v) p = rule (pix v (p-1)) (pix v p) (pix v (p+1)) := by
  have finite : ∀ z : Phase, ∀ k : Fin 28,
      pix (next z) (k.val : Int) =
        rule (pix z ((k.val : Int)-1)) (pix z k.val) (pix z ((k.val : Int)+1)) := by decide +kernel
  let k : Fin 28 := ⟨(p%28).toNat, by omega⟩
  have hk : (k.val : Int) = p%28 := by dsimp [k]; omega
  have h0 : p % 28 = (k.val : Int) % 28 := by omega
  rw [pix_congr (next v) h0, pix_congr v (i := p-1) (j := (k.val : Int)-1) (by omega),
    pix_congr v h0, pix_congr v (i := p+1) (j := (k.val : Int)+1) (by omega)]
  exact finite v k

-- The second component is the exclusive safe cutoff relative to the graft point.
private def tick (s : State) : State :=
  (next s.1, if pix s.1 (s.2-1) then s.2 else s.2-1)

private def advance (s : State) : Nat → State
  | 0 => s
  | t+1 => tick (advance s t)

private theorem advance_add (s : State) (a b : Nat) :
    advance s (a+b) = advance (advance s a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg tick ih

private def move (s : State) (k : Int) : State := (s.1, s.2+28*k)

private theorem advance_move (s : State) (k : Int) (t : Nat) :
    advance (move s k) t = move (advance s t) k := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [advance, ih]
    generalize advance s t = z
    unfold tick move
    simp only
    rw [pix_congr z.1 (i := z.2+28*k-1) (j := z.2-1) (by omega)]
    cases pix z.1 (z.2-1) <;> simp <;> omega

def radius (q : Nat) := 336*q+97
def cut (q : Nat) : Int := 308*(q : Int)+84

set_option maxRecDepth 60000 in
set_option maxHeartbeats 4000000 in
private theorem sweep :
    advance (0,1) 98 = (58,-56) ∧ advance (28,1) 98 = (58,-57) ∧
    advance (58,-56) 336 = (58,-252) ∧ advance (58,-57) 336 = (58,-253) := by decide +kernel

private theorem blocks (q : Nat) :
    advance (0,1) (radius q+1) = move (58,-56) (-7*(q : Int)) ∧
    advance (28,1) (radius q+1) = move (58,-57) (-7*(q : Int)) := by
  induction q with
  | zero => exact ⟨sweep.1,sweep.2.1⟩
  | succ q ih =>
    rw [show radius (q+1)+1 = (radius q+1)+336 by unfold radius; omega,
        advance_add, advance_add (28,1), ih.1, ih.2,
        advance_move, advance_move, sweep.2.2.1, sweep.2.2.2]
    constructor <;> apply Prod.ext <;> simp [move] <;> omega

private theorem decreasing (s : State) {a b : Nat} (h : a ≤ b) :
    (advance s b).2 ≤ (advance s a).2 := by
  induction b with
  | zero =>
    have hh : a=0 := by omega
    subst a
    exact Int.le_refl _
  | succ b ih =>
    by_cases e : a=b+1
    · subst a; omega
    · have hh := ih (by omega)
      simp only [advance, tick]
      split <;> omega

private def rightCut (q : Nat) (v : Phase) (j : Int) : Bool :=
  if j ≤ cut q then pix v j else cell (radius q) j

private def leftCut (lo : Int) (x : Int → Bool) (j : Int) : Bool :=
  if lo ≤ j then x j else false

private theorem right_safe (q : Nat) (v : Phase) (t : Nat) :
    ∀ j : Int, j < cut q+(advance (v,1) t).2 →
      evol (rightCut q v) t j = pix (advance (v,1) t).1 j := by
  induction t with
  | zero =>
    intro j hj
    simp only [advance] at hj
    simp [evol, advance, rightCut, show j ≤ cut q by omega]
  | succ t ih =>
    intro j hj
    let s := advance (v,1) t
    change j < cut q+(if pix s.1 (s.2-1) then s.2 else s.2-1) at hj
    change rule _ _ _ = pix (next s.1) j
    have le : j < cut q+s.2 := by split at hj <;> omega
    rw [ring, ih (j-1) (by change j-1 < cut q+s.2; omega), ih j le]
    by_cases safe : j+1 < cut q+s.2
    · rw [ih (j+1) safe]
    · have edge : pix s.1 (s.2-1) = true := by
        cases e : pix s.1 (s.2-1) <;> simp [e] at hj ⊢ <;> omega
      unfold cut at *
      have mask : pix s.1 j = true :=
        (pix_congr _ (i := j) (j := s.2-1) (by omega)).trans edge
      change rule (pix s.1 (j-1)) (pix s.1 j) _ = rule (pix s.1 (j-1)) (pix s.1 j) _
      simp [rule, mask]

private theorem left_safe (lo : Int) (x : Int → Bool) (t : Nat) :
    (∀ j : Int, lo+t ≤ j → evol (leftCut lo x) t j = evol x t j) ∧
    evol (leftCut lo x) t (lo+t-1) = xor (evol x t (lo+t-1)) (x (lo-1)) := by
  induction t with
  | zero => simp [evol, leftCut]; constructor <;> intros <;> omega
  | succ t ih =>
    constructor
    · intro j hj
      change rule _ _ _ = rule _ _ _
      rw [ih.1 (j-1) (by omega), ih.1 j (by omega), ih.1 (j+1) (by omega)]
    · rw [show lo+((t+1 : Nat) : Int)-1=lo+t by omega]
      simp only [evol]
      rw [ih.2, ih.1 (lo+t) (by omega), ih.1 (lo+t+1) (by omega)]
      simp only [rule]
      rw [Bool.xor_assoc, Bool.xor_comm (x (lo-1)), ← Bool.xor_assoc]

private def normal (t : Nat) : Phase := ⟨t%4+56, by omega⟩

private theorem normal_step (t : Nat) : next (normal t) = normal (t+1) := by
  have table : ∀ k : Fin 4, next (normal k.val) = normal (k.val+1) := by decide
  let k : Fin 4 := ⟨t%4, by omega⟩
  have h0 : normal t = normal k.val := by apply Fin.ext; dsimp [normal,k]; omega
  have h1 : normal (t+1) = normal (k.val+1) := by apply Fin.ext; dsimp [normal,k]; omega
  rw [h0, h1, table k]

private theorem phase_at {v : Phase} (hv : v = 0 ∨ v = 28) (t : Nat) (ht : 28 ≤ t) :
    (advance (v,1) t).1 = normal t := by
  obtain ⟨k, hk⟩ : ∃ k, t = 28+k := ⟨t-28, by omega⟩
  subst t
  induction k with
  | zero => rcases hv with rfl | rfl <;> decide
  | succ k ih =>
    change next (advance (v,1) (28+k)).1 = normal (28+k+1)
    rw [ih (by omega), normal_step]

private theorem normal_center (t : Nat) : pix (normal t) 0 = decide (t%2=0) := by
  have table : ∀ k : Fin 4, pix (normal k.val) 0 = decide (k.val%2=0) := by decide
  let k : Fin 4 := ⟨t%4, by omega⟩
  have he : normal t = normal k.val := by apply Fin.ext; dsimp [normal,k]; omega
  have h2 : k.val%2=t%2 := by dsimp [k]; omega
  rw [he, table k, h2]

private theorem width {v : Phase} (hv : v = 0 ∨ v = 28) {q t : Nat}
    (ht : t ≤ radius q+1) : 112*(q : Int)+26 < cut q+(advance (v,1) t).2 := by
  have endBound := decreasing (v,1) ht
  rcases hv with rfl | rfl
  · rw [(blocks q).1] at endBound
    simp only [move] at endBound
    unfold cut; omega
  · rw [(blocks q).2] at endBound
    simp only [move] at endBound
    unfold cut; omega

private theorem reference {v : Phase} (hv : v = 0 ∨ v = 28) {q t : Nat}
    (ht : 28 ≤ t) (ht' : t ≤ radius q+1) {j : Int} (hj : j ≤ 112*(q : Int)+26) :
    evol (rightCut q v) t j = pix (normal t) j :=
  (right_safe q v t j (by have := width hv ht'; omega)).trans (by rw [phase_at hv t ht])

private def start (q : Nat) (v : Phase) := leftCut (-((radius q : Nat) : Int)) (rightCut q v)

/-- Start at radius 336q+97. Copy the actual singleton's outermost 28q+13 cells
on the right and use the indicated 28-bit ring in the interior. -/
def crop (q word : Nat) (j : Int) : Bool :=
  if -((radius q : Nat) : Int) ≤ j then
    if j ≤ cut q then word.testBit (j % 28).toNat else cell (radius q) j
  else false

def rowA (q : Nat) := crop q 264086941
def rowB (q : Nat) := crop q 230553614

def Endpoints (r : Int → Bool) (h : Nat) : Prop :=
  r (-(h : Int)) = true ∧ r h = true ∧ ∀ j, j < -(h : Int) ∨ (h : Int) < j → r j = false

private theorem recover_suffix (h : Nat) (x y : Int → Bool) (upper : Int)
    (tail : ∀ j : Int, upper < j → x j = y j)
    (right : ∀ j : Int, 0 ≤ j → evol x h j = evol y h j) :
    ∀ j : Int, -(h : Int) ≤ j → x j = y j := by
  have down (k : Nat) : ∀ j : Int, upper+1-k ≤ j → -(h : Int) ≤ j → x j = y j := by
    induction k with
    | zero =>
      intro j hj _
      exact tail j (by omega)
    | succ k ih =>
      intro j hj lo
      by_cases old : upper+1-k ≤ j
      · exact ih j old lo
      · have eqCut : leftCut (j+1) x = leftCut (j+1) y := by
          funext p
          unfold leftCut
          split
          · exact ih p (by omega) (by omega)
          · rfl
        have f := (left_safe (j+1) x h).2
        rw [eqCut, (left_safe (j+1) y h).2,
          show j+1+(h : Int)-1=j+h by omega, right (j+h) (by omega),
          show j+1-1=j by omega] at f
        cases evol y h (j+h) <;> simpa using f.symm
  intro j hj
  exact down (upper+1-j).toNat j (by omega) hj

/-- If two initial configurations agree sufficiently far right and their entire
right halves agree after h ticks, their first exterior bits at -h-1 differ
exactly when their next center bits differ. -/
theorem first_exterior_discrepancy (h : Nat) (x y : Int → Bool) (upper : Int)
    (tail : ∀ j : Int, upper < j → x j = y j)
    (right : ∀ j : Int, 0 ≤ j → evol x h j = evol y h j) :
    xor (x (-(h : Int)-1)) (y (-(h : Int)-1)) =
      xor (evol x (h+1) 0) (evol y (h+1) 0) := by
  have common := recover_suffix h x y upper tail right
  have cuts : leftCut (-(h : Int)) x = leftCut (-(h : Int)) y := by
    funext j
    unfold leftCut
    split
    · exact common j (by omega)
    · rfl
  have eq := (left_safe (-(h : Int)) x (h+1)).2
  rw [cuts, (left_safe (-(h : Int)) y (h+1)).2,
    show -(h : Int)+((h+1 : Nat) : Int)-1 = 0 by omega] at eq
  have exchange (a b c d : Bool) (e : xor d b = xor c a) : xor a b = xor c d := by
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all
  exact exchange _ _ _ _ eq

/-- With the whole right half observed, an h-step past supported in [-h,h]
is uniquely determined. The two endpoint colors themselves are unnecessary. -/
theorem whole_right_determines (h : Nat) (x y : Int → Bool)
    (xz : ∀ j : Int, j < -(h : Int) ∨ (h : Int) < j → x j = false)
    (yz : ∀ j : Int, j < -(h : Int) ∨ (h : Int) < j → y j = false)
    (right : ∀ j : Int, 0 ≤ j → evol x h j = evol y h j) : x = y := by
  have tail (j : Int) (hj : (h : Int) < j) : x j = y j :=
    (xz j (Or.inr hj)).trans (yz j (Or.inr hj)).symm
  funext j
  by_cases lo : j < -(h : Int)
  · rw [xz j (Or.inl lo), yz j (Or.inl lo)]
  · exact recover_suffix h x y h tail right j (by omega)

theorem endpoints_evolve {x : Int → Bool} {h : Nat} (e : Endpoints x h) (t : Nat) :
    Endpoints (evol x t) (h+t) := by
  induction t with
  | zero => exact e
  | succ t ih =>
    obtain ⟨l, r, z⟩ := ih
    constructor
    · change rule _ _ _ = true
      rw [show -((h+(t+1) : Nat) : Int)+1 = -((h+t : Nat) : Int) by omega, l,
        z _ (Or.inl (by omega)), z _ (Or.inl (by omega))]
      decide
    constructor
    · change rule _ _ _ = true
      rw [show ((h+(t+1) : Nat) : Int)-1 = ((h+t : Nat) : Int) by omega, r,
        z _ (Or.inr (by omega)), z _ (Or.inr (by omega))]
      decide
    · intro j hj
      change rule _ _ _ = false
      rw [z (j-1) (by omega), z j (by omega), z (j+1) (by omega)]
      decide

private theorem endpoints_aux {v : Phase} (hv : v=0 ∨ v=28) (q : Nat) :
    Endpoints (start q v) (radius q) := by
  have on : pix v 15 = true := by rcases hv with rfl | rfl <;> decide
  have a := (pix_congr v (i := -((radius q : Nat) : Int)) (j := 15)
    (by unfold radius; omega)).trans on
  have b := Rule30Diagonals.R_zero (radius q)
  simp [Rule30Diagonals.R] at b
  have hcut : cut q < (radius q : Int) := by unfold cut radius; omega
  have hleft : -((radius q : Nat) : Int) ≤ cut q := by unfold cut radius; omega
  unfold Endpoints start leftCut rightCut
  constructor
  · simp [a,hleft]
  constructor
  · simp [show -((radius q : Nat) : Int) ≤ (radius q : Int) by omega,
      show ¬ (radius q : Int) ≤ cut q by omega,b]
  · intro j hj
    rcases hj with h | h
    · rw [ite_eq_right (by omega)]
    · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
      exact Rule30Diagonals.cell_eq_false_of_gt _ _ h

/-- The grafted right-edge band agrees with the actual singleton at the
same age at every later tick, for both words and arbitrary interior words. -/
theorem genuine_right_edge (q word t : Nat) : ∀ j : Int, cut q+t < j →
    evol (crop q word) t j = cell (radius q+t) j := by
  induction t with
  | zero =>
    intro j hj
    simp [crop, evol, show -((radius q : Nat) : Int) ≤ j by unfold radius cut at *; omega, show ¬ j ≤ cut q by omega]
  | succ t ih =>
    intro j hj
    change rule _ _ _ = rule _ _ _
    rw [ih (j-1) (by omega), ih j (by omega), ih (j+1) (by omega)]
    rfl

private theorem strip {v : Phase} (hv : v=0 ∨ v=28) {q t : Nat}
    (ht : 28≤t) (hh : t≤radius q) {j : Int} (lo : 0≤j) (hi : j≤112*(q : Int)+26) :
    evol (start q v) t j = pix (normal t) j := by
  rw [start, (left_safe _ _ t).1 j (by omega)]
  exact reference hv ht (by omega) hi

private theorem exit_cell {v : Phase} (hv : v=0 ∨ v=28) (q : Nat) :
    evol (start q v) (radius q+1) 0 = !pix v 14 := by
  have f := (left_safe (-((radius q : Nat) : Int)) (rightCut q v) (radius q+1)).2
  rw [show -((radius q : Nat) : Int)+((radius q+1 : Nat) : Int)-1=0 by omega,
    reference hv (by unfold radius; omega) (by omega) (by omega), normal_center] at f
  have even : (radius q+1)%2=0 := by unfold radius; omega
  have tail : rightCut q v (-((radius q : Nat) : Int)-1) = pix v 14 := by
    unfold rightCut
    rw [ite_eq_left (by unfold radius cut; omega)]
    exact pix_congr v (by unfold radius; omega)
  simp only [tail, even, decide_true, Bool.true_xor] at f
  exact f

/-- In two histories with initial support endpoints ±(336q+97), the
center alternates from tick 28 through tick 336q+97. The histories agree
there on columns 0 through 112q+26, then have opposite next center bits. -/
theorem half_age_pair (q : Nat) :
    (∀ t, 28≤t → t≤336*q+97 →
      evol (rowA q) t 0 = decide (t%2=0) ∧
      ∀ j : Int, 0≤j → j≤112*(q : Int)+26 →
        evol (rowA q) t j = evol (rowB q) t j) ∧
    evol (rowA q) (336*q+98) 0 = true ∧
    evol (rowB q) (336*q+98) 0 = false := by
  refine ⟨?_, (exit_cell (Or.inl rfl) q).trans (by decide),
    (exit_cell (Or.inr rfl) q).trans (by decide)⟩
  intro t ht hh
  refine ⟨(strip (Or.inl rfl) ht hh (by omega) (by omega)).trans (normal_center t), ?_⟩
  intro j lo hi
  exact (strip (Or.inl rfl) ht hh lo hi).trans (strip (Or.inr rfl) ht hh lo hi).symm

theorem initial_endpoints (q : Nat) :
    Endpoints (rowA q) (radius q) ∧ Endpoints (rowB q) (radius q) :=
  ⟨endpoints_aux (Or.inl rfl) q, endpoints_aux (Or.inr rfl) q⟩

private def edge (t : Nat) (i : Int) := cell t (i - t)

private theorem edge_step (t : Nat) (i : Int) :
    edge (t+1) i = rule (edge t (i-2)) (edge t (i-1)) (edge t i) := by
  unfold edge
  simp only [cell]
  congr 2 <;> omega

set_option maxRecDepth 60000 in
private theorem ten_bits : ∀ k : Fin 10,
    edge 5 k.val = (891 : Nat).testBit k.val ∧
    edge 9 k.val = (891 : Nat).testBit k.val ∧
    (264086941 : Nat).testBit (((k.val : Int)-97)%28).toNat = (891 : Nat).testBit k.val ∧
    (230553614 : Nat).testBit (((k.val : Int)-97)%28).toNat = (891 : Nat).testBit k.val := by
  decide +kernel

private theorem left_period (u : Nat) : ∀ i : Int, i < 10 → edge (5+u) i = edge (9+u) i := by
  induction u with
  | zero =>
    intro i hi
    by_cases neg : i < 0
    · unfold edge
      rw [cell_eq_false_of_lt _ _ (by omega), cell_eq_false_of_lt _ _ (by omega)]
    · let k : Fin 10 := ⟨i.toNat, by omega⟩
      have eq : (k.val : Int) = i := by dsimp [k]; omega
      rw [← eq]
      exact (ten_bits k).1.trans (ten_bits k).2.1.symm
  | succ u ih =>
    intro i hi
    rw [show 5+(u+1)=5+u+1 by omega, show 9+(u+1)=9+u+1 by omega,
      edge_step, edge_step, ih (i-2) (by omega), ih (i-1) (by omega), ih i hi]

private theorem left_blocks (n : Nat) (i : Int) (hi : i < 10) :
    edge (5+4*n) i = edge 5 i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 5+4*(n+1)=9+4*n by omega, ← left_period (4*n) i hi, ih]

private theorem left_initial (q : Nat) (j : Int) (hj : j < -(radius q : Int)+10) :
    rowA q j = cell (radius q) j ∧ rowB q j = cell (radius q) j := by
  by_cases below : j < -(radius q : Int)
  · simp [rowA, rowB, crop, show ¬ -(radius q : Int) ≤ j by omega,
      cell_eq_false_of_lt _ _ below]
  · let k : Fin 10 := ⟨(j+radius q).toNat, by omega⟩
    have eq : (k.val : Int) = j+radius q := by dsimp [k]; omega
    have bit : cell (radius q) j = (891 : Nat).testBit k.val := by
      have same := left_blocks (84*q+23) (k.val : Int) (by omega)
      rw [show 5+4*(84*q+23)=radius q by unfold radius; omega] at same
      have pos : (k.val : Int) - radius q = j := by omega
      exact (by simpa only [edge, pos] using same.trans (ten_bits k).1)
    have modEq : j%28 = ((k.val : Int)-97)%28 := by unfold radius at eq; omega
    simp only [rowA, rowB, crop, ite_eq_left (show -(radius q : Int) ≤ j by omega),
      ite_eq_left (show j ≤ cut q by unfold radius cut at *; omega), bit, modEq]
    exact ⟨(ten_bits k).2.2.1, (ten_bits k).2.2.2⟩

/-- The ten leftmost cells and the vacuum beyond them agree with the singleton
of the corresponding age for all subsequent times. -/
theorem genuine_left_ten (q t : Nat) : ∀ j : Int, j < -(radius q : Int)-t+10 →
    evol (rowA q) t j = cell (radius q+t) j ∧
    evol (rowB q) t j = cell (radius q+t) j := by
  induction t with
  | zero => intro j hj; exact left_initial q j (by omega)
  | succ t ih =>
    intro j hj
    obtain ⟨al, bl⟩ := ih (j-1) (by omega)
    obtain ⟨ac, bc⟩ := ih j (by omega)
    obtain ⟨ar, br⟩ := ih (j+1) (by omega)
    constructor <;> change rule _ _ _ = rule _ _ _
    · rw [al, ac, ar]; rfl
    · rw [bl, bc, br]; rfl

/-! ### Looking earlier than the comparison starts -/

private def sample (x : Int → Bool) : Nat → Int → List Bool
  | 0, _ => []
  | k+1, p => x p :: sample x k (p+1)

private def emit (a b : Bool) : List Bool → List Bool
  | [] => []
  | c :: cs => rule a b c :: emit b c cs

-- Guess the last two predecessor bits and reconstruct towards the left edge.
private def unroll (b c : Bool) : List Bool → List Bool
  | [] => [b,c]
  | y :: ys =>
    let rest := unroll b c ys
    (xor y (rest[0]?.getD false || rest[1]?.getD false)) :: rest

private theorem unroll_emit (xs : List Bool) (a b : Bool) :
    ∃ l r, unroll l r (emit a b xs) = a :: b :: xs := by
  induction xs generalizing a b with
  | nil => exact ⟨a,b,rfl⟩
  | cons x xs ih =>
    obtain ⟨l,r,h⟩ := ih b x
    refine ⟨l,r,?_⟩
    simp [emit,unroll,h,rule]

private def possible : Nat → List Bool → Bool
  | 0, _ => true
  | d+1, ys =>
    let accept := fun (b c : Bool) =>
      match unroll b c ys with
      | false :: false :: xs => possible d xs
      | _ => false
    accept false false || accept false true || accept true false || accept true true

private theorem possible_emit (d : Nat) (xs : List Bool) (ok : possible d xs = true) :
    possible (d+1) (emit false false xs) = true := by
  obtain ⟨b,c,h⟩ := unroll_emit xs false false
  cases b <;> cases c <;> simp [possible,h,ok]

private theorem sample_step (x : Int → Bool) (k : Nat) (p : Int) :
    sample (fun j => rule (x (j-1)) (x j) (x (j+1))) k (p-1) =
      emit (x (p-2)) (x (p-1)) (sample x k p) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    simp only [sample,emit]
    have tail := ih (p+1)
    rw [show p+1-1=p by omega, show p+1-2=p-1 by omega] at tail
    simp only [show p-1-1=p-2 by omega, show p-1+1=p by omega,tail]

private theorem possible_from_vacuum (x : Int → Bool) (p : Int)
    (vac : ∀ j, j < p → x j = false) (k d : Nat) :
    possible d (sample (evol x d) k (p-d)) = true := by
  have white (t : Nat) : ∀ j : Int, j < p-t → evol x t j = false := by
    induction t with
    | zero => intro j hj; exact vac j (by omega)
    | succ t ih =>
      intro j hj
      change rule _ _ _ = false
      rw [ih (j-1) (by omega), ih j (by omega), ih (j+1) (by omega)]
      decide
  induction d with
  | zero => rfl
  | succ d ih =>
    have step := sample_step (evol x d) k (p-d)
    rw [white d _ (by omega),white d _ (by omega)] at step
    rw [show p-((d+1 : Nat) : Int)=p-d-1 by omega]
    exact (congrArg (possible (d+1)) step).trans (possible_emit d _ ih)

private theorem sample_ext (x y : Int → Bool) (k : Nat) (p s : Int)
    (eq : ∀ i : Nat, i < k → x (p+i) = y (s+i)) : sample x k p = sample y k s := by
  induction k generalizing p s with
  | zero => rfl
  | succ k ih =>
    simp only [sample]
    congr 1
    · simpa using eq 0 (by omega)
    · apply ih
      intro i hi
      rw [show p+1+(i : Int)=p+(i+1 : Nat) by omega,
        show s+1+(i : Int)=s+(i+1 : Nat) by omega]
      exact eq (i+1) (by omega)

private theorem initial_sample (q word k : Nat) (hk : k ≤ 46) :
    sample (crop q word) k (-(radius q : Int)) =
      sample (fun j => word.testBit (j%28).toNat) k (-97) := by
  apply sample_ext
  intro i hi
  unfold crop
  rw [ite_eq_left (by omega),ite_eq_left (by unfold cut radius; omega)]
  congr 2
  unfold radius
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 4000000 in
private theorem rejected :
    possible 6 (sample (fun j => (264086941 : Nat).testBit (j%28).toNat) 46 (-97)) = false ∧
    possible 2 (sample (fun j => (230553614 : Nat).testBit (j%28).toNat) 36 (-97)) = false := by
  decide +kernel

/-- Looking further back separates both families from the singleton. Even with
an unrestricted right tail, the first start cannot have a six-step past with
the nominal left vacuum, and the second start cannot have a two-step past. -/
theorem older_origin_excludes (q : Nat) (x : Int → Bool) :
    ((∀ j, j < -(radius q : Int)+6 → x j = false) → evol x 6 ≠ rowA q) ∧
    ((∀ j, j < -(radius q : Int)+2 → x j = false) → evol x 2 ≠ rowB q) := by
  constructor
  · intro vac eq
    have ok := possible_from_vacuum x _ vac 46 6
    rw [eq, show -(radius q : Int)+6-(6 : Nat) = -(radius q : Int) by omega,
      rowA, initial_sample _ _ _ (by decide), rejected.1] at ok
    contradiction
  · intro vac eq
    have ok := possible_from_vacuum x _ vac 36 2
    rw [eq, show -(radius q : Int)+2-(2 : Nat) = -(radius q : Int) by omega,
      rowB, initial_sample _ _ _ (by decide), rejected.2] at ok
    contradiction

end Ruliology.CellularAutomata.Rule30HalfAgeOrigin
