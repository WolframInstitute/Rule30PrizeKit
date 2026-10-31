module

public import Ruliology.CellularAutomata.Rule30FrozenRuler
public import Init.Data.Bool

/-!
# A one-in-four temporal tail cannot be attached to a black right edge

For an arbitrary code with a black edge, no two adjacent digits can eventually
follow the four-column, eight-tick one-in-four ether at any spatial or temporal
phase. In particular no full tail can do so. The invariant allows arbitrary
odd-time bits. Its backward spatial propagation discards one initial time step
per digit; no temporal period, finite support, or period bound is assumed.

`ether_step` checks that the excluded pattern is a genuine two-sided Rule30
pattern in this frame. The finite truth table in `local_descent` proves a local
step; induction, not enumeration of source depths or periods, reaches the edge.
`no_moving_ether_pair` translates the result through the existing right-edge
conjugacy. These are co-moving columns, not the fixed center column. Problem 1,
general same-edge rigidity and the alternating-tail case remain open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EtherGrounding

set_option autoImplicit false

open Rule30FrozenRuler Rule30Realization

/-- The pair invariant at a relative time phase. The second column's even
positions are `1000`; the first is its specified pointwise transform. -/
def good (r : Nat) (u v : Bool) : Bool :=
  match r % 8 with
  | 0 => !u && v
  | 1 => u
  | 2 => !u && !v
  | 3 => u
  | 4 => !u && !v
  | 5 => u == !v
  | 6 => u && !v
  | _ => u

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 4096 in
theorem local_descent : ∀ r : Fin 8,
    ∀ u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ w₀ w₁ w₂ : Bool,
    good r.val u₀ v₀ = true → good (r.val+1) u₁ v₁ = true →
    good (r.val+2) u₂ v₂ = true → good (r.val+3) u₃ v₃ = true →
    xor u₀ u₁ = (v₀ || w₀) → xor u₁ u₂ = (v₁ || w₁) →
    xor u₂ u₃ = (v₂ || w₂) →
    (w₀ = true → xor v₀ v₁ = true) →
    (w₁ = true → xor v₁ v₂ = true) →
    (w₂ = true → xor v₂ v₃ = true) →
    good (r.val+7) v₁ w₁ = true := by
  intro r
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨
      r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 := by omega
  rcases hr with h|h|h|h|h|h|h|h <;> simp only [h] <;> decide

theorem xor_cancel (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> decide

theorem delta_one (x : Nat → Bool) (t : Nat) :
    xor (iter t x 1) (iter (t+1) x 1) = iter t x 0 := by
  change xor (iter t x 1) (xor (iter t x 1) (iter t x 0)) = _
  exact xor_cancel _ _

theorem delta_succ (x : Nat → Bool) (j t : Nat) :
    xor (iter t x (j+2)) (iter (t+1) x (j+2)) =
      (iter t x (j+1) || iter t x j) := by
  change xor (iter t x (j+2)) (xor (iter t x (j+2)) _) = _
  exact xor_cancel _ _

theorem lower_dominates (x : Nat → Bool) (j t : Nat)
    (h : iter t x j = true) :
    xor (iter t x (j+1)) (iter (t+1) x (j+1)) = true := by
  cases j with
  | zero => simpa [delta_one] using h
  | succ j => rw [delta_succ]; simp [h]

/-- An eventual invariant of two adjacent temporal columns, with arbitrary phase. -/
def HasPair (x : Nat → Bool) (k p : Nat) : Prop :=
  ∃ s, ∀ t, s ≤ t → good (t+p) (iter t x (k+1)) (iter t x k) = true

theorem good_shift (a b n : Nat) (u v : Bool) :
    good ((a+b)%8+n) u v = good (a+n+b) u v := by
  have h : ((a+b)%8+n)%8 = (a+n+b)%8 := by omega
  unfold good
  rw [h]

/-- Move the invariant one digit toward the edge, losing one initial time. -/
theorem pair_descends (x : Nat → Bool) (j p : Nat)
    (h : HasPair x (j+1) p) : HasPair x j (p+6) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s+1, ?_⟩
  intro t ht
  cases t with
  | zero => omega
  | succ q =>
    have hq : s ≤ q := by omega
    let r : Fin 8 := ⟨(q+p)%8, Nat.mod_lt _ (by decide)⟩
    have g (i : Nat) :
        good (r.val+i) (iter (q+i) x (j+2)) (iter (q+i) x (j+1)) = true := by
      change good ((q+p)%8+i) _ _ = true
      rw [good_shift]
      exact hs (q+i) (by omega)
    have hd := local_descent r
      (iter q x (j+2)) (iter (q+1) x (j+2))
      (iter (q+2) x (j+2)) (iter (q+3) x (j+2))
      (iter q x (j+1)) (iter (q+1) x (j+1))
      (iter (q+2) x (j+1)) (iter (q+3) x (j+1))
      (iter q x j) (iter (q+1) x j) (iter (q+2) x j)
      (g 0) (g 1) (g 2) (g 3)
      (delta_succ x j q) (delta_succ x j (q+1))
      (delta_succ x j (q+2))
      (lower_dominates x j q) (lower_dominates x j (q+1))
      (lower_dominates x j (q+2))
    change good ((q+p)%8+7) _ _ = true at hd
    rw [good_shift] at hd
    have heq : q+7+p = q+1+(p+6) := by omega
    simpa only [heq] using hd

theorem pair_reaches_edge (x : Nat → Bool) (k p : Nat)
    (h : HasPair x k p) : ∃ q, HasPair x 0 q := by
  induction k generalizing p with
  | zero => exact ⟨p,h⟩
  | succ k ih => exact ih (p+6) (pair_descends x k p h)

theorem no_pair_at_edge (x : Nat → Bool) (hx : x 0 = true) (p : Nat) :
    ¬ HasPair x 0 p := by
  rintro ⟨s,hs⟩
  let t := 8*(s+p+1)+10-p
  have ht : s ≤ t := by dsimp [t]; omega
  have hr : (t+p)%8 = 2 := by dsimp [t]; omega
  have hh := hs t ht
  simp [good,hr,iter_zero,hx] at hh

/-- Uniform in depth, phase, initial row, and temporal behavior. -/
theorem no_black_edge_pair (x : Nat → Bool) (hx : x 0 = true) (k p : Nat) :
    ¬ HasPair x k p := by
  intro h
  obtain ⟨q,hq⟩ := pair_reaches_edge x k p h
  exact no_pair_at_edge x hx q hq

/-- Four spatial columns of the one-in-four ether, bit `t` read in time order.
The time words are `11010100`, `01010011`, `01001101`, `00110101`. -/
def ether (i t : Nat) : Bool :=
  (match i % 4 with
   | 0 => 43 | 1 => 202 | 2 => 178 | _ => 172).testBit (t % 8)

set_option synthInstance.maxSize 4096 in
theorem ether_pair_table : ∀ i : Fin 4, ∀ t : Fin 8,
    good (t.val+2*i.val) (ether (i.val+1) t.val) (ether i.val t.val) = true := by decide

theorem ether_pair (i t : Nat) :
    good (t+2*i) (ether (i+1) t) (ether i t) = true := by
  have hi : (i+1)%4 = (i%4+1)%4 := by omega
  have ht : (t+2*i)%8 = (t%8+2*(i%4))%8 := by omega
  have h := ether_pair_table ⟨i%4,Nat.mod_lt _ (by decide)⟩
    ⟨t%8,Nat.mod_lt _ (by decide)⟩
  simpa only [ether,good,hi,ht,Nat.mod_mod] using h

set_option synthInstance.maxSize 4096 in
theorem ether_step_table : ∀ i : Fin 4, ∀ t : Fin 8,
    ether i.val (t.val+1) =
      xor (ether i.val t.val) (ether (i.val+3) t.val || ether (i.val+2) t.val) := by decide

/-- Positive control: this is a genuine two-sided Rule30 pattern in the edge frame. -/
theorem ether_step (i t : Nat) : ether i (t+1) =
    xor (ether i t) (ether (i+3) t || ether (i+2) t) := by
  have h := ether_step_table ⟨i%4,Nat.mod_lt _ (by decide)⟩
    ⟨t%8,Nat.mod_lt _ (by decide)⟩
  simp only [ether] at h ⊢
  have h1 : (t+1)%8 = (t%8+1)%8 := by omega
  have h2 : (i+2)%4 = (i%4+2)%4 := by omega
  have h3 : (i+3)%4 = (i%4+3)%4 := by omega
  simpa only [h1,h2,h3,Nat.mod_mod] using h

/-- No pair of adjacent columns of a black-edge code can eventually become
this ether, at any spatial or temporal phase. No global period is assumed. -/
theorem no_eventual_ether_pair (x : Nat → Bool) (hx : x 0 = true)
    (k i q : Nat) : ¬ ∃ s, ∀ t, s ≤ t →
      iter t x k = ether i (t+q) ∧
      iter t x (k+1) = ether (i+1) (t+q) := by
  rintro ⟨s,hs⟩
  apply no_black_edge_pair x hx k (q+2*i)
  refine ⟨s, ?_⟩
  intro t ht
  obtain ⟨h0,h1⟩ := hs t ht
  rw [h0,h1]
  simpa only [Nat.add_assoc] using ether_pair i (t+q)

/-- In particular, an eventually matching full spatial tail is impossible. -/
theorem no_eventual_ether_tail (x : Nat → Bool) (hx : x 0 = true)
    (k i q : Nat) : ¬ ∃ s, ∀ t, s ≤ t → ∀ j,
      iter t x (k+j) = ether (i+j) (t+q) := by
  rintro ⟨s,hs⟩
  apply no_eventual_ether_pair x hx k i q
  refine ⟨s, ?_⟩
  intro t ht
  exact ⟨by simpa using hs t ht 0, hs t ht 1⟩

/-- The same exclusion for actual Rule30 cells at fixed offsets behind a
rightmost black cell. No hypothesis is imposed on the row to its left. -/
theorem no_moving_ether_pair (row : Int → Bool) (e : Int)
    (he : row e = true) (hr : ∀ z, e < z → row z = false) (k i q : Nat) :
    ¬ ∃ s, ∀ t, s ≤ t →
      evol row t (e+t-k) = ether i (t+q) ∧
      evol row t (e+t-(k+1 : Nat)) = ether (i+1) (t+q) := by
  rintro ⟨s,hs⟩
  apply no_eventual_ether_pair (code row e) (by simpa [code] using he) k i q
  refine ⟨s, ?_⟩
  intro t ht
  have hc := (edge_evol row e he hr t).2.2
  have eq (j : Nat) : iter t (code row e) j = evol row t (e+t-j) := by
    have h := congrFun hc j
    exact h.symm
  rw [eq,eq]
  exact hs t ht

end Ruliology.CellularAutomata.Rule30EtherGrounding
