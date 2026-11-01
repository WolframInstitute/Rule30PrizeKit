module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# The binary wedge hypothesis and the rotated wedge

Symbols are `Sym = Fin 4`, streams are `Nat → Sym`. `phi` is the backward step on pairs of adjacent
cells of Rule 30 (see `Rule30SEPToPeriodTwo.pair_backward`), `boundary q = 3 - q`, and `cone e` is the
inverse cone built from a boundary stream `e` by `cone e 0 j = boundary (e j)`,
`cone e 1 j = phi (e j) (boundary (e (j + 1)))` and
`cone e (t + 2) j = phi (cone e t (j + 1)) (cone e (t + 1) (j + 1))`. `inverse e t = cone e t 0` is its
diagonal, `peel x t = phi (x t) (x (t + 1))`, and `wedge n e = peel^n (inverse e)`. A stream is binary
on a prefix when its symbols there are `1` or `2`, and `ConstantWedge n L c e` says `wedge n e t = c`
for `t < L`.

Two statements are open hypotheses and are not proved here:

* `BWH`: for `n ≥ 7` and `c ∈ {2, 3}`, no stream with a binary prefix of length `2n + 2` has a
  constant wedge `c` of length `n + 2`;
* `RW`: for `n ≥ 1`, `r ≤ 2` and `c ∈ {2, 3}`, there is no `RWWitness n r c e`: a binary prefix of
  length `2n + r + 2` with no two adjacent `1` symbols from position `n` on, a constant wedge `c` of
  length `n + r + 2`, and the last two symbols `1, 2`.

`bwh_implies_rw`: `BWH` and `SmallRW`, which is `RW` for `n < 7`, imply `RW`. The six small lengths are
hypotheses supplied by finite certificates, not proved here. `rw_truncates_to_bwh` and
`maximal_drop_inheritance` are the finite-horizon steps. Prefix locality (`inverse_prefix`,
`wedge_prefix`) shows that infinite streams encode finite words faithfully. Controls:
`small_control_table`, `hard_core_guard_control` and `small_bwh_control` show that the small cases and the
hard-core guard cannot be dropped.

For how `BWH` and `RW` relate to `Rule30PeriodTwo.Q01` and to mortality of the auxiliary frontier
(`Rule30AlternatingTraceBridge.Mortality`), see `Rule30SEPToPeriodTwo`: no implication is proved in
either direction.

Nothing here proves `BWH` or `RW`, and nothing here bounds the center column of Rule 30; Problems 1 to 3
stay open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30WedgeBridge


abbrev Sym := Fin 4
abbrev Stream := Nat → Sym

def boundary (q : Sym) : Sym := ⟨3-q.val, by omega⟩

def phi (a b : Sym) : Sym :=
  match a.val, b.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 3 | 0, _ => 2
  | 2, 0 => 3 | 2, 1 => 2 | 2, 2 => 0 | 2, _ => 1
  | _, 0 => 3 | _, 1 => 2 | _, 2 => 1 | _, _ => 0

def cone (e : Stream) : Nat → Nat → Sym
  | 0, j => boundary (e j)
  | 1, j => phi (e j) (boundary (e (j+1)))
  | t+2, j => phi (cone e t (j+1)) (cone e (t+1) (j+1))

def inverse (e : Stream) (t : Nat) : Sym := cone e t 0
def peel (x : Stream) (t : Nat) : Sym := phi (x t) (x (t+1))

def peelPow : Nat → Stream → Stream
  | 0, x => x
  | n+1, x => peel (peelPow n x)

def wedge (n : Nat) (e : Stream) : Stream := peelPow n (inverse e)

def shift (e : Stream) : Stream := fun t => e (t+1)

theorem cone_shift (e : Stream) (t : Nat) :
    ∀ j, cone (shift e) t j = cone e t (j+1) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    match t with
    | 0 => rfl
    | 1 => rfl
    | t+2 =>
      simp only [cone]
      rw [ih t (by omega), ih (t+1) (by omega)]

theorem rotated_peel (e : Stream) :
    peel (inverse (shift e)) = fun t => inverse e (t+2) := by
  funext t
  simp only [peel, inverse, cone_shift, cone]

theorem peelPow_translate (n k : Nat) (x : Stream) :
    peelPow n (fun t => x (t+k)) = fun t => peelPow n x (t+k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext t
    simp only [peelPow, peel, ih]
    congr 2 <;> omega

theorem peelPow_inside (n : Nat) (x : Stream) :
    peelPow n (peel x) = peelPow (n+1) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [peelPow] at *; rw [ih]

/-- Exact at every depth, for arbitrary four-state endpoints. -/
theorem wedge_shift (n : Nat) (e : Stream) (t : Nat) :
    wedge (n+1) (shift e) t = wedge n e (t+2) := by
  unfold wedge
  rw [← peelPow_inside, rotated_peel, peelPow_translate]

theorem cone_locality (e f : Stream) (t : Nat) :
    ∀ j, (∀ i, j ≤ i → i ≤ j+t → e i = f i) → cone e t j = cone f t j := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j h
    match t with
    | 0 => simp only [cone]; rw [h j (by omega) (by omega)]
    | 1 => simp only [cone]; rw [h j (by omega) (by omega), h (j+1) (by omega) (by omega)]
    | t+2 =>
      simp only [cone]
      rw [ih t (by omega) (j+1) (by intro i hi hj; exact h i (by omega) (by omega)),
          ih (t+1) (by omega) (j+1) (by intro i hi hj; exact h i (by omega) (by omega))]

theorem inverse_prefix (e f : Stream) (L : Nat)
    (h : ∀ i, i < L → e i = f i) :
    ∀ i, i < L → inverse e i = inverse f i := by
  intro i hi
  exact cone_locality e f i 0 (by intro j _ hj; exact h j (by omega))

theorem peelPow_locality (x y : Stream) (n : Nat) :
    ∀ t, (∀ i, t ≤ i → i ≤ t+n → x i = y i) → peelPow n x t = peelPow n y t := by
  induction n with
  | zero => intro t h; exact h t (by omega) (by omega)
  | succ n ih =>
    intro t h
    simp only [peelPow, peel]
    rw [ih t (by intro i hi hj; exact h i hi (by omega)),
        ih (t+1) (by intro i hi hj; exact h i (by omega) (by omega))]

theorem wedge_prefix (e f : Stream) (L n t : Nat)
    (h : ∀ i, i < L → e i = f i) (ht : t+n < L) :
    wedge n e t = wedge n f t := by
  apply peelPow_locality
  intro i _ hi
  exact inverse_prefix e f L h i (by omega)

def binary (q : Sym) : Prop := q=1 ∨ q=2
def constantTail (q : Sym) : Prop := q=2 ∨ q=3
def BinaryPrefix (e : Stream) (L : Nat) : Prop := ∀ i, i < L → binary (e i)

def ConstantWedge (n L : Nat) (c : Sym) (e : Stream) : Prop :=
  ∀ t, t < L → wedge n e t = c

/-- A finite binary witness; no hard-core or terminal conditions. -/
def BinaryRun (n k : Nat) (c : Sym) (e : Stream) : Prop :=
  BinaryPrefix e (n+k) ∧ ConstantWedge n k c e

/-- A finite horizon, with both an attaining witness and the universal bound. -/
def MaxHorizon (n : Nat) (c : Sym) (M : Nat) : Prop :=
  (∃ e, BinaryRun n M c e) ∧ ∀ e k, BinaryRun n k c e → k ≤ M

theorem binary_run_shift (n k : Nat) (c : Sym) (e : Stream)
    (h : BinaryRun n (k+2) c e) : BinaryRun (n+1) k c (shift e) := by
  constructor
  · intro i hi
    exact h.1 (i+1) (by omega)
  · intro t ht
    rw [wedge_shift]
    exact h.2 (t+2) (by omega)

/-- The first nonbinary forced symbol shifts with the entire constant cut. -/
theorem exact_exit_shift (n k : Nat) (c : Sym) (e : Stream)
    (hb : BinaryPrefix e (n+(k+2)))
    (hx : ¬binary (e (n+(k+2))))
    (hc : ConstantWedge n (k+3) c e) :
    BinaryPrefix (shift e) ((n+1)+k) ∧
    ¬binary (shift e ((n+1)+k)) ∧
    ConstantWedge (n+1) (k+1) c (shift e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hb (i+1) (by omega)
  · simpa only [shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx
  · intro t ht
    rw [wedge_shift]
    exact hc (t+2) (by omega)

/-- This is a lower bound, not the upper bound required by BWH+. -/
theorem horizon_drop_floor (n k M : Nat) (c : Sym)
    (hold : MaxHorizon n c (k+2)) (hnew : MaxHorizon (n+1) c M) : k ≤ M := by
  obtain ⟨e, he⟩ := hold.1
  exact hnew.2 (shift e) k (binary_run_shift n k c e he)

/-- Every parent maximizer supplies a child maximizer when the drop is two.
It does not assert that every child maximizer has a parent. -/
theorem maximal_drop_inheritance (n k : Nat) (c : Sym) (e : Stream)
    (hold : BinaryRun n (k+2) c e) (hnew : MaxHorizon (n+1) c k) :
    BinaryRun (n+1) k c (shift e) ∧
    (∀ L, BinaryRun (n+1) L c (shift e) → L ≤ k) ∧
    (∀ j, shift e ((n+1)+j) = e (n+(j+2))) := by
  refine ⟨binary_run_shift n k c e hold, ?_, ?_⟩
  · intro L hL
    exact hnew.2 (shift e) L hL
  · intro j
    unfold shift
    congr 1 <;> omega

/-- All continuation pairs, including the pair crossing the source boundary. -/
def HardCoreJunction (n L : Nat) (e : Stream) : Prop :=
  ∀ i, n ≤ i → i < L → ¬(e (i-1)=1 ∧ e i=1)

/-- The final symbol is included in BinaryPrefix; 12 is the penultimate pair. -/
def RWWitness (n r : Nat) (c : Sym) (e : Stream) : Prop :=
  BinaryPrefix e (2*n+r+2) ∧
  HardCoreJunction n (2*n+r+2) e ∧
  ConstantWedge n (n+r+2) c e ∧
  e (2*n+r-1)=1 ∧ e (2*n+r)=2

def BWH : Prop := ∀ n, 7 ≤ n → ∀ c, constantTail c → ∀ e,
  BinaryPrefix e (2*n+2) → ¬ConstantWedge n (n+2) c e

def SmallRW : Prop := ∀ n, 1 ≤ n → n < 7 → ∀ r, r ≤ 2 → ∀ c,
  constantTail c → ∀ e, ¬RWWitness n r c e

def RW : Prop := ∀ n, 1 ≤ n → ∀ r, r ≤ 2 → ∀ c,
  constantTail c → ∀ e, ¬RWWitness n r c e

theorem bwh_implies_rw (hb : BWH) (hs : SmallRW) : RW := by
  intro n hn r hr c hc e hw
  by_cases hsmall : n < 7
  · exact hs n hn hsmall r hr c hc e hw
  · exact hb n (by omega) c hc e
      (by intro i hi; exact hw.1 i (by omega))
      (by intro t ht; exact hw.2.2.1 t (by omega))

def prefixStream (e : Stream) (L : Nat) : Stream := fun i => if i < L then e i else 0

/-- A finite RW witness truncates to the exact finite BWH witness. -/
theorem rw_truncates_to_bwh (n r : Nat) (c : Sym) (e : Stream)
    (hw : RWWitness n r c e) :
    BinaryPrefix (prefixStream e (2*n+2)) (2*n+2) ∧
    ConstantWedge n (n+2) c (prefixStream e (2*n+2)) := by
  constructor
  · intro i hi
    simpa only [prefixStream, hi, ↓reduceIte] using hw.1 i (by omega)
  · intro t ht
    rw [wedge_prefix (prefixStream e (2*n+2)) e (2*n+2) n t
      (by intro i hi; simp only [prefixStream, hi, ↓reduceIte]) (by omega)]
    exact hw.2.2.1 t (by omega)

/-- The retained n=5, tail-3 exception, including eight forced symbols. -/
def smallControl (i : Nat) : Sym :=
  ([1,2,1,2,1,1,2,1,1,2,1,2,1] : List Sym).getD i 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem small_control_table :
    (∀ i : Fin 13, binary (smallControl i.val)) ∧
    (∀ t : Fin 8, wedge 5 smallControl t.val = 3) ∧
    smallControl 10 = 1 ∧ smallControl 11 = 2 ∧
    smallControl 4 = 1 ∧ smallControl 5 = 1 := by
  unfold binary
  decide

/-- Dropping the junction guard admits this exact small RW witness. -/
theorem hard_core_guard_control :
    BinaryPrefix smallControl 13 ∧ ConstantWedge 5 8 3 smallControl ∧
    smallControl 10 = 1 ∧ smallControl 11 = 2 ∧
    ¬HardCoreJunction 5 13 smallControl := by
  obtain ⟨hb, hc, h10, h11, h4, h5⟩ := small_control_table
  refine ⟨?_, ?_, h10, h11, ?_⟩
  · intro i hi
    exact hb ⟨i, hi⟩
  · intro t ht
    exact hc ⟨t, ht⟩
  · intro h
    exact h 5 (by omega) (by omega) ⟨h4, h5⟩

/-- Extending BWH+ indiscriminately below n=7 is false on these definitions. -/
theorem small_bwh_control :
    ¬(∀ e, BinaryPrefix e 12 → ¬ConstantWedge 5 7 3 e) := by
  intro h
  exact h smallControl
    (by intro i hi; exact hard_core_guard_control.1 i (by omega))
    (by intro t ht; exact hard_core_guard_control.2.1 t (by omega))


end Rule30WedgeBridge
end Ruliology.CellularAutomata
