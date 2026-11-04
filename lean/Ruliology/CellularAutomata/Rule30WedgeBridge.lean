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


/-! ## 1. Polynomial-Time Row-Stepping Evaluation of `cone`, `inverse`, `peelPow`, and `wedge` -/

/-- Tabulate `k` consecutive values `[x t, x (t + 1), ..., x (t + k - 1)]` of a function `x : Nat → Sym`. -/
def tabulate (x : Nat → Sym) (t : Nat) : Nat → List Sym
  | 0 => []
  | k + 1 => x t :: tabulate x (t + 1) k

/-- Pairwise `phi` combination of two lists of `Sym`. -/
def zipPhi : List Sym → List Sym → List Sym
  | a :: as, b :: bs => phi a b :: zipPhi as bs
  | _, _ => []

/-- **Exact Cone Row-Step Identity (`zipPhi_tabulate_cone`):** combining row `t` (length `k + 1`
from `j + 1`) and row `t + 1` (length `k` from `j + 1`) with `zipPhi` produces row `t + 2`
(length `k` from `j`). -/
theorem zipPhi_tabulate_cone (e : Stream) (t : Nat) : ∀ (k j : Nat),
    zipPhi (tabulate (cone e t) (j + 1) (k + 1)) (tabulate (cone e (t + 1)) (j + 1) k) =
      tabulate (cone e (t + 2)) j k
  | 0, _ => rfl
  | k + 1, j => by
    have h1 : tabulate (cone e t) (j + 1) (k + 1 + 1) =
        cone e t (j + 1) :: tabulate (cone e t) (j + 1 + 1) (k + 1) := rfl
    have h2 : tabulate (cone e (t + 1)) (j + 1) (k + 1) =
        cone e (t + 1) (j + 1) :: tabulate (cone e (t + 1)) (j + 1 + 1) k := rfl
    have h3 : tabulate (cone e (t + 2)) j (k + 1) =
        cone e (t + 2) j :: tabulate (cone e (t + 2)) (j + 1) k := rfl
    rw [h1, h2, h3, zipPhi, zipPhi_tabulate_cone e t k (j + 1)]
    rfl

/-- Collect `k` diagonal entries `cone e t j, cone e (t + 1) j, ...` from two adjacent rows `r0, r1`. -/
def collectHead : Nat → List Sym → List Sym → List Sym
  | 0, _, _ => []
  | k + 1, r0, r1 => r0.headD 0 :: collectHead k r1 (zipPhi r0.tail r1.tail)

/-- **Exact Linear Row-Stepping Identity for `cone` (`collectHead_tabulate_cone`):** starting from
`r0 = tabulate (cone e t) j k` and `r1 = tabulate (cone e (t + 1)) j (k - 1)`, `collectHead`
returns `[cone e t j, cone e (t + 1) j, ..., cone e (t + k - 1) j]`. -/
theorem collectHead_tabulate_cone (e : Stream) : ∀ (k t j : Nat),
    collectHead k (tabulate (cone e t) j k) (tabulate (cone e (t + 1)) j (k - 1)) =
      tabulate (fun s => cone e s j) t k
  | 0, _, _ => rfl
  | 1, t, j => rfl
  | k + 2, t, j => by
    have h0 : tabulate (cone e t) j (k + 2) =
        cone e t j :: tabulate (cone e t) (j + 1) (k + 1) := rfl
    have h1 : tabulate (cone e (t + 1)) j (k + 2 - 1) =
        cone e (t + 1) j :: tabulate (cone e (t + 1)) (j + 1) k := rfl
    rw [collectHead, h0, List.headD_cons, List.tail_cons]
    conv => lhs; rhs; rw [h1, List.tail_cons, zipPhi_tabulate_cone e t k j, ← h1]
    have ih := collectHead_tabulate_cone e (k + 1) (t + 1) j
    simp only [Nat.add_sub_cancel] at ih
    rw [show k + 2 - 1 = k + 1 by omega, ih]
    rfl

/-- Fast `O(M^2)` computation of `[inverse e 0, inverse e 1, ..., inverse e (M - 1)]`. -/
def fastInverseList (M : Nat) (e : Stream) : List Sym :=
  collectHead M (tabulate (cone e 0) 0 M) (tabulate (cone e 1) 0 (M - 1))

/-- **Fast Inverse List Equivalence (`fastInverseList_eq`):** `fastInverseList M e` equals
`tabulate (inverse e) 0 M`. -/
theorem fastInverseList_eq (M : Nat) (e : Stream) :
    fastInverseList M e = tabulate (inverse e) 0 M :=
  collectHead_tabulate_cone e M 0 0

/-- One-step `phi` contraction on a finite list of stream values. -/
def peelList : List Sym → List Sym
  | a :: b :: rest => phi a b :: peelList (b :: rest)
  | _ => []

/-- `n`-fold iteration of `peelList`. -/
def iterPeelList : Nat → List Sym → List Sym
  | 0, l => l
  | n + 1, l => iterPeelList n (peelList l)

/-- Contracting `tabulate x t (k + 1)` with `peelList` yields `tabulate (peel x) t k`. -/
theorem peelList_tabulate (x : Stream) : ∀ (k t : Nat),
    peelList (tabulate x t (k + 1)) = tabulate (peel x) t k
  | 0, _ => rfl
  | k + 1, t => by
    have h : tabulate x t (k + 1 + 1) = x t :: x (t + 1) :: tabulate x (t + 1 + 1) k := rfl
    rw [h, peelList]
    have ih := peelList_tabulate x k (t + 1)
    have h2 : tabulate x (t + 1) (k + 1) = x (t + 1) :: tabulate x (t + 1 + 1) k := rfl
    rw [← h2, ih]
    rfl

/-- **Exact Tabulated Peel Identity (`iterPeelList_tabulate`):** applying `iterPeelList n` to
`tabulate x t (k + n)` yields `tabulate (peelPow n x) t k`. -/
theorem iterPeelList_tabulate : ∀ (n k t : Nat) (x : Stream),
    iterPeelList n (tabulate x t (k + n)) = tabulate (peelPow n x) t k
  | 0, k, t, x => by simp [iterPeelList, peelPow]
  | n + 1, k, t, x => by
    rw [show k + (n + 1) = (k + n) + 1 by omega, iterPeelList,
      peelList_tabulate x (k + n) t, iterPeelList_tabulate n k t (peel x), peelPow_inside]

/-- Fast `O((n + K)^2)` computation of `[wedge n e 0, ..., wedge n e (K - 1)]`. -/
def fastWedgeList (n K : Nat) (e : Stream) : List Sym :=
  iterPeelList n (fastInverseList (K + n) e)

/-- **Fast Wedge List Equivalence (`fastWedgeList_eq`):** `fastWedgeList n K e` equals
`tabulate (wedge n e) 0 K`. -/
theorem fastWedgeList_eq (n K : Nat) (e : Stream) :
    fastWedgeList n K e = tabulate (wedge n e) 0 K := by
  unfold fastWedgeList wedge
  rw [fastInverseList_eq, iterPeelList_tabulate]

/-- All elements of `tabulate x t K` equal `c` iff `∀ i < K, x (t + i) = c`. -/
theorem all_tabulate_eq_true_iff (x : Stream) (c : Sym) : ∀ (K t : Nat),
    ((tabulate x t K).all (fun s => decide (s = c)) = true) ↔ (∀ i, i < K → x (t + i) = c)
  | 0, _ => by simp [tabulate]
  | K + 1, t => by
    simp only [tabulate, List.all_cons, Bool.and_eq_true, decide_eq_true_eq,
      all_tabulate_eq_true_iff x c K (t + 1)]
    constructor
    · rintro ⟨h0, hrest⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have h := hrest i (by omega)
        rwa [show t + 1 + i = t + (i + 1) by omega] at h
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have h1 := h (i + 1) (by omega)
      rwa [show t + (i + 1) = t + 1 + i by omega] at h1

/-- **Decidable ConstantWedge Criterion (`constantWedge_iff_fastWedgeList`):** `ConstantWedge n K c e`
holds iff `(fastWedgeList n K e).all (fun s => decide (s = c)) = true`. -/
theorem constantWedge_iff_fastWedgeList (n K : Nat) (c : Sym) (e : Stream) :
    ConstantWedge n K c e ↔ (fastWedgeList n K e).all (fun s => decide (s = c)) = true := by
  rw [fastWedgeList_eq, all_tabulate_eq_true_iff]
  simp only [Nat.zero_add, ConstantWedge]

/-! ## 2. Finite Prefix Enumeration & Completeness for `BinaryPrefix` and `HardCoreJunction` -/

/-- Stream backed by a finite list `w : List Sym` padded with `0`. -/
def listStream (w : List Sym) (i : Nat) : Sym :=
  w.getD i 0

/-- Extract the length-`L` prefix of a stream `e` as a `List Sym`. -/
def streamPrefix : Stream → Nat → List Sym
  | _, 0 => []
  | e, L + 1 => e 0 :: streamPrefix (shift e) L

/-- `listStream (streamPrefix e L)` agrees with `e` on all `i < L`. -/
theorem listStream_streamPrefix : ∀ (L : Nat) (e : Stream) (i : Nat), i < L →
    listStream (streamPrefix e L) i = e i
  | 0, _, _, hi => by omega
  | _ + 1, _, 0, _ => rfl
  | L + 1, e, i + 1, hi => listStream_streamPrefix L (shift e) i (by omega)

/-- Exhaustive generator of all binary words (`1` or `2`) of length `L`. -/
def genBin : Nat → List (List Sym)
  | 0 => [[]]
  | L + 1 => (genBin L).map (1 :: ·) ++ (genBin L).map (2 :: ·)

/-- **Completeness of `genBin` (`streamPrefix_mem_genBin`):** if `BinaryPrefix e L`, then
`streamPrefix e L ∈ genBin L`. -/
theorem streamPrefix_mem_genBin : ∀ (L : Nat) (e : Stream),
    BinaryPrefix e L → streamPrefix e L ∈ genBin L
  | 0, _, _ => List.Mem.head []
  | L + 1, e, hb => by
    have hshift : BinaryPrefix (shift e) L := fun i hi => hb (i + 1) (by omega)
    have ih := streamPrefix_mem_genBin L (shift e) hshift
    simp only [streamPrefix, genBin, List.mem_append, List.mem_map]
    rcases hb 0 (by omega) with h1 | h2
    · left; exact ⟨streamPrefix (shift e) L, ih, by rw [h1]⟩
    · right; exact ⟨streamPrefix (shift e) L, ih, by rw [h2]⟩

/-- Boolean check that `w` has no adjacent `1, 1` at indices `(i - 1, i)` for `n ≤ i < L`. -/
def checkHC (n L : Nat) (w : List Sym) : Bool :=
  (List.range (L - n)).all (fun d =>
    !(decide (listStream w (n + d - 1) = 1) && decide (listStream w (n + d) = 1)))

/-- If `HardCoreJunction n L e` holds, then `checkHC n L (streamPrefix e L) = true`. -/
theorem checkHC_streamPrefix {n L : Nat} {e : Stream} (hn : 1 ≤ n)
    (hhc : HardCoreJunction n L e) : checkHC n L (streamPrefix e L) = true := by
  unfold checkHC
  rw [List.all_eq_true]
  intro d hd
  rw [List.mem_range] at hd
  rw [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
  rw [listStream_streamPrefix L e (n + d - 1) (by omega),
      listStream_streamPrefix L e (n + d) (by omega)]
  have h := hhc (n + d) (by omega) (by omega)
  by_cases ha : e (n + d - 1) = 1
  · right; intro hb; exact h ⟨ha, hb⟩
  · left; exact ha

/-- Boolean certificate checking that NO word in `genBin (n + K)` satisfies both `checkHC n (n + K)`
and `ConstantWedge n K c`. -/
def certNoHCWedge (n K : Nat) (c : Sym) : Bool :=
  (genBin (n + K)).all (fun w =>
    !(checkHC n (n + K) w && (fastWedgeList n K (listStream w)).all (fun s => decide (s = c))))

/-- **Soundness of `certNoHCWedge` (`no_hc_wedge_of_cert`):** if `certNoHCWedge n K c = true`, then
no stream `e` satisfies `BinaryPrefix e (n + K)`, `HardCoreJunction n (n + K) e`, and `ConstantWedge n K c e`. -/
theorem no_hc_wedge_of_cert {n K : Nat} {c : Sym} (hn : 1 ≤ n)
    (hcert : certNoHCWedge n K c = true) :
    ∀ e : Stream, BinaryPrefix e (n + K) → HardCoreJunction n (n + K) e → ¬ ConstantWedge n K c e := by
  intro e hb hhc hcw
  unfold certNoHCWedge at hcert
  rw [List.all_eq_true] at hcert
  have hmem := streamPrefix_mem_genBin (n + K) e hb
  have hw := hcert (streamPrefix e (n + K)) hmem
  have hhc_b : checkHC n (n + K) (streamPrefix e (n + K)) = true := checkHC_streamPrefix hn hhc
  have hcw_list : ConstantWedge n K c (listStream (streamPrefix e (n + K))) := by
    intro t ht
    rw [wedge_prefix (listStream (streamPrefix e (n + K))) e (n + K) n t
      (fun i hi => listStream_streamPrefix (n + K) e i hi) (by omega)]
    exact hcw t ht
  have hcw_b : (fastWedgeList n K (listStream (streamPrefix e (n + K)))).all
      (fun s => decide (s = c)) = true :=
    (constantWedge_iff_fastWedgeList n K c _).mp hcw_list
  rw [hhc_b, hcw_b] at hw
  contradiction

/-! ## 3. Unconditional Proof of `SmallRW` and Discharging `SmallRW` Across the Bridge Ladder -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- All 12 certificates `(1 ≤ n ≤ 6, c ∈ {2, 3})` pass at horizon `n + K ≤ 10`. -/
theorem smallRW_certs :
    certNoHCWedge 1 2 2 = true ∧ certNoHCWedge 1 2 3 = true ∧
    certNoHCWedge 2 2 2 = true ∧ certNoHCWedge 2 2 3 = true ∧
    certNoHCWedge 3 5 2 = true ∧ certNoHCWedge 3 5 3 = true ∧
    certNoHCWedge 4 3 2 = true ∧ certNoHCWedge 4 3 3 = true ∧
    certNoHCWedge 5 5 2 = true ∧ certNoHCWedge 5 5 3 = true ∧
    certNoHCWedge 6 4 2 = true ∧ certNoHCWedge 6 4 3 = true := by
  decide

/-- Helper: if `n + K ≤ 2 * n + r + 2` and `K ≤ n + r + 2`, any `RWWitness n r c e` restricts to
`BinaryPrefix e (n + K)`, `HardCoreJunction n (n + K) e`, and `ConstantWedge n K c e`. -/
theorem no_rwWitness_of_cert {n K r : Nat} {c : Sym} {e : Stream}
    (hn : 1 ≤ n) (hK : K ≤ n + r + 2) (hcert : certNoHCWedge n K c = true)
    (hw : RWWitness n r c e) : False := by
  apply no_hc_wedge_of_cert hn hcert e
  · intro i hi; exact hw.1 i (by omega)
  · intro i hni hi; exact hw.2.1 i hni (by omega)
  · intro t ht; exact hw.2.2.1 t (by omega)

/-- **Unconditional Proof of `SmallRW` (`smallRW`):** for all `1 ≤ n < 7`, `r ≤ 2`, and
`c ∈ {2, 3}`, there is no `RWWitness n r c e`. -/
theorem smallRW : SmallRW := by
  intro n hn1 hn7 r hr c hc e hw
  obtain ⟨c12, c13, c22, c23, c32, c33, c42, c43, c52, c53, c62, c63⟩ := smallRW_certs
  have hn_cases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hc with rfl | rfl
  · rcases hn_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_rwWitness_of_cert (by omega) (by omega) c12 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c22 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c32 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c42 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c52 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c62 hw
  · rcases hn_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_rwWitness_of_cert (by omega) (by omega) c13 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c23 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c33 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c43 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c53 hw
    · exact no_rwWitness_of_cert (by omega) (by omega) c63 hw

/-- **`BWH` Alone Implies `RW` (`bwh_implies_rw_unconditional`):** with `smallRW` proved, the
`SmallRW` hypothesis is discharged from `bwh_implies_rw`. -/
theorem bwh_implies_rw_unconditional (hb : BWH) : RW :=
  bwh_implies_rw hb smallRW

end Rule30WedgeBridge

end Ruliology.CellularAutomata
