module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers

/-!
# Rule 30: light cones and the block tree

The locality facts behind space-efficient evaluation of the center column.

* `evol_window`: the cell at position `p` and time `t` depends only on the initial cells in
  `[p - t, p + t]`.
* `block_step`: cut the rows into space blocks of width `b` (`block`) and the time axis into steps
  of `b`. Block `j` at time `(k + 1) b` is a fixed function, `blockStep b`, of the blocks `j - 1`,
  `j` and `j + 1` at time `k b`.
* `center_eq_root`: so the center cell at time `m b` is the first entry of the node `(m, 0)` of a
  dependency graph of height `m` and fan-in `3`, whose nodes are `b`-bit blocks and whose sources
  are blocks of the initial row.

This is the shape that R. Williams's block-respecting simulation ("Simulating Time with Square-Root
Space", STOC 2025) passes to the tree evaluation algorithm of J. Cook and I. Mertz (STOC 2024).
Tree evaluation needs about `(h + v) log v` bits for height `h` and node size `v`; here `h = n / b`
and `v = b`, so `b ≈ √n` gives the center cell at time `n` in about `√n · log n` bits of memory. Neither algorithm is formalized here. Nothing in this module is specific to rule 30
beyond its radius `1`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30LightCone

open Rule30Realization (evol)
open Rule30ZeroBoundaryBarriers (evol_local evol_restart evol_shift_all)

/-- **The light cone.** The cell at position `p` and time `t` depends only on the initial cells in
`[p - t, p + t]`. -/
theorem evol_window {x x' : Int → Bool} {t : Nat} {p : Int}
    (h : ∀ q, p - t ≤ q → q ≤ p + t → x' q = x q) : evol x' t p = evol x t p :=
  evol_local h t p (by omega) (by omega)

/-- Space block `j` of width `b`: the cells `j b, …, j b + b - 1` of the row `x`. -/
def block (b : Nat) (x : Int → Bool) (j : Int) : List Bool :=
  (List.range b).map fun i : Nat => x (j * b + (i : Int))

/-- The row made of three blocks: `l` on `[-b, 0)`, `m` on `[0, b)` and `r` on `[b, 2 b)`, white
elsewhere. -/
def assemble (b : Nat) (l m r : List Bool) (p : Int) : Bool :=
  if p < -(b : Int) then false
  else if p < 0 then l.getD (p + b).toNat false
  else if p < b then m.getD p.toNat false
  else if p < 2 * b then r.getD (p - b).toNat false
  else false

/-- One time block: the middle block after `b` steps from three adjacent blocks. -/
def blockStep (b : Nat) (l m r : List Bool) : List Bool := block b (evol (assemble b l m r) b) 0

theorem getD_block (b : Nat) (x : Int → Bool) (j : Int) {i : Nat} (hi : i < b) :
    (block b x j).getD i false = x (j * b + i) := by
  simp [block, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- `assemble` reproduces the row around block `j`, translated to block `0`. -/
theorem assemble_blocks (b : Nat) (y : Int → Bool) (j : Int) (q : Int) (h1 : -(b : Int) ≤ q)
    (h2 : q ≤ 2 * b - 1) :
    assemble b (block b y (j - 1)) (block b y j) (block b y (j + 1)) q = y (q + j * b) := by
  unfold assemble
  rw [ite_eq_right (by omega)]
  by_cases hq0 : q < 0
  · rw [ite_eq_left hq0, getD_block b y _ (by omega)]
    congr 1
    rw [Int.toNat_of_nonneg (by omega), Int.sub_mul]
    omega
  · rw [ite_eq_right hq0]
    by_cases hqb : q < b
    · rw [ite_eq_left hqb, getD_block b y _ (by omega), Int.toNat_of_nonneg (by omega)]
      congr 1
      omega
    · rw [ite_eq_right hqb, ite_eq_left (by omega), getD_block b y _ (by omega)]
      congr 1
      rw [Int.toNat_of_nonneg (by omega), Int.add_mul]
      omega

/-- **Each node of the block tree has three parents**: block `j` at time `(k + 1) b` is
`blockStep b` of the blocks `j - 1`, `j`, `j + 1` at time `k b`. -/
theorem block_step (b : Nat) (x : Int → Bool) (k : Nat) (j : Int) :
    block b (fun p => evol x ((k + 1) * b) p) j =
      blockStep b (block b (fun p => evol x (k * b) p) (j - 1))
        (block b (fun p => evol x (k * b) p) j) (block b (fun p => evol x (k * b) p) (j + 1)) := by
  let y : Int → Bool := fun p => evol x (k * b) p
  have key : ∀ i : Nat, i < b →
      evol (assemble b (block b y (j - 1)) (block b y j) (block b y (j + 1))) b (0 * b + i) =
        evol x ((k + 1) * b) (j * b + i) := by
    intro i hi
    have hz := evol_local (x := fun q => y (q + j * b))
      (x' := assemble b (block b y (j - 1)) (block b y j) (block b y (j + 1)))
      (a := -(b : Int)) (b := 2 * b - 1)
      (fun q h1 h2 => assemble_blocks b y j q h1 h2) b (0 * b + i) (by omega) (by omega)
    have hs := evol_shift_all (x := y) (x' := fun q => y (q + j * b)) (d := -(j * b))
      (fun p => by show y (p + -(j * b) + j * b) = y p; congr 1; omega) b (j * b + i)
    rw [show (j * b + (i : Int)) + -(j * b) = 0 * b + i by omega] at hs
    have hr : evol y b (j * b + i) = evol x ((k + 1) * b) (j * b + i) := by
      rw [show (k + 1) * b = k * b + b by rw [Nat.succ_mul]]
      exact evol_restart x (k * b) b (j * b + i)
    exact hz.trans (hs.trans hr)
  unfold blockStep
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact (key i hi).symm

/-- **The center cell is the root of the block tree**: at time `m b` it is the first entry of
block `0`. -/
theorem center_eq_root (b m : Nat) (hb : 0 < b) (x : Int → Bool) :
    evol x (m * b) 0 = (block b (fun p => evol x (m * b) p) 0).getD 0 false := by
  rw [getD_block b _ 0 hb]
  simp

/-! ## 1. Left-Edge Sensitivity and Right-Edge White-Corridor Condition of `evol` -/

open Rule30Jen (rule)

/-- **No Boolean Fixed Point of Negation (`bool_eq_not_false`):** no Boolean `b` satisfies
`b = !b`. -/
theorem bool_eq_not_false (b : Bool) (h : b = !b) : False := by
  cases b <;> contradiction

/-- **Left-Permutivity of `rule` (`rule_flip_left`):** flipping the left input of `rule`
unconditionally flips the output. -/
theorem rule_flip_left (a b c : Bool) : rule (!a) b c = !rule a b c := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **Right-Input Flip Criterion of `rule` (`rule_flip_right_iff`):** flipping the right input of
`rule` flips the output if and only if the center input `b` is `false`. -/
theorem rule_flip_right_iff (a b c : Bool) :
    (rule a b (!c) = !rule a b c) ↔ b = false := by
  cases a <;> cases b <;> cases c <;> decide

/-- **Universal Left-Edge Sensitivity of `evol` (`evol_flip_leftmost`):** for every `t : Nat`,
`p : Int`, and configurations `x x' : Int → Bool`, if `x'` agrees with `x` on `(p - t, p + t]` and
flips the leftmost light-cone cell `x' (p - t) = !x (p - t)`, then `evol x' t p = !evol x t p`. -/
theorem evol_flip_leftmost {x x' : Int → Bool} : ∀ (t : Nat) (p : Int),
    (∀ q, p - t < q → q ≤ p + t → x' q = x q) →
    x' (p - t) = !x (p - t) →
    evol x' t p = !evol x t p
  | 0, p, _, hflip => by
    simpa [evol, Int.sub_zero] using hflip
  | t + 1, p, hag, hflip => by
    have hL : evol x' t (p - 1) = !evol x t (p - 1) :=
      evol_flip_leftmost t (p - 1)
        (fun q h1 h2 => hag q (by omega) (by omega))
        (by rw [show p - 1 - (t : Int) = p - ((t + 1 : Nat) : Int) by omega]; exact hflip)
    have hM : evol x' t p = evol x t p :=
      evol_window (fun q h1 h2 => hag q (by omega) (by omega))
    have hR : evol x' t (p + 1) = evol x t (p + 1) :=
      evol_window (fun q h1 h2 => hag q (by omega) (by omega))
    change rule (evol x' t (p - 1)) (evol x' t p) (evol x' t (p + 1)) =
      !rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1))
    rw [hL, hM, hR, rule_flip_left]

/-- **Right-Edge White-Corridor Sensitivity of `evol` (`evol_flip_rightmost_iff`):** if `x'` agrees
with `x` on `[p - t, p + t)` and flips the rightmost light-cone cell `x' (p + t) = !x (p + t)`, then
`evol x' t p = !evol x t p` if and only if the right-boundary sub-diagonal
`evol x s (p + t - 1 - s)` is `false` for every `0 ≤ s < t`. -/
theorem evol_flip_rightmost_iff {x x' : Int → Bool} : ∀ (t : Nat) (p : Int),
    (∀ q, p - t ≤ q → q < p + t → x' q = x q) →
    x' (p + t) = !x (p + t) →
    (evol x' t p = !evol x t p ↔ ∀ s, s < t → evol x s (p + t - 1 - s) = false)
  | 0, p, _, hflip => by
    simpa [evol, Int.add_zero] using hflip
  | t + 1, p, hag, hflip => by
    have hL : evol x' t (p - 1) = evol x t (p - 1) :=
      evol_window (fun q h1 h2 => hag q (by omega) (by omega))
    have hM : evol x' t p = evol x t p :=
      evol_window (fun q h1 h2 => hag q (by omega) (by omega))
    have ih := evol_flip_rightmost_iff t (p + 1)
      (fun q h1 h2 => hag q (by omega) (by omega))
      (by rw [show p + 1 + (t : Int) = p + ((t + 1 : Nat) : Int) by omega]; exact hflip)
    change (rule (evol x' t (p - 1)) (evol x' t p) (evol x' t (p + 1)) =
      !rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1))) ↔ _
    rw [hL, hM]
    constructor
    · intro hstep s hs
      by_cases hst : s < t
      · have hR : evol x' t (p + 1) = !evol x t (p + 1) := by
          revert hstep
          cases evol x t (p - 1) <;> cases evol x t p <;>
            cases evol x' t (p + 1) <;> cases evol x t (p + 1) <;> decide
        have hsub := ih.mp hR s hst
        rwa [show p + 1 + (t : Int) - 1 - (s : Int) =
          p + ((t + 1 : Nat) : Int) - 1 - (s : Int) by omega] at hsub
      · obtain rfl : s = t := by omega
        rw [show p + ((s + 1 : Nat) : Int) - 1 - (s : Int) = p by omega]
        revert hstep
        cases evol x s (p - 1) <;> cases evol x s p <;>
          cases evol x' s (p + 1) <;> cases evol x s (p + 1) <;> decide
    · intro hall
      have hR : evol x' t (p + 1) = !evol x t (p + 1) := by
        apply ih.mpr
        intro s hs
        rw [show p + 1 + (t : Int) - 1 - (s : Int) =
          p + ((t + 1 : Nat) : Int) - 1 - (s : Int) by omega]
        exact hall s (by omega)
      have hM0 : evol x t p = false := by
        have h := hall t (by omega)
        rwa [show p + ((t + 1 : Nat) : Int) - 1 - (t : Int) = p by omega] at h
      rw [hR, hM0]
      exact (rule_flip_right_iff _ false _).mpr rfl

/-! ## 2. Triangular Left-Permutivity and Left-Parent Injectivity of `blockStep` -/

/-- **Left-Block Readout of `assemble` (`assemble_left`):** for `i < b`, position `(i : Int) - b` of
`assemble b l m r` is `l.getD i false`. -/
theorem assemble_left (b : Nat) (l m r : List Bool) {i : Nat} (hi : i < b) :
    assemble b l m r ((i : Int) - b) = l.getD i false := by
  unfold assemble
  rw [ite_eq_right (by omega), ite_eq_left (by omega),
    show ((i : Int) - b + b).toNat = i by omega]

/-- **Agreement of `assemble` Above Left-Block Index `i` (`assemble_eq_of_gt`):** if `l₁` and `l₂`
agree at all indices `k` with `i < k < b`, then `assemble b l₁ m r` and `assemble b l₂ m r` agree at
every position `q > (i : Int) - b`. -/
theorem assemble_eq_of_gt (b : Nat) (l₁ l₂ m r : List Bool) (i : Nat)
    (hag : ∀ k, i < k → k < b → l₁.getD k false = l₂.getD k false)
    (q : Int) (hq : (i : Int) - b < q) :
    assemble b l₁ m r q = assemble b l₂ m r q := by
  unfold assemble
  by_cases h1 : q < -(b : Int)
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : q < 0
    · rw [ite_eq_left h2, ite_eq_left h2]
      exact hag (q + b).toNat (by omega) (by omega)
    · rw [ite_eq_right h2, ite_eq_right h2]

/-- **Strict Upper-Triangular Independence on the Left Block (`blockStep_getD_gt_congr`):** for
`i < j < b`, if `l₁` and `l₂` agree on `(i, b)`, then `(blockStep b l₁ m r).getD j false` equals
`(blockStep b l₂ m r).getD j false`. -/
theorem blockStep_getD_gt_congr (b : Nat) (l₁ l₂ m r : List Bool) {i j : Nat}
    (hij : i < j) (hjb : j < b)
    (hag : ∀ k, i < k → k < b → l₁.getD k false = l₂.getD k false) :
    (blockStep b l₁ m r).getD j false = (blockStep b l₂ m r).getD j false := by
  unfold blockStep
  rw [getD_block b _ 0 hjb, getD_block b _ 0 hjb]
  exact evol_window fun q h1 _ => assemble_eq_of_gt b l₁ l₂ m r i hag q (by omega)

/-- **Pivot Flip on the Left Block (`blockStep_getD_flip_pivot`):** for `i < b`, if `l₁` and `l₂`
agree on `(i, b)` and `l₂.getD i false = !l₁.getD i false`, then
`(blockStep b l₂ m r).getD i false = !(blockStep b l₁ m r).getD i false`. -/
theorem blockStep_getD_flip_pivot (b : Nat) (l₁ l₂ m r : List Bool) {i : Nat} (hib : i < b)
    (hag : ∀ k, i < k → k < b → l₁.getD k false = l₂.getD k false)
    (hflip : l₂.getD i false = !l₁.getD i false) :
    (blockStep b l₂ m r).getD i false = !(blockStep b l₁ m r).getD i false := by
  unfold blockStep
  rw [getD_block b _ 0 hib, getD_block b _ 0 hib, Int.zero_mul, Int.zero_add]
  apply evol_flip_leftmost b (i : Int)
  · intro q h1 _
    exact (assemble_eq_of_gt b l₁ l₂ m r i hag q h1).symm
  · rw [assemble_left b l₂ m r hib, assemble_left b l₁ m r hib, hflip]

/-- **Downward Induction from Upper-Triangular Pivot Flip (`left_block_getD_eq_of_blockStep_eq`):**
if `blockStep b l₁ m r = blockStep b l₂ m r`, then `l₁.getD i false = l₂.getD i false` for all
`i < b`. -/
theorem left_block_getD_eq_of_blockStep_eq (b : Nat) (l₁ l₂ m r : List Bool)
    (heq : blockStep b l₁ m r = blockStep b l₂ m r) :
    ∀ d, d ≤ b → ∀ i, b - d ≤ i → i < b → l₁.getD i false = l₂.getD i false
  | 0, _, i, h1, h2 => by omega
  | d + 1, hd, i, h1, h2 => by
    have ih := left_block_getD_eq_of_blockStep_eq b l₁ l₂ m r heq d (by omega)
    by_cases hgt : b - d ≤ i
    · exact ih i hgt h2
    · cases hbit : (l₁.getD i false == l₂.getD i false) with
      | true => exact eq_of_beq hbit
      | false =>
        have hflip : l₂.getD i false = !l₁.getD i false := by
          revert hbit; cases l₁.getD i false <;> cases l₂.getD i false <;> decide
        have hpiv := blockStep_getD_flip_pivot b l₁ l₂ m r h2
          (fun k hk1 hk2 => ih k (by omega) hk2) hflip
        rw [heq] at hpiv
        exact False.elim (bool_eq_not_false _ hpiv)

/-- **Helper: List Equality from `getD` Agreement (`list_eq_of_length_eq_of_getD`):** two lists of
equal length `b` that have identical `getD i false` for all `i < b` are equal. -/
theorem list_eq_of_length_eq_of_getD {l₁ l₂ : List Bool} {b : Nat}
    (hl₁ : l₁.length = b) (hl₂ : l₂.length = b)
    (hget : ∀ i, i < b → l₁.getD i false = l₂.getD i false) :
    l₁ = l₂ := by
  apply List.ext_getElem (hl₁.trans hl₂.symm)
  intro i hi₁ hi₂
  have h := hget i (hl₁ ▸ hi₁)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂] using h

/-- **Left-Parent Injectivity of `blockStep` (`blockStep_left_injective`):** for every block width
`b` and any middle and right parent blocks `m, r : List Bool`, `blockStep b · m r` is injective on
left parent blocks `l₁, l₂` of length `b`. -/
theorem blockStep_left_injective (b : Nat) {l₁ l₂ : List Bool} (m r : List Bool)
    (hl₁ : l₁.length = b) (hl₂ : l₂.length = b)
    (heq : blockStep b l₁ m r = blockStep b l₂ m r) :
    l₁ = l₂ :=
  list_eq_of_length_eq_of_getD hl₁ hl₂ fun i hi =>
    left_block_getD_eq_of_blockStep_eq b l₁ l₂ m r heq b (Nat.le_refl b) i (by omega) hi

/-! ## 3. Multi-Level Block-Tree Leftmost Leaf Injectivity and Root Sensitivity -/

/-- **Length of `block` (`length_block`):** every space block `block b x j` has length `b`. -/
theorem length_block (b : Nat) (x : Int → Bool) (j : Int) :
    (block b x j).length = b := by
  simp [block]

/-- **Multi-Level Root Pivot Flip from the Leftmost Leaf Block (`root_block_getD_flip_leftmost`):**
at tree height `m`, if `x'` agrees with `x` on `(i - m * b, i + m * b]` for `i < b` and flips entry
`i` of the leftmost leaf block `block b x (-m)`, then entry `i` of the root block at time `m * b`
flips. -/
theorem root_block_getD_flip_leftmost (b m : Nat) {x x' : Int → Bool} {i : Nat} (hib : i < b)
    (hag : ∀ q : Int, (i : Int) - (m * b : Nat) < q → q ≤ (i : Int) + (m * b : Nat) → x' q = x q)
    (hflip : (block b x' (-(m : Int))).getD i false = !(block b x (-(m : Int))).getD i false) :
    (block b (fun p => evol x' (m * b) p) 0).getD i false =
      !(block b (fun p => evol x (m * b) p) 0).getD i false := by
  rw [getD_block b _ 0 hib, getD_block b _ 0 hib, Int.zero_mul, Int.zero_add]
  rw [getD_block b x' (-(m : Int)) hib, getD_block b x (-(m : Int)) hib] at hflip
  apply evol_flip_leftmost (m * b) (i : Int) hag
  have hidx : (i : Int) - ((m * b : Nat) : Int) = -(m : Int) * (b : Int) + (i : Int) := by
    rw [Int.natCast_mul, Int.neg_mul]; omega
  rw [hidx]
  exact hflip

/-- **Multi-Level Leftmost Leaf-Block Injectivity (`root_block_leftmost_leaf_injective`):** at any
tree height `m`, if two initial configurations `x, x'` agree on `[-(m - 1) * b, m * b + b)` and
produce the same root block `block b (fun p => evol · (m * b) p) 0` at time `m * b`, then their
leftmost leaf blocks `block b x (-m)` and `block b x' (-m)` are identical. -/
theorem root_block_leftmost_leaf_injective (b m : Nat) {x x' : Int → Bool}
    (hmid : ∀ q : Int, -(m : Int) * b + b ≤ q → q < (m * b : Nat) + b → x' q = x q)
    (hroot : block b (fun p => evol x (m * b) p) 0 = block b (fun p => evol x' (m * b) p) 0) :
    block b x (-(m : Int)) = block b x' (-(m : Int)) := by
  have hstep : ∀ d, d ≤ b → ∀ i, b - d ≤ i → i < b →
      (block b x (-(m : Int))).getD i false = (block b x' (-(m : Int))).getD i false := by
    intro d
    induction d with
    | zero => intro _ i h1 h2; omega
    | succ d ih =>
      intro hd i h1 h2
      by_cases hgt : b - d ≤ i
      · exact ih (by omega) i hgt h2
      · cases hbit : ((block b x (-(m : Int))).getD i false == (block b x' (-(m : Int))).getD i false) with
        | true => exact eq_of_beq hbit
        | false =>
          have hflip : (block b x' (-(m : Int))).getD i false = !(block b x (-(m : Int))).getD i false := by
            revert hbit
            cases (block b x (-(m : Int))).getD i false <;>
              cases (block b x' (-(m : Int))).getD i false <;> decide
          have hpiv := root_block_getD_flip_leftmost b m h2
            (fun q hq1 hq2 => by
              by_cases hqb : q < -(m : Int) * b + b
              · have hk : (q - -(m : Int) * b).toNat < b := by omega
                have hgt_k : b - d ≤ (q - -(m : Int) * b).toNat := by
                  have : (i : Int) - ((m * b : Nat) : Int) = -(m : Int) * b + i := by
                    rw [Int.natCast_mul, Int.neg_mul]; omega
                  omega
                have heq_k := ih (by omega) (q - -(m : Int) * b).toNat hgt_k hk
                rw [getD_block b x (-(m : Int)) hk, getD_block b x' (-(m : Int)) hk,
                  Int.toNat_of_nonneg (by omega)] at heq_k
                simpa [show -(m : Int) * b + (q - -(m : Int) * b) = q by omega] using heq_k.symm
              · exact hmid q (by omega) (by omega))
            hflip
          rw [hroot] at hpiv
          exact False.elim (bool_eq_not_false _ hpiv)
  exact list_eq_of_length_eq_of_getD (length_block b x _) (length_block b x' _) fun i hi =>
    hstep b (Nat.le_refl b) i (by omega) hi

end Rule30LightCone
end Ruliology.CellularAutomata
