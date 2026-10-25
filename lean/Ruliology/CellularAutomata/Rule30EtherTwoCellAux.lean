module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Ether

open Rule30Jen Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ### The two-cell right half -/

/-- The right half with black cells at `p` and `q` and all other cells white. -/
def delta2 (p q : Nat) : Nat → Bool := fun r => decide (r = p ∨ r = q)

theorem delta2_eq_false {p q i : Nat} (h : i ≠ p) (h2 : i ≠ q) : delta2 p q i = false := by
  unfold delta2
  exact decide_eq_false_iff_not.2 (by omega)

theorem delta2_pos {p q : Nat} : delta2 p q p = true := by
  unfold delta2; simp

theorem delta2_neg {p q : Nat} : delta2 p q q = true := by
  unfold delta2; simp

theorem delta2_of_ne {p q i : Nat} (h : i ≠ p) (h2 : i ≠ q) : delta2 p q i = false :=
  delta2_eq_false h h2

/-- The same, indexed from `0` for column `1`. -/
def deltaR2 (p q : Nat) : Nat → Bool := fun i => delta2 p q (i + 1)

/-- Width used by the finite checker. -/
def Bof2 (p q t k : Nat) : Nat := max (max p q + t + 2) (k + 13)

/-- The simulated row at time `t`. -/
def rowOfB2 (p q φ t k : Nat) : List Bool :=
  iterRow (fun n => wordAt w0001 (n + φ)) t (seg (deltaR2 p q) (Bof2 p q t k))

/-- Boolean check of `InFamily` for the two-cell right half. -/
def famBAt2 (j0 p q φ t k : Nat) : Bool :=
  let row := rowOfB2 p q φ t k
  ((j0 + k) % 7 == 2) && (j0 == 5 || j0 == 6) &&
  (List.range k).all (fun i => row.getD i false == ether (j0 + i + 1) (t + φ)) &&
  wallStates.contains (((t + φ) % 4, (List.range 13).map (fun i => row.getD (k + i) false)))

theorem famBAt2_data {j0 p q φ t k : Nat} (h : famBAt2 j0 p q φ t k = true) :
    (j0 + k) % 7 = 2 ∧
    (∀ r, 1 ≤ r → r ≤ k →
      drv (fun n => wordAt w0001 (n + φ)) (delta2 p q) t r = ether (j0 + r) (t + φ)) ∧
    ((t + φ) % 4, rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) t k 13) ∈ wallStates := by
  let B := Bof2 p q t k
  have hx : ∀ i, max p q < i → delta2 p q i = false :=
    fun i hi => delta2_eq_false (by omega) (by omega)
  have hb : max p q + t < B := by dsimp [B, Bof2]; omega
  have hrow : rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) t 0 B = rowOfB2 p q φ t k := by
    unfold rowOfB2
    exact rowOf_iter _ _ (max p q) t B hx hb t (Nat.le_refl t)
  unfold famBAt2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hk, hjok⟩, hE⟩, hW⟩ := h
  refine ⟨beq_iff_eq.1 hk, ?_, ?_⟩
  · intro r hr1 hrk
    have hrB : r - 1 < B := by dsimp [B, Bof2]; omega
    have hmem := List.all_eq_true.1 hE (r - 1) (List.mem_range.2 (by omega))
    have hqrow : (rowOfB2 p q φ t k).getD (r - 1) false =
        ether (j0 + (r - 1) + 1) (t + φ) := beq_iff_eq.1 hmem
    rw [← hrow] at hqrow
    rw [rowOf_getD _ _ _ _ _ hrB] at hqrow
    rw [show 0 + (r - 1) + 1 = r by omega] at hqrow
    rw [hqrow]
    exact ether_congr (by omega) (by omega)
  · have hwall : (List.range 13).map (fun i => (rowOfB2 p q φ t k).getD (k + i) false) =
        rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) t k 13 := by
      calc
        (List.range 13).map (fun i => (rowOfB2 p q φ t k).getD (k + i) false)
            = (List.range 13).map
                (fun i => (rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) t 0 B).getD
                  (k + i) false) := by rw [hrow]
        _ = (List.range 13).map
                (fun i => (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) t (k + i + 1)) := by
              apply List.map_congr_left
              intro i hi
              have hik : k + i < B := by
                have hi13 : i < 13 := List.mem_range.1 hi
                dsimp [B, Bof2]; omega
              rw [rowOf_getD _ _ _ _ _ hik]
              congr 1
              omega
        _ = rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) t k 13 := by
              rw [rowOf_eq_map]
    rw [← hwall]
    exact List.contains_iff_mem.1 hW

theorem famBAt2_sound {j0 p q φ t k : Nat} (h : famBAt2 j0 p q φ t k = true) :
    InFamily (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) j0 φ t := by
  obtain ⟨hk, hE, hW⟩ := famBAt2_data h
  exact ⟨k, hk, hE, hW⟩

theorem delta2_eq {p q : Nat} {x : Nat → Bool} (hx : x p = true)
    (hxq : x q = true) (hx' : ∀ r, r ≠ p → r ≠ q → x r = false) : x = delta2 p q := by
  funext r
  by_cases h1 : r = p
  · subst r; rw [hx]; exact delta2_pos.symm
  · by_cases h2 : r = q
    · subst r; rw [hxq]; exact delta2_neg.symm
    · rw [hx' r h1 h2]; exact (delta2_eq_false h1 h2).symm

/-- **Light cone transfer.**  If the second cell `q` is beyond the backward light cone of the
13-cell wall window at time `t` (columns up to `k + 13`), the two-cell orbit agrees with the
single-cell orbit at `p` on that window, so it inherits the family property. -/
theorem twoCell_from_single {j0 p q φ t k : Nat} (hq : k + 13 + t < q)
    (hk : (j0 + k) % 7 = 2)
    (hE : ∀ r, 1 ≤ r → r ≤ k →
      drv (fun n => wordAt w0001 (n + φ)) (delta p) t r = ether (j0 + r) (t + φ))
    (hW : ((t + φ) % 4, rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta p)) t k 13)
      ∈ wallStates) :
    InFamily (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) j0 φ t := by
  have hagree : ∀ r, 1 ≤ r → r ≤ k + 13 →
      drv (fun n => wordAt w0001 (n + φ)) (delta p) t r =
      drv (fun n => wordAt w0001 (n + φ)) (delta2 p q) t r := by
    intro r hr1 hr2
    apply drv_agree (fun n => wordAt w0001 (n + φ)) (delta p) (delta2 p q) r t hr1
    intro i hi1 hlo hhi
    have hne : i ≠ q := by omega
    by_cases hip : i = p
    · rw [hip, show delta p p = true from by unfold delta; simp, delta2_pos]
    · rw [show delta p i = false from delta_eq_false hip, delta2_eq_false hip hne]
  refine InFamily_congr_at (F := drv (fun n => wordAt w0001 (n + φ)) (delta p))
    (G := drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) (j0 := j0) (s := φ) (t := t)
    (k := k) hk hE hW hagree


/-- Two orbits whose initial right halves agree on every column `≥ 1` coincide. -/
theorem drv_congr_ge_one {c x y : Nat → Bool} (h : ∀ r, 1 ≤ r → x r = y r) :
    ∀ t r, drv c x t r = drv c y t r := by
  intro t
  induction t with
  | zero =>
    intro r
    rcases Nat.eq_zero_or_pos r with hr0 | hr
    · subst hr0
      rw [show drv c x 0 0 = c 0 from rfl, show drv c y 0 0 = c 0 from rfl]
    · rw [drv_init c x r hr, drv_init c y r hr, h r hr]
  | succ t ih =>
    intro r
    rcases Nat.eq_zero_or_pos r with hr0 | hr
    · subst hr0
      rw [drv_col0, drv_col0]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [show drv c x (t + 1) (r' + 1) =
            rule (drv c x t r') (drv c x t (r' + 1)) (drv c x t (r' + 2)) from rfl,
          show drv c y (t + 1) (r' + 1) =
            rule (drv c y t r') (drv c y t (r' + 1)) (drv c y t (r' + 2)) from rfl,
          ih r', ih (r' + 1), ih (r' + 2)]

theorem delta2_zero_left {q r : Nat} (hr : 1 ≤ r) : delta2 0 q r = delta q r := by
  unfold delta2 delta
  by_cases hq : r = q
  · subst hq; simp
  · have hr0 : r ≠ 0 := by omega
    simp [hr0, hq]

theorem drv_delta2_zero_left {c : Nat → Bool} {q : Nat} :
    drv c (delta2 0 q) = drv c (delta q) := by
  funext t r
  exact drv_congr_ge_one (fun r hr => delta2_zero_left hr) t r

/-- **Light cone transfer with an explicit reference orbit.**  If the reference two-cell orbit
(with the second cell at `r`) and the target two-cell orbit (second cell at `q`) both have their
second cell beyond the backward light cone of the wall window at time `t`, they agree on the
window and the target inherits the family property. -/
theorem twoCell_from_ref {j0 p q r φ t k : Nat} (hr : k + 13 + t < r) (hq : k + 13 + t < q)
    (hk : (j0 + k) % 7 = 2)
    (hE : ∀ s, 1 ≤ s → s ≤ k →
      drv (fun n => wordAt w0001 (n + φ)) (delta2 p r) t s = ether (j0 + s) (t + φ))
    (hW : ((t + φ) % 4, rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta2 p r)) t k 13)
      ∈ wallStates) :
    InFamily (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) j0 φ t := by
  have hagree : ∀ s, 1 ≤ s → s ≤ k + 13 →
      drv (fun n => wordAt w0001 (n + φ)) (delta2 p r) t s =
      drv (fun n => wordAt w0001 (n + φ)) (delta2 p q) t s := by
    intro s hs1 hs2
    apply drv_agree (fun n => wordAt w0001 (n + φ)) (delta2 p r) (delta2 p q) s t hs1
    intro i hi1 hlo hhi
    have hne_r : i ≠ r := by omega
    have hne_q : i ≠ q := by omega
    by_cases hip : i = p
    · rw [hip, delta2_pos, delta2_pos]
    · rw [delta2_eq_false hip hne_r, delta2_eq_false hip hne_q]
  refine InFamily_congr_at (F := drv (fun n => wordAt w0001 (n + φ)) (delta2 p r))
    (G := drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) (j0 := j0) (s := φ) (t := t)
    (k := k) hk hE hW hagree

/-- **Large-position case.**  If the initial right half is white on the columns `1 .. 30`, then at
time `14 - φ` the wall window has not seen it and the orbit is the all-white orbit there. -/
theorem large_case2 {x : Nat → Bool} {φ : Nat} (hx0 : ∀ i, 1 ≤ i → i ≤ 30 → x i = false)
    (hφ : φ < 4) : InFamily (drv (fun n => wordAt w0001 (n + φ)) x) 6 φ (14 - φ) := by
  obtain ⟨hEw, hWw⟩ := allWhite_data φ hφ
  have ht : 14 - φ + φ = 14 := by omega
  refine InFamily_congr_at (F := drv (fun n => wordAt w0001 (n + φ)) (delta 0))
    (G := drv (fun n => wordAt w0001 (n + φ)) x) (j0 := 6) (s := φ) (t := 14 - φ) (k := 3)
    (by decide) ?_ ?_ ?_
  · intro q hq1 hq3
    rw [ht]
    exact hEw q hq1 hq3
  · rw [ht]
    exact hWw
  · intro q hq1 hq16
    apply drv_agree (fun n => wordAt w0001 (n + φ)) (delta 0) x q (14 - φ) hq1
    intro i hi1 hlo hhi
    rw [show delta 0 i = false from delta_eq_false (by omega), hx0 i hi1 (by omega)]

end Rule30Ether
end Ruliology.CellularAutomata
