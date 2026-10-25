module

public import Ruliology.CellularAutomata.Rule30Ether

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

open Rule30Jen Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ### A computable row model for the driven right half -/

/-- The single-cell right half at position `p`. -/
def delta (p : Nat) : Nat → Bool := fun q => decide (q = p)

/-- The same, indexed from `0` for column `1`. -/
def deltaR (p : Nat) : Nat → Bool := fun i => delta p (i + 1)

theorem delta_eq_false {p i : Nat} (h : i ≠ p) : delta p i = false := by
  unfold delta; exact decide_eq_false_iff_not.2 h

/-- One step of a strip whose right neighbour is white. -/
def rowStep (c0 : Bool) (row : List Bool) : List Bool :=
  lin3 (c0 :: (row ++ [false]))

/-- Iterated row step. -/
def iterRow (c : Nat → Bool) : Nat → List Bool → List Bool
  | 0, row => row
  | n + 1, row => rowStep (c n) (iterRow c n row)

/-- Width used by the finite checker. -/
def Bof (p t k : Nat) : Nat := max (p + t + 2) (k + 13)

/-- The simulated row at time `t`. -/
def rowOfB (p φ t k : Nat) : List Bool :=
  iterRow (fun n => wordAt w0001 (n + φ)) t (seg (deltaR p) (Bof p t k))

/-- Boolean check of `InFamily` for ether alignment `(j0, 0)` and phase `φ`, at time `t`,
with column `k` a B3.  Only alignments `j0 = 5, 6` are accepted. -/
def famBAt (j0 p φ t k : Nat) : Bool :=
  let row := rowOfB p φ t k
  ((j0 + k) % 7 == 2) && (j0 == 5 || j0 == 6) &&
  (List.range k).all (fun i => row.getD i false == ether (j0 + i + 1) (t + φ)) &&
  wallStates.contains (((t + φ) % 4, (List.range 13).map (fun i => row.getD (k + i) false)))

theorem seg_getD (f : Nat → Bool) : ∀ (n i : Nat), i < n → (seg f n).getD i false = f i
  | 0, i, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    show (seg (fun j => f (j + 1)) n).getD i false = f (i + 1)
    exact seg_getD (fun j => f (j + 1)) n i (by omega)

theorem rowOf_getD (F : Nat → Nat → Bool) (t k b i : Nat) (hi : i < b) :
    (rowOf F t k b).getD i false = F t (k + i + 1) := by
  unfold rowOf
  exact seg_getD (fun j => F t (k + j + 1)) b i hi

theorem seg_eq_map_range (f : Nat → Bool) (n : Nat) :
    seg f n = (List.range n).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [seg_succ, ih]
    rw [List.range_succ, List.map_append]
    rfl

theorem rowOf_eq_map (F : Nat → Nat → Bool) (t k b : Nat) :
    rowOf F t k b = (List.range b).map (fun i => F t (k + i + 1)) := by
  unfold rowOf
  exact seg_eq_map_range _ _

/-! ### Light cone and the driven recurrence -/

theorem drv_false_of_gt (c x : Nat → Bool) (p : Nat)
    (hx : ∀ i, p < i → x i = false) : ∀ (t q : Nat), p + t < q → drv c x t q = false := by
  intro t
  induction t with
  | zero =>
    intro q hq
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [drv_init c x (q' + 1) (by omega)]
    exact hx (q' + 1) (by omega)
  | succ t ih =>
    intro q hq
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    show rule (drv c x t q') (drv c x t (q' + 1)) (drv c x t (q' + 2)) = false
    rw [ih q' (by omega), ih (q' + 1) (by omega), ih (q' + 2) (by omega)]
    rfl

theorem rowOf_iter (c x : Nat → Bool) (p T b : Nat)
    (hx : ∀ i, p < i → x i = false) (hb : p + T < b) :
    ∀ t, t ≤ T →
      rowOf (drv c x) t 0 b = iterRow c t (seg (fun i => x (i + 1)) b) := by
  intro t ht
  induction t with
  | zero =>
    unfold rowOf iterRow
    apply seg_congr
    intro i _
    rw [show 0 + i + 1 = i + 1 by omega, drv_init c x (i + 1) (by omega)]
  | succ t ih =>
    have htT : t ≤ T := by omega
    have hfalse : drv c x t (b + 1) = false := by
      exact drv_false_of_gt c x p hx t (b + 1) (by omega)
    rw [rowOf_succ (drv_isR30 c x) t 0 b, drv_col0, ih htT,
      show 0 + b + 1 = b + 1 by omega, hfalse]
    rfl

/-! ### Agreement and family transfer -/

theorem drv_agree (c x y : Nat → Bool) (q t : Nat) (hq : 1 ≤ q)
    (h : ∀ i, 1 ≤ i → q - t ≤ i → i ≤ q + t → x i = y i) :
    drv c x t q = drv c y t q := by
  induction t generalizing q with
  | zero =>
    rw [drv_init c x q hq, drv_init c y q hq]
    exact h q hq (by omega) (by omega)
  | succ t ih =>
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    show rule (drv c x t q') (drv c x t (q' + 1)) (drv c x t (q' + 2)) =
      rule (drv c y t q') (drv c y t (q' + 1)) (drv c y t (q' + 2))
    have harg : ∀ r, q' ≤ r → r ≤ q' + 2 → drv c x t r = drv c y t r := by
      intro r hr1 hr2
      rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · subst r
        rw [drv_col0, drv_col0]
      · exact ih r hrpos (fun i hi1 hi2 hi3 => h i hi1 (by omega) (by omega))
    rw [harg q' (by omega) (by omega), harg (q' + 1) (by omega) (by omega),
      harg (q' + 2) (by omega) (by omega)]

theorem InFamily_congr_at {F G : Nat → Nat → Bool} {j0 s t k : Nat}
    (hk : (j0 + k) % 7 = 2)
    (hE : ∀ p, 1 ≤ p → p ≤ k → F t p = ether (j0 + p) (t + s))
    (hW : ((t + s) % 4, rowOf F t k 13) ∈ wallStates)
    (h : ∀ p, 1 ≤ p → p ≤ k + 13 → F t p = G t p) :
    InFamily G j0 s t := by
  refine ⟨k, hk, ?_, ?_⟩
  · intro p hp1 hpk
    rw [← h p hp1 (by omega)]
    exact hE p hp1 hpk
  · have hrow : rowOf F t k 13 = rowOf G t k 13 := by
      unfold rowOf
      apply seg_congr
      intro i hi
      exact h (k + i + 1) (by omega) (by omega)
    rwa [hrow] at hW

theorem InFamily_phase_congr {F : Nat → Nat → Bool} {j0 s s' t : Nat}
    (hss : s % 4 = s' % 4) : InFamily F j0 s t ↔ InFamily F j0 s' t := by
  constructor
  · intro h
    obtain ⟨k, hk, hE, hW⟩ := h
    refine ⟨k, hk, ?_, ?_⟩
    · intro p hp1 hpk
      rw [hE p hp1 hpk]
      exact ether_congr rfl (by omega)
    · rw [show (t + s') % 4 = (t + s) % 4 by omega]
      exact hW
  · intro h
    obtain ⟨k, hk, hE, hW⟩ := h
    refine ⟨k, hk, ?_, ?_⟩
    · intro p hp1 hpk
      rw [hE p hp1 hpk]
      exact ether_congr rfl (by omega)
    · rw [show (t + s) % 4 = (t + s') % 4 by omega]
      exact hW

theorem drv_phase_congr (c c' : Nat → Bool) (x : Nat → Bool) (h : ∀ t, c t = c' t) :
    drv c x = drv c' x := by
  funext t q
  induction t generalizing q with
  | zero =>
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst q; rw [drv_col0, drv_col0, h 0]
    · rw [drv_init c x q hq, drv_init c' x q hq]
  | succ t ih =>
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst q; rw [drv_col0, drv_col0, h (t + 1)]
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      show rule (drv c x t q') (drv c x t (q' + 1)) (drv c x t (q' + 2)) =
        rule (drv c' x t q') (drv c' x t (q' + 1)) (drv c' x t (q' + 2))
      rw [ih q', ih (q' + 1), ih (q' + 2)]

/-! ### Soundness of the Boolean family check -/

theorem famBAt_data {j0 p φ t k : Nat} (h : famBAt j0 p φ t k = true) :
    (j0 + k) % 7 = 2 ∧
    (∀ q, 1 ≤ q → q ≤ k →
      drv (fun n => wordAt w0001 (n + φ)) (delta p) t q = ether (j0 + q) (t + φ)) ∧
    ((t + φ) % 4, rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta p)) t k 13) ∈ wallStates := by
  let B := Bof p t k
  have hx : ∀ i, p < i → delta p i = false := fun i hi => delta_eq_false (by omega)
  have hb : p + t < B := by dsimp [B, Bof]; omega
  have hrow : rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta p)) t 0 B = rowOfB p φ t k := by
    unfold rowOfB
    exact rowOf_iter _ _ p t B hx hb t (Nat.le_refl t)
  unfold famBAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hk, hjok⟩, hE⟩, hW⟩ := h
  refine ⟨beq_iff_eq.1 hk, ?_, ?_⟩
  · intro q hq1 hqk
    have hqB : q - 1 < B := by dsimp [B, Bof]; omega
    have hmem := List.all_eq_true.1 hE (q - 1) (List.mem_range.2 (by omega))
    have hqrow : (rowOfB p φ t k).getD (q - 1) false =
        ether (j0 + (q - 1) + 1) (t + φ) := beq_iff_eq.1 hmem
    rw [← hrow] at hqrow
    rw [rowOf_getD _ _ _ _ _ hqB] at hqrow
    rw [show 0 + (q - 1) + 1 = q by omega] at hqrow
    rw [hqrow]
    exact ether_congr (by omega) (by omega)
  · have hwall : (List.range 13).map (fun i => (rowOfB p φ t k).getD (k + i) false) =
        rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta p)) t k 13 := by
      calc
        (List.range 13).map (fun i => (rowOfB p φ t k).getD (k + i) false)
            = (List.range 13).map
                (fun i => (rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta p)) t 0 B).getD
                  (k + i) false) := by rw [hrow]
        _ = (List.range 13).map
                (fun i => (drv (fun n => wordAt w0001 (n + φ)) (delta p)) t (k + i + 1)) := by
              apply List.map_congr_left
              intro i hi
              have hik : k + i < B := by
                have hi13 : i < 13 := List.mem_range.1 hi
                dsimp [B, Bof]; omega
              rw [rowOf_getD _ _ _ _ _ hik]
              congr 1
              omega
        _ = rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta p)) t k 13 := by
              rw [rowOf_eq_map]
    rw [← hwall]
    exact List.contains_iff_mem.1 hW

theorem famBAt_sound {j0 p φ t k : Nat} (h : famBAt j0 p φ t k = true) :
    InFamily (drv (fun n => wordAt w0001 (n + φ)) (delta p)) j0 φ t := by
  obtain ⟨hk, hE, hW⟩ := famBAt_data h
  exact ⟨k, hk, hE, hW⟩


theorem delta_eq {p : Nat} {x : Nat → Bool} (hx : x p = true)
    (hx' : ∀ q, q ≠ p → x q = false) : x = delta p := by
  funext q
  by_cases hq : q = p
  · subst q
    rw [hx]
    unfold delta
    simp
  · rw [hx' q hq]
    unfold delta
    exact (decide_eq_false_iff_not.2 hq).symm

theorem allWhite_data (φ : Nat) (hφ : φ < 4) :
    (∀ q, 1 ≤ q → q ≤ 3 →
      drv (fun n => wordAt w0001 (n + φ)) (delta 0) (14 - φ) q = ether (6 + q) 14) ∧
    ((14 % 4, rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta 0)) (14 - φ) 3 13) ∈ wallStates) := by
  have hcases : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa using (famBAt_data (j0 := 6) (p := 0) (φ := 0) (t := 14) (k := 3) (by decide)).2
  · simpa using (famBAt_data (j0 := 6) (p := 0) (φ := 1) (t := 13) (k := 3) (by decide)).2
  · simpa using (famBAt_data (j0 := 6) (p := 0) (φ := 2) (t := 12) (k := 3) (by decide)).2
  · simpa using (famBAt_data (j0 := 6) (p := 0) (φ := 3) (t := 11) (k := 3) (by decide)).2

theorem large_case {x : Nat → Bool} {p φ : Nat} (hp : 31 ≤ p) (hx' : ∀ q, q ≠ p → x q = false) (hφ : φ < 4) :
    InFamily (drv (fun n => wordAt w0001 (n + φ)) x) 6 φ (14 - φ) := by
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
    intro i hi1 hilo hihi
    have hine : i ≠ p := by omega
    rw [show delta 0 i = false from delta_eq_false (by omega), hx' i hine]
