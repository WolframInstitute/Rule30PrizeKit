module

public import Ruliology.CellularAutomata.Rule30EtherTwoCellData
public import Ruliology.CellularAutomata.Rule30EtherSingleCell

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Ether

open Rule30Jen Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# The two-cell case of period-4 absorption for `0001`

For every two positions `p < q` and every phase `φ`, the right half with black cells at `p` and
`q` and all other cells white, driven by `0001^∞` at phase `φ`, eventually enters the
ether-and-wall family for the alignment `(5, 0)` or `(6, 0)`:

`∃ a ∈ A0001, ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1`.

This is the two-cell restriction of `Rule30Ether.Absorption w0001 A0001`, not the full
conjecture.

The proof splits on the smallest black position `p`:

* `p ≥ 31`: at time `14 - φ` the wall window `1..16` has not seen either cell, so the orbit
  agrees there with the all-white orbit (`large_case2`).
* `p = 0`: column `0` is overwritten by the driver, so the orbit is the single-cell orbit at `q`
  (`singleCell_mod`).
* `1 ≤ p ≤ 30`: if the second cell `q` is beyond the backward light cone of the wall window at
  the single-cell entry time `t1` (`q ≥ t1 + k + 14`), the two-cell orbit agrees with the
  single-cell orbit on the window and inherits the family (`twoCell_from_ref`).  The remaining
  finitely many `q` are covered by the packed finite check of `Rule30EtherTwoCellData`.
-/

/-- The finite part: the light-cone bound for the reference witness is below the reference
position `sQ`. -/
def checkBound : Bool :=
  (List.range 30).all (fun i =>
    (List.range 4).all (fun φ =>
      let d := sdata (i + 1) φ
      decide (d.2.1 + 13 + d.1 < sQ)))

theorem checkBound_ok : checkBound = true := by decide

theorem boundData (p φ : Nat) (hp1 : 1 ≤ p) (hp30 : p ≤ 30) (hφ : φ < 4) :
    (sdata p φ).2.1 + 13 + (sdata p φ).1 < sQ := by
  have h := checkBound_ok
  unfold checkBound at h
  have h1 := List.all_eq_true.1 h (p - 1) (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 h1 φ (List.mem_range.2 hφ)
  rw [show p - 1 + 1 = p by omega] at h2
  exact of_decide_eq_true h2

/-- The explicit range ends exactly at the light-cone threshold `t1 + k + 14`. -/
def checkLen : Bool :=
  (List.range 30).all (fun i =>
    (List.range 4).all (fun φ =>
      ((i + 1) + 1 + (dataAll (i + 1) φ).length ==
        max ((i + 1) + 1) ((sdata (i + 1) φ).1 + (sdata (i + 1) φ).2.1 + 14))))

theorem checkLen_ok : checkLen = true := by decide

theorem lenData (p φ : Nat) (hp1 : 1 ≤ p) (hp30 : p ≤ 30) (hφ : φ < 4) :
    p + 1 + (dataAll p φ).length =
      max (p + 1) ((sdata p φ).1 + (sdata p φ).2.1 + 14) := by
  have h := checkLen_ok
  unfold checkLen at h
  have h1 := List.all_eq_true.1 h (p - 1) (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 h1 φ (List.mem_range.2 hφ)
  rw [show p - 1 + 1 = p by omega] at h2
  exact beq_iff_eq.1 h2

/-- **The finite range `1 ≤ p ≤ 30`.** -/
theorem small_case2 (p q φ : Nat) (hp1 : 1 ≤ p) (hp30 : p ≤ 30) (hpq : p < q) (hφ : φ < 4) :
    ∃ a ∈ A0001, ∃ t1,
      InFamily (drv (fun t => wordAt w0001 (t + φ)) (delta2 p q)) a.1 (a.2 + φ) t1 := by
  by_cases hq : q < p + 1 + (dataAll p φ).length
  · -- the explicit finite range
    obtain ⟨hlen, hchk⟩ := checkAll_range p φ hp1 hp30 hφ
    obtain ⟨hmem, hIF⟩ := checkRange_sound (data := dataAll p φ) (p := p) (φ := φ) (q := q)
      hp1 hchk hpq hq
    refine ⟨(((dataAll p φ).getD (q - p - 1) (0, 6, 3)).2.2, 0), by simpa [A0001] using hmem,
      ((dataAll p φ).getD (q - p - 1) (0, 6, 3)).1, ?_⟩
    simpa using hIF
  · -- beyond the light cone: transfer from the single-cell orbit at `p`
    obtain ⟨hlen, -⟩ := checkAll_range p φ hp1 hp30 hφ
    have hs := checkSingle_range p φ hp1 hp30 hφ
    obtain ⟨hj, hk, hE, hW⟩ := famRowN_data (q := sQ) (by omega) (by unfold sQ; omega) hs
    have htb : (sdata p φ).2.1 + 13 + (sdata p φ).1 < sQ := boundData p φ hp1 hp30 hφ
    have hlen2 := lenData p φ hp1 hp30 hφ
    have hqbig : (sdata p φ).2.1 + 13 + (sdata p φ).1 < q := by
      have h1 : p + 1 + (dataAll p φ).length ≤ q := by omega
      have h2 : (sdata p φ).1 + (sdata p φ).2.1 + 14 ≤ p + 1 + (dataAll p φ).length := by
        rw [hlen2]
        exact Nat.le_max_right _ _
      omega
    refine ⟨((sdata p φ).2.2, 0), by simpa [A0001] using hj, (sdata p φ).1, ?_⟩
    simpa using twoCell_from_ref (j0 := (sdata p φ).2.2) (p := p) (q := q) (r := sQ) (φ := φ)
      (t := (sdata p φ).1) (k := (sdata p φ).2.1) htb hqbig hk hE hW

/-- **The two-cell case for a fixed phase `φ < 4`.** -/
theorem twoCell_mod (x : Nat → Bool) (p q φ : Nat) (hpq : p < q) (hx : x p = true)
    (hxq : x q = true) (hx' : ∀ r, r ≠ p → r ≠ q → x r = false) (hφ : φ < 4) :
    ∃ a ∈ A0001, ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  have hx2 : x = delta2 p q := delta2_eq hx hxq hx'
  rw [hx2]
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · -- `p = 0`: column `0` is the driver, so this is the single-cell case at `q`
    subst hp0
    rw [drv_delta2_zero_left]
    exact singleCell_mod (delta q) q φ (by unfold delta; simp)
      (fun r hr => delta_eq_false hr) hφ
  · rcases Nat.lt_or_ge p 31 with hp31 | hp31
    · exact small_case2 p q φ hp1 (by omega) hpq hφ
    · -- both cells are beyond the light cone of the window at time `14 - φ`
      have hx0 : ∀ i, 1 ≤ i → i ≤ 30 → delta2 p q i = false :=
        fun i hi1 hi30 => delta2_eq_false (by omega) (by omega)
      exact ⟨(6, 0), by decide, 14 - φ, by simpa using large_case2 (x := delta2 p q) hx0 hφ⟩

/-- **Two-cell absorption for `w = 0001`.**  For every two positions `p < q` and every phase
`φ`, the right half with black cells at `p` and `q` and all other cells white, driven by
`0001^∞` at phase `φ`, eventually enters the ether-and-wall family for the alignment `(5, 0)` or
`(6, 0)`.  This is the two-cell restriction of `Rule30Ether.Absorption w0001 A0001`, not the full
absorption conjecture. -/
theorem twoCell_absorption (x : Nat → Bool) (p q φ : Nat) (hpq : p < q) (hx : x p = true)
    (hxq : x q = true) (hx' : ∀ r, r ≠ p → r ≠ q → x r = false) :
    ∃ a ∈ A0001, ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  have hφ0 : φ % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨a, ha, t1, hIF⟩ := twoCell_mod x p q (φ % 4) hpq hx hxq hx' hφ0
  have hdrv : drv (fun t => wordAt w0001 (t + φ)) x =
      drv (fun t => wordAt w0001 (t + φ % 4)) x := by
    apply drv_phase_congr
    intro t
    unfold wordAt
    congr 1
    simp only [Nat.add_mod, Nat.mod_mod]
  have ha0 : a.2 = 0 := by
    have hmem := ha
    simp [A0001] at hmem
    rcases hmem with rfl | rfl <;> rfl
  have hss : (a.2 + φ % 4) % 4 = (a.2 + φ) % 4 := by
    rw [ha0]
    simp
  refine ⟨a, ha, t1, ?_⟩
  rw [hdrv]
  exact (InFamily_phase_congr (F := drv (fun t => wordAt w0001 (t + φ % 4)) x)
    (j0 := a.1) (s := a.2 + φ % 4) (s' := a.2 + φ) hss).1 hIF

end Rule30Ether
end Ruliology.CellularAutomata
