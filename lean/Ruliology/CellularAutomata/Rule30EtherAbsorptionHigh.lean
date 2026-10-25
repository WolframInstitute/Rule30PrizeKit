module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux
public import Ruliology.CellularAutomata.Rule30EtherTwoCellAux

@[expose] public section

/-!
# High-support period-4 absorption for the word `0001`

Every finitely supported right half that is white on positions `1, …, 30`, of arbitrary support
size and for every phase `φ`, enters the ether-and-wall family for alignment `(5,0)` or `(6,0)` at
time `14 - φ`.  The wall window is confined to cells `1, …, 16` at that time, so cells at positions
at least `31` cannot influence it and the orbit agrees there with the all-white orbit.

This is the high-support restriction of `Rule30Ether.Absorption w0001 A0001`; it is not the full
absorption conjecture.  The single-cell case (`Rule30Ether.singleCell_absorption`) and this high
support case are separate partial results.
-/

namespace Ruliology.CellularAutomata
namespace Rule30Ether

open Rule30Jen Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- **High-support period-4 absorption for `w = 0001`.** Every finitely supported right half that
is white on positions `1, …, 30`, of arbitrary support size and for every phase `φ`, enters the
ether-and-wall family for alignment `(5,0)` or `(6,0)` at time `14 - φ`. -/
theorem absorption_high_mod (x : Nat → Bool) (φ : Nat)
    (hx0 : ∀ i, 1 ≤ i → i ≤ 30 → x i = false) (hφ : φ < 4) :
    ∃ a ∈ A0001, ∃ t1,
      InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 :=
  ⟨(6, 0), by decide, 14 - φ, by simpa using large_case2 (x := x) hx0 hφ⟩

/-- Phase reduction for high-support absorption. -/
theorem absorption_high (x : Nat → Bool) (φ : Nat)
    (hx0 : ∀ i, 1 ≤ i → i ≤ 30 → x i = false) :
    ∃ a ∈ A0001, ∃ t1,
      InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  have hφ0 : φ % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨a, ha, t1, hIF⟩ := absorption_high_mod x (φ % 4) hx0 hφ0
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
    rw [ha0]; simp
  refine ⟨a, ha, t1, ?_⟩
  rw [hdrv]
  exact (InFamily_phase_congr (F := drv (fun t => wordAt w0001 (t + φ % 4)) x)
    (j0 := a.1) (s := a.2 + φ % 4) (s' := a.2 + φ) hss).1 hIF

end Rule30Ether
end Ruliology.CellularAutomata
