module

public import Ruliology.CellularAutomata.Rule30EtherTwoCellBase
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG0
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG1
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG2
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG3
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG4
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG5
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG6
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG7
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG8
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG9
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG10
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG11
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG12
public import Ruliology.CellularAutomata.Rule30EtherTwoCellDataG13

@[expose] public section

/-!
# Finite data for the two-cell period-4 absorption theorem

`dataAll p φ` is assembled from the 14 certificate modules `Rule30EtherTwoCellDataG0`–`G13`;
`checkAll_range` combines their checked ranges. `checkSingleAll` verifies the single-cell
reference witnesses. These are finite computations only; the mathematical reduction is in
`Rule30EtherTwoCell`.
-/

namespace Ruliology.CellularAutomata
namespace Rule30Ether

open Rule30Jen Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def dataAll (p φ : Nat) : List (Nat × Nat × Nat) :=
  if p ≤ 2 then dataAllG0 p φ
  else if p ≤ 4 then dataAllG1 p φ
  else if p ≤ 5 then dataAllG2 p φ
  else if p ≤ 7 then dataAllG3 p φ
  else if p ≤ 9 then dataAllG4 p φ
  else if p ≤ 10 then dataAllG5 p φ
  else if p ≤ 11 then dataAllG6 p φ
  else if p ≤ 12 then dataAllG7 p φ
  else if p ≤ 13 then dataAllG8 p φ
  else if p ≤ 15 then dataAllG9 p φ
  else if p ≤ 17 then dataAllG10 p φ
  else if p ≤ 19 then dataAllG11 p φ
  else if p ≤ 21 then dataAllG12 p φ
  else dataAllG13 p φ

theorem checkAll_range (p φ : Nat) (hp1 : 1 ≤ p) (hp30 : p ≤ 30) (hφ : φ < 4) :
    (dataAll p φ).length = Mfun p φ - p - 1 ∧ checkRange (dataAll p φ) p φ = true := by
  by_cases h0 : p ≤ 2
  · have hh := checkAllG0_range p φ (by omega) h0 hφ
    simpa [dataAll, if_pos h0] using hh
  by_cases h1 : p ≤ 4
  · have hh := checkAllG1_range p φ (by omega) h1 hφ
    simpa [dataAll, if_neg h0, if_pos h1] using hh
  by_cases h2 : p ≤ 5
  · have hh := checkAllG2_range p φ (by omega) h2 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_pos h2] using hh
  by_cases h3 : p ≤ 7
  · have hh := checkAllG3_range p φ (by omega) h3 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_pos h3] using hh
  by_cases h4 : p ≤ 9
  · have hh := checkAllG4_range p φ (by omega) h4 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4] using hh
  by_cases h5 : p ≤ 10
  · have hh := checkAllG5_range p φ (by omega) h5 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5] using hh
  by_cases h6 : p ≤ 11
  · have hh := checkAllG6_range p φ (by omega) h6 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6] using hh
  by_cases h7 : p ≤ 12
  · have hh := checkAllG7_range p φ (by omega) h7 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7] using hh
  by_cases h8 : p ≤ 13
  · have hh := checkAllG8_range p φ (by omega) h8 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8] using hh
  by_cases h9 : p ≤ 15
  · have hh := checkAllG9_range p φ (by omega) h9 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h9] using hh
  by_cases h10 : p ≤ 17
  · have hh := checkAllG10_range p φ (by omega) h10 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos h10] using hh
  by_cases h11 : p ≤ 19
  · have hh := checkAllG11_range p φ (by omega) h11 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_pos h11] using hh
  by_cases h12 : p ≤ 21
  · have hh := checkAllG12_range p φ (by omega) h12 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_pos h12] using hh
  by_cases h13 : p ≤ 30
  · have hh := checkAllG13_range p φ (by omega) h13 hφ
    simpa [dataAll, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_pos h13] using hh
  · omega

def checkSingleAll : Bool :=
  (List.range 30).all (fun i =>
    (List.range 4).all (fun φ =>
      let d := sdata (i + 1) φ
      famRowN (i + 1) sQ φ d.1 d.2.1 d.2.2))

theorem checkSingleAll_ok : checkSingleAll = true := by decide

theorem checkSingle_range (p φ : Nat) (hp1 : 1 ≤ p) (hp30 : p ≤ 30) (hφ : φ < 4) :
    famRowN p sQ φ (sdata p φ).1 (sdata p φ).2.1 (sdata p φ).2.2 = true := by
  have h := checkSingleAll_ok
  unfold checkSingleAll at h
  have h1 := List.all_eq_true.1 h (p - 1) (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 h1 φ (List.mem_range.2 hφ)
  rw [show p - 1 + 1 = p by omega] at h2
  exact h2

end Rule30Ether
end Ruliology.CellularAutomata
