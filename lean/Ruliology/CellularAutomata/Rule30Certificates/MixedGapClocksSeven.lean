module

public import Ruliology.CellularAutomata.Rule30Certificates.MixedGapClocksSevenPhases

/-!
# Remaining phases and rank soundness for the seven-white clock

The clock with one black and seven white ticks cannot be an eventual word of the singleton center.
The phase checks are split across two files to bound the resources used by each kernel build.

Contributors: Dusty Galindo; OpenAI Codex (GPT-6.2 Astra).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30MixedGapClocks.Seven
open Ruliology.CellularAutomata Rule30StripCertificates

set_option maxRecDepth 110000
set_option maxHeartbeats 0
set_option Elab.async false





private theorem edges4 : phaseEdges 4 = true := by decide +kernel

private theorem edges5 : phaseEdges 5 = true := by decide +kernel

private theorem edges6 : phaseEdges 6 = true := by decide +kernel

private theorem edges7 : phaseEdges 7 = true := by decide +kernel

private theorem edges : cert.check = true := by
  apply List.all_eq_true.2
  intro φ hp
  have bound : φ < 8 := List.mem_range.1 hp
  change phaseEdges φ = true
  have cases8 : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 ∨ φ = 4 ∨ φ = 5 ∨ φ = 6 ∨ φ = 7 := by omega
  rcases cases8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact edges0
  · exact edges1
  · exact edges2
  · exact edges3
  · exact edges4
  · exact edges5
  · exact edges6
  · exact edges7





private theorem counters4 : phaseCounters 4 = true := by decide +kernel

private theorem counters5 : phaseCounters 5 = true := by decide +kernel

private theorem counters6 : phaseCounters 6 = true := by decide +kernel

private theorem counters7 : phaseCounters 7 = true := by decide +kernel

private theorem counters : cert.checkG = true := by
  apply List.all_eq_true.2
  intro φ hp
  have bound : φ < 8 := List.mem_range.1 hp
  change phaseCounters φ = true
  have cases8 : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 ∨ φ = 4 ∨ φ = 5 ∨ φ = 6 ∨ φ = 7 := by omega
  rcases cases8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact counters0
  · exact counters1
  · exact counters2
  · exact counters3
  · exact counters4
  · exact counters5
  · exact counters6
  · exact counters7


theorem seven_white_one_black : ¬ EventuallyWord clock := by
  rintro ⟨T,hT⟩
  exact cert.sound edges counters (by decide) (by decide) T hT

end Ruliology.CellularAutomata.Rule30MixedGapClocks.Seven
