module

public import Ruliology.CellularAutomata.Rule30EtherThreeReach
public import Ruliology.CellularAutomata.Rule30CoupledEmptyRight

/-!
# Local entry tests and gate recovery beside the period-three word 001

Quint and Gemini's `Rule30EtherThreeReach` certifies entry from the empty right half
at tick 1270. We use the existing 47-cell trap `t001` and identify three shorter
windows that force entry after one, nine or ten ticks. The strip proof allows either
exterior bit independently on every tick. The 40- and 42-cell tests therefore apply
to arbitrary physical right tails. Bit zero represents site +1.

Under the imposed clock 001, sample +1 at physical time 3k+1. The empty right half
first follows its final seven-sample phase without interruption at k = 100.
A finite right half that agrees with the empty orbit's first 38 cells at tick 4800
can leave that gate phase and then recover it permanently. Its sharp local recovery
index is 3351. At that restart the reference index is 1600.

The coupled exclusion uses `Rule30CoupledEmptyRight.not_coupled_of_ptrap`.
It applies at any tick where the indicated near field and clock phase coincide.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodThreeGateRecovery

open Rule30EtherThree Rule30Ether Rule30StripCertificates

abbrev drive := wordAt3 w001
abbrev field (r : Nat) := drv drive (fun p => r.testBit (p-1))
def gate (r k : Nat) := field r (3*k+1) 1
def pattern (k : Nat) : Bool := decide (5 ≤ k % 7)
def alternative : Nat := 0x5705722af7c7428

private theorem gate_packed (r k : Nat) :
    gate r k = (rowN drive r (3*k+1)).testBit 0 :=
  (rowN_eq_drv drive r (3*k+1) 0).symm

/-- Reuse the kit's trap invariant. A white gate reads bit zero of the strip. -/
theorem late_read {F : Nat → Nat → Bool} (hF : IsR30 F)
    (hc : ∀ t, F t 0 = drive t) {T i : Nat}
    (hi : i < t001.n) (ph : T % 3 = t001.lab i % 3)
    (hr : EncF F t001.b T 0 (t001.st i))
    (k : Nat) (hT : T ≤ 3*k+1) :
    F (3*k+1) 1 = t001.u.testBit ((t001.lab i + (3*k+1-T)) % 21) := by
  have hdrive : ∀ t, 0 ≤ t → F t 0 = wordAt3 t001.w (t-0) :=
    fun t _ => by rw [Nat.sub_zero]; exact hc t
  have inv := PTrap.invariant t001 t001_check hF 0 hdrive T i (by omega) hi
    (by simpa using ph) hr (3*k+1-T)
  obtain ⟨j, hj, enc, lab⟩ := inv
  rw [show T + (3*k+1-T) = 3*k+1 by omega] at enc
  change t001.lab j = (t001.lab i + (3*k+1-T)) % 21 at lab
  have phase : t001.lab j % 3 = 1 := by omega
  have white : wordAt3 t001.w (t001.lab j % 3) = false := by rw [phase]; decide
  have bit := (PTrap.step t001 t001_check hj false).2.2.2.2 white
  rw [← lab, ← bit]
  exact (encF_head enc (by decide)).symm

private theorem label_word : ∀ i : Fin 7,
    t001.u.testBit ((3*i.val+4)%21) = pattern i.val := by decide

private theorem gate_after {r T i offset : Nat} (hi : i < t001.n)
    (ph : T % 3 = t001.lab i % 3)
    (enc : EncF (field r) t001.b T 0 (t001.st i))
    (align : (t001.lab i + 21 - T%21)%21 = (3*offset+3)%21)
    (k : Nat) (hT : T ≤ 3*k+1) : gate r k = pattern (k+offset) := by
  rw [gate, late_read (F := field r) (drv_isR30 _ _) (drv_col0 _ _) hi ph enc k hT]
  have h := label_word ⟨(k+offset)%7, by omega⟩
  dsimp only at h
  rw [show (t001.lab i + (3*k+1-T)) % 21 = (3*((k+offset)%7)+4)%21 by omega, h]
  simp [pattern]

private theorem empty_entry :
    EncF (field 0) t001.b 1270 0 (t001.st 597) := by
  have e := encF_rowN drive 0 47 1270
  have hf : (fun t => wordAt3 w001 (t+0)) = drive := by
    funext t; rw [Nat.add_zero]
  have eqn := rowN_empty_eq
  rw [hf] at eqn
  rw [← eqn] at e
  exact e

set_option maxRecDepth 131072 in
set_option maxHeartbeats 4000000 in
private theorem alternative_mask :
    t001.st 46 = rowN drive alternative 10582 % 2^47 := by decide +kernel

private theorem alternative_entry :
    EncF (field alternative) t001.b 10582 0 (t001.st 46) := by
  rw [alternative_mask]
  exact encF_rowN drive alternative 47 10582

theorem empty_tail (k : Nat) (hk : 423 ≤ k) : gate 0 k = pattern k := by
  exact gate_after (offset := 0) (by decide) (by decide) empty_entry (by decide) k (by omega)

theorem alternative_tail (k : Nat) (hk : 3527 ≤ k) :
    gate alternative k = pattern (k+1600) :=
  gate_after (by decide) (by decide) alternative_entry (by decide) k (by omega)

/- The finite interval before entry, evaluated in a single forward pass. -/
private def periodStep (r : Nat) := stepN true (stepN false (stepN false r))
private def prefixOK (offset r : Nat) : Nat → Bool
  | 0 => true
  | n+1 => ((stepN false r).testBit 0 == pattern offset) &&
      prefixOK (offset+1) (periodStep r) n

private theorem row_triple (r k : Nat) :
    rowN drive r (3*(k+1)) = periodStep (rowN drive r (3*k)) := by
  rw [show 3*(k+1) = 3*k+2+1 by omega, rowN, rowN, rowN]
  have b (j : Nat) : drive (3*k+j) = drive j := by
    unfold drive wordAt3
    rw [show (3*k+j)%3=j%3 by omega]
  rw [b 2, b 1, show drive (3*k) = drive 0 from b 0]
  rfl

private theorem prefixOK_sound (r off start n : Nat)
    (h : prefixOK (start+off) (rowN drive r (3*start)) n = true) :
    ∀ j, j < n → gate r (start+j) = pattern (start+j+off) := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp h
    intro j hj
    cases j with
    | zero =>
      simp only [Nat.add_zero]
      rw [gate_packed, rowN]
      have b : drive (3*start) = false := by simp [drive, wordAt3, w001]
      rw [b]
      exact beq_iff_eq.mp head
    | succ j =>
      rw [← row_triple, show start+off+1 = start+1+off by omega] at tail
      simpa only [show start+(j+1) = (start+1)+j by omega] using
        ih (start+1) tail j (by omega)

set_option maxRecDepth 131072 in
set_option maxHeartbeats 4000000 in
private theorem checked_empty : prefixOK 100 (rowN drive 0 300) 323 = true := by decide +kernel

set_option maxRecDepth 131072 in
set_option maxHeartbeats 4000000 in
private theorem checked_alternative :
    prefixOK (3351+1600) (rowN drive alternative (3*3351)) 176 = true := by decide +kernel

/-- At sample 100 the chronological gate word starts 0001100 and repeats forever. -/
theorem exact_empty (k : Nat) (hk : 100 ≤ k) : gate 0 k = pattern k := by
  by_cases late : 423 ≤ k
  · exact empty_tail k late
  · have h := prefixOK_sound 0 0 100 323 checked_empty (k-100) (by omega)
    simpa only [show 100+(k-100) = k by omega, Nat.add_zero] using h

/-- The escaped finite restart returns to exactly the reference phase. -/
theorem exact_alternative (k : Nat) (hk : 3351 ≤ k) : gate alternative k = pattern (k+1600) := by
  by_cases late : 3527 ≤ k
  · exact alternative_tail k late
  · have h := prefixOK_sound alternative 1600 3351 176 checked_alternative (k-3351) (by omega)
    simpa only [show 3351+(k-3351) = k by omega] using h

set_option maxRecDepth 131072 in
set_option maxHeartbeats 4000000 in
theorem onset_sharp : gate 0 99 ≠ pattern 99 ∧
    gate alternative 3350 ≠ pattern (3350+1600) := by
  simp only [gate_packed]
  decide +kernel

/-- At the restart the alternative follows nineteen complete seven-sample
words and disagrees on the very next sample. -/
theorem first_escape :
    (∀ j, j < 133 → gate alternative j = pattern (j+1600)) ∧
    gate alternative 133 ≠ pattern (133+1600) := by
  constructor
  · simpa only [Nat.zero_add] using prefixOK_sound alternative 1600 0 133 (by decide +kernel)
  · rw [gate_packed]
    decide +kernel

/-- All 47-bit windows with the specified low bits. -/
private def completions (lowWord width count : Nat) : List Nat :=
  (List.range count).map (fun e => lowWord + 2^width * e)

/-- The exterior bit can be chosen afresh on every tick. -/
private def successors (phase : Nat) (initial : List Nat) : Nat → List Nat
  | 0 => initial
  | n+1 =>
    ((successors phase initial n).flatMap (fun x =>
      [stripStep 47 (wordAt3 w001 (phase+n)) false x,
       stripStep 47 (wordAt3 w001 (phase+n)) true x])).eraseDups

private def trapIndices (label : Nat) : List Nat :=
  (List.range t001.n).filter fun i => t001.lab i == label

private def covered (phase lowWord width count ticks label : Nat) : Bool :=
  let target := (trapIndices label).map t001.st
  (successors phase (completions lowWord width count) ticks).all target.contains

private theorem reachable {F : Nat → Nat → Bool} (hf : IsR30 F) (T phase : Nat)
    (I : List Nat) {r : Nat} (hr : EncF F 47 T 0 r) (hi : r ∈ I) (n : Nat)
    (clock : ∀ j, j < n → F (T+j) 0 = wordAt3 w001 (phase+j)) :
    ∃ s ∈ successors phase I n, EncF F 47 (T+n) 0 s := by
  induction n with
  | zero => exact ⟨r, hi, hr⟩
  | succ n ih =>
    obtain ⟨s, hs, enc⟩ := ih (fun j hj => clock j (by omega))
    have next := encF_step hf enc
    rw [clock n (by omega)] at next
    refine ⟨_, List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨s,hs,?_⟩), next⟩
    cases F (T+n) (0+1+47) <;> simp

private theorem capture {F : Nat → Nat → Bool} (hf : IsR30 F) (T : Nat)
    {r : Nat} (hr : EncF F 47 T 0 r)
    (phase lowWord width count ticks label : Nat)
    (low : r % 2^width = lowWord) (bound : r / 2^width < count)
    (clock : ∀ j, j < ticks → F (T+j) 0 = wordAt3 w001 (phase+j))
    (ok : covered phase lowWord width count ticks label = true) :
    ∃ i, i < t001.n ∧ t001.lab i = label ∧ EncF F t001.b (T+ticks) 0 (t001.st i) := by
  have mem : r ∈ completions lowWord width count := List.mem_map.mpr
    ⟨r / 2^width, List.mem_range.mpr bound, by rw [← low]; exact Nat.mod_add_div ..⟩
  obtain ⟨s, hs, enc⟩ := reachable hf T phase _ hr mem ticks clock
  have found := List.all_eq_true.mp ok s hs
  obtain ⟨i, hi, eq⟩ := List.mem_map.mp (List.contains_iff_mem.mp found)
  obtain ⟨lt, lab⟩ := List.mem_filter.mp hi
  exact ⟨i, List.mem_range.mp lt, beq_iff_eq.mp lab, eq.symm ▸ enc⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem checks :
    covered 0 0x2a2af7c7428 42 32 1 16 = true ∧
    covered 1 0xaaa20c596e 40 128 9 16 = true ∧
    covered 2 0xaab716cf23 40 128 10 18 = true := by decide +kernel

/-- At the original restart phase, the near 42 cells guarantee entry in one tick. -/
theorem from42 {F : Nat → Nat → Bool} (hf : IsR30 F) (T r : Nat)
    (hr : EncF F 47 T 0 r) (low : r % 2^42 = 0x2a2af7c7428)
    (clock : F T 0 = false) :
    ∃ i, i < t001.n ∧ t001.lab i = 16 ∧ EncF F t001.b (T+1) 0 (t001.st i) := by
  apply capture hf T hr 0 _ 42 32 1 16 low _ _ checks.1
  · have := hr.1; omega
  · intro j hj; have : j = 0 := by omega
    subst j; exact clock

/-- In the second-white phase the near 40 cells guarantee entry in nine ticks. -/
theorem from40_white {F : Nat → Nat → Bool} (hf : IsR30 F) (T r : Nat)
    (hr : EncF F 47 T 0 r) (low : r % 2^40 = 0xaaa20c596e)
    (clock : ∀ j, j < 9 → F (T+j) 0 = wordAt3 w001 (1+j)) :
    ∃ i, i < t001.n ∧ t001.lab i = 16 ∧ EncF F t001.b (T+9) 0 (t001.st i) := by
  apply capture hf T hr 1 _ 40 128 9 16 low _ clock checks.2.1
  have := hr.1; omega

/-- In the black phase the near 40 cells guarantee entry in ten ticks. -/
theorem from40_black {F : Nat → Nat → Bool} (hf : IsR30 F) (T r : Nat)
    (hr : EncF F 47 T 0 r) (low : r % 2^40 = 0xaab716cf23)
    (clock : ∀ j, j < 10 → F (T+j) 0 = wordAt3 w001 (2+j)) :
    ∃ i, i < t001.n ∧ t001.lab i = 18 ∧ EncF F t001.b (T+10) 0 (t001.st i) := by
  apply capture hf T hr 2 _ 40 128 10 18 low _ clock checks.2.2
  have := hr.1; omega


set_option maxRecDepth 131072 in
/-- These are windows on the empty-start orbit. The alternative agrees on the first
38 cells at the original restart and disagrees on the 42-cell test. -/
theorem observed_windows :
    rowN drive 0 4800 % 2^42 = 0x2a2af7c7428 ∧
    rowN drive 0 4813 % 2^40 = 0xaaa20c596e ∧
    rowN drive 0 4814 % 2^40 = 0xaab716cf23 ∧
    alternative % 2^38 = rowN drive 0 4800 % 2^38 ∧
    alternative % 2^42 ≠ rowN drive 0 4800 % 2^42 := by decide +kernel

/-- Three local entry conditions, including their clock phases. -/
def EntryWindow (phase r : Nat) : Prop :=
  (phase%3 = 0 ∧ r % 2^42 = 0x2a2af7c7428) ∨
  (phase%3 = 1 ∧ r % 2^40 = 0xaaa20c596e) ∨
  (phase%3 = 2 ∧ r % 2^40 = 0xaab716cf23)

/-- A finite-left realization of a permanently imposed 001 clock cannot encounter
any of the three displayed near fields in its indicated phase, at any later tick. -/
theorem no_coupled_of_window (φ T r : Nat) (x : Nat → Bool) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false)
    (hr : EncF (drv (fun t => wordAt3 w001 (t+φ)) x) 47 T 0 r)
    (window : EntryWindow (T+φ) r) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt3 w001 (t+φ)) s x := by
  let F := drv (fun t => wordAt3 w001 (t+φ)) x
  have clk (q j : Nat) (hq : (T+φ)%3 = q) : F (T+j) 0 = wordAt3 w001 (q+j) := by
    rw [show F (T+j) 0 = wordAt3 w001 (T+j+φ) from drv_col0 _ _ _]
    unfold wordAt3
    rw [show (T+j+φ)%3 = (q+j)%3 by omega]
  have exclude (n l : Nat) (phase : (T+n+φ)%3 = l%3)
      (hit : ∃ i, i < t001.n ∧ t001.lab i = l ∧ EncF F t001.b (T+n) 0 (t001.st i)) :
      ¬ Rule30Coupled.Coupled (fun t => wordAt3 w001 (t+φ)) s x := by
    obtain ⟨i, hi, lab, enc⟩ := hit
    exact Rule30CoupledEmptyRight.not_coupled_of_ptrap t001 t001_check (by decide)
      φ (Rule30CoupledEmptyRight.wordAt3_has_black (by decide) φ) hi (by rwa [lab]) enc s hs
  rcases window with ⟨h,low⟩ | ⟨h,low⟩ | ⟨h,low⟩
  · exact exclude 1 16 (by omega) (from42 (drv_isR30 _ _) T r hr low (clk 0 0 h))
  · exact exclude 9 16 (by omega) (from40_white (drv_isR30 _ _) T r hr low (fun j _ => clk 1 j h))
  · exact exclude 10 18 (by omega) (from40_black (drv_isR30 _ _) T r hr low (fun j _ => clk 2 j h))

/-- For a full physical row with finite left support and any right tail, a matching
entry window forces a first finite disagreement with the proposed center clock. -/
theorem finite_break (φ r W : Nat) (x : Int → Bool)
    (left : ∀ p : Int, p < -(W : Int) → x p = false)
    (origin : x 0 = wordAt3 w001 (0+φ))
    (bound : r < 2^47) (near : ∀ j : Nat, j < 47 → r.testBit j = x ((1+j : Nat) : Int))
    (window : EntryWindow φ r) :
    ∃ d, 1 ≤ d ∧ (∀ t, t < d → Rule30Realization.evol x t 0 = wordAt3 w001 (t+φ)) ∧
      Rule30Realization.evol x d 0 ≠ wordAt3 w001 (d+φ) := by
  apply Rule30CoupledEmptyRight.finite_divergence_of_no_coupled (R := x) _ (fun _ _ => rfl) origin left
  intro s hs
  apply no_coupled_of_window φ 0 r _ s hs
  · refine ⟨bound, fun j hj => ?_⟩
    rw [drv_init _ _ _ (by omega)]
    exact near j hj
  · simpa only [Nat.zero_add] using window

/-- The finite row agrees with a specified low word. Its physical evolution at
the stated horizon lies outside every window in the trap, irrespective of label. -/
def Misses (phase lowWord width horizon initial : Nat) : Prop :=
  initial % 2^width = lowWord % 2^width ∧
  ∀ i : Fin t001.n,
    rowN (fun t => drive (phase+t)) initial horizon % 2^47 ≠ t001.st i.val

instance (p v w h r : Nat) : Decidable (Misses p v w h r) := by
  unfold Misses
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Both coordinates of each local entry certificate are sharp. The first row in
each pair misses one tick earlier. The second agrees on one fewer site and misses
at the claimed deadline. All six rows have a white tail. -/
theorem sharp_windows :
    Misses 0 0x2a2af7c7428 42 0 0x16a2af7c7428 ∧
    Misses 0 0x2a2af7c7428 41 1 0x4a2af7c7428 ∧
    Misses 1 0xaaa20c596e 40 8 0x3caaa20c596e ∧
    Misses 1 0xaaa20c596e 39 9 0x12aa20c596e ∧
    Misses 2 0xaab716cf23 40 9 0x1f3aab716cf23 ∧
    Misses 2 0xaab716cf23 39 10 0x12ab716cf23 := by decide +kernel

end Ruliology.CellularAutomata.Rule30PeriodThreeGateRecovery
