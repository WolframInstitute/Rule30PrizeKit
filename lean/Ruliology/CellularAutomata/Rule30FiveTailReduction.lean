module

public import Ruliology.CellularAutomata.Rule30ShortTail

@[expose] public section

/-!
Reduce every Boolean tail of length at most five to the shorter-tail
family or one of eight new black-ended cores. Removing white ends and
rotating finite periods preserves the eventual-word assertion.
-/
namespace Ruliology.CellularAutomata.Rule30FiveTailReduction
open Rule30Jen Rule30Realization Rule30WordRotation

def fiveCores : List (List Bool) :=
  [[true,false,false,false,true], [true,false,false,true,true],
   [true,false,true,false,true], [true,false,true,true,true],
   [true,true,false,false,true], [true,true,false,true,true],
   [true,true,true,false,true], [true,true,true,true,true]]

private def words : List (List Bool) := (List.range 6).flatMap Rule30Jen.allLists
private theorem decomposition_check : words.all (fun u =>
    u.all (! ·) || (shortCores ++ fiveCores).any (fun v => (List.range 6).any (fun a =>
      (List.range 6).any (fun b => u == List.replicate a false ++ v ++ List.replicate b false)))) = true :=
  by decide +kernel

theorem decomposition (u : List Bool) (hlen : u.length ≤ 5) :
    (∀ b, b ∈ u → b = false) ∨ ∃ a b v, v ∈ shortCores ++ fiveCores ∧
      u = List.replicate a false ++ v ++ List.replicate b false := by
  have hmem : u ∈ words := List.mem_flatMap.mpr
    ⟨u.length, List.mem_range.mpr (by omega), Rule30Jen.mem_allLists u⟩
  have h := List.all_eq_true.mp decomposition_check u hmem
  rcases Bool.or_eq_true_iff.mp h with hz | hc
  · left
    intro b hb
    have := List.all_eq_true.mp hz b hb
    cases b <;> simp_all
  · right
    obtain ⟨v, hv, hvcheck⟩ := List.any_eq_true.mp hc
    obtain ⟨a, _, hacheck⟩ := List.any_eq_true.mp hvcheck
    obtain ⟨b, _, hbcheck⟩ := List.any_eq_true.mp hacheck
    exact ⟨a,b,v,hv,by simpa only [beq_iff_eq] using hbcheck⟩

private theorem replicate_append (a b : Nat) :
    List.replicate a false ++ List.replicate b false = List.replicate (a+b) false := by
  induction a with
  | zero => simp
  | succ a ih => simpa [List.replicate_succ, Nat.succ_add] using congrArg (false :: ·) ih

private theorem replicate_getD (r n : Nat) : (List.replicate r false).getD n false = false := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    cases n with
    | zero => simp [List.replicate_succ]
    | succ n => simpa only [List.replicate_succ,List.getD_cons_succ] using ih n

/-- The eight length-five core exclusions imply every length-at-most-five exclusion.
The threshold is a sufficient bound; this theorem does not provide the core proofs. -/
theorem no_five_tail_of_cores {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (hcores : ∀ v, v ∈ fiveCores → ∀ r, 69 ≤ r →
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ v))
    (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  rcases decomposition u hu with hz | ⟨a,b,v,hv,he⟩
  · obtain ⟨T,hT⟩ := hword
    apply Rule30FiniteConfigs.no_column_eventually_constant hlo hzero i
    refine ⟨T,false,fun t ht => ?_⟩
    rw [hT t ht]
    have hzword : ∀ b, b ∈ List.replicate r false ++ u → b = false := by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact (List.mem_replicate.mp hb).2
      · exact hz b hb
    rw [List.eq_replicate_of_mem hzword]
    exact replicate_getD _ _
  · rw [he] at hword
    have hw : Rule30FiniteStrips.EventuallyWord x i
        ((List.replicate r false ++ List.replicate a false ++ v) ++ List.replicate b false) := by
      simpa only [List.append_assoc] using hword
    have hrot := eventuallyWord_swap (by simp; omega) hw
    have hlist : List.replicate b false ++ (List.replicate r false ++ List.replicate a false ++ v) =
        List.replicate (b+(r+a)) false ++ v := by
      rw [replicate_append, ← List.append_assoc, replicate_append]
    rw [hlist] at hrot
    rcases List.mem_append.mp hv with hv | hv
    · have hvlen : v.length ≤ 4 := by
        simp only [shortCores,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact Rule30ShortTail.no_short_tail_leftFinite hlo hzero i v hvlen
        (b+(r+a)) (by omega) hrot
    · exact hcores v hv (b+(r+a)) (by omega) hrot

/-! ### Intrinsic Characterization of `fiveCores`, Disjointness from `shortCores`, and Canonical `seed` Specialization -/

/-- Every word `v ∈ fiveCores` has length `5`. -/
theorem fiveCores_length {v : List Bool} (hv : v ∈ fiveCores) : v.length = 5 := by
  revert v hv
  decide

/-- Every word `v ∈ fiveCores` begins and ends with `true`. -/
theorem fiveCores_head_last_true {v : List Bool} (hv : v ∈ fiveCores) :
    v.getD 0 false = true ∧ v.getD 4 false = true := by
  revert v hv
  decide

/-- **Exact Intrinsic Characterization of `fiveCores` (`mem_fiveCores_iff`):** a Boolean list `v`
belongs to `fiveCores` if and only if `v.length = 5`, `v.getD 0 false = true`, and `v.getD 4 false = true`. -/
theorem mem_fiveCores_iff (v : List Bool) :
    v ∈ fiveCores ↔ v.length = 5 ∧ v.getD 0 false = true ∧ v.getD 4 false = true := by
  constructor
  · intro hv
    exact ⟨fiveCores_length hv, (fiveCores_head_last_true hv).1, (fiveCores_head_last_true hv).2⟩
  · rintro ⟨hlen, h0, h4⟩
    rcases v with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | tl⟩⟩⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · simp at hlen
    · simp at hlen
    · simp at hlen
    · simp at h0 h4
      subst h0; subst h4
      cases b1 <;> cases b2 <;> cases b3 <;> decide
    · simp at hlen

/-- Every word in `shortCores` has length at most `4`. -/
theorem shortCores_length_le_four {v : List Bool} (hv : v ∈ shortCores) :
    v.length ≤ 4 := by
  revert v hv
  decide

/-- **Disjointness of `fiveCores` from `shortCores` (`fiveCores_disjoint_shortCores`):**
no word in `fiveCores` belongs to `shortCores`. -/
theorem fiveCores_disjoint_shortCores {v : List Bool}
    (hv5 : v ∈ fiveCores) (hv4 : v ∈ shortCores) : False := by
  have h5 := fiveCores_length hv5
  have h4 := shortCores_length_le_four hv4
  omega

/-- **Intrinsic Black-Ended Core Form of `no_five_tail_of_cores` (`no_five_tail_of_black_ended_five`):**
if every length-5 word `v` starting and ending with `true` is excluded after `r ≥ 69` white cells,
then every Boolean word `u` of length `u.length ≤ 5` is excluded after `r ≥ 69` white cells. -/
theorem no_five_tail_of_black_ended_five {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (hcores : ∀ v : List Bool, v.length = 5 → v.getD 0 false = true → v.getD 4 false = true →
      ∀ r, 69 ≤ r → ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ v))
    (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) :=
  no_five_tail_of_cores hlo hzero i
    (fun v hv r hr' => hcores v (fiveCores_length hv) (fiveCores_head_last_true hv).1
      (fiveCores_head_last_true hv).2 r hr')
    u hu r hr

/-- **Canonical Single-Black-Cell `seed` Specialization (`no_five_tail_seed_of_cores`):**
for the standard initial configuration `seed`, excluding the 8 cores in `fiveCores` at column `i`
for `r ≥ 69` excludes `List.replicate r false ++ u` for every `u` with `u.length ≤ 5` and `r ≥ 69`. -/
theorem no_five_tail_seed_of_cores (i : Int)
    (hcores : ∀ v, v ∈ fiveCores → ∀ r, 69 ≤ r →
      ¬ Rule30FiniteStrips.EventuallyWord seed i (List.replicate r false ++ v))
    (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord seed i (List.replicate r false ++ u) := by
  have hlo : seed 0 = true := by decide
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    show decide (p = 0) = false
    simp; omega
  exact no_five_tail_of_cores hlo hzero i hcores u hu r hr

end Ruliology.CellularAutomata.Rule30FiveTailReduction
