module

public import Ruliology.CellularAutomata.Rule30FiniteStrips

@[expose] public section

/-!
Eventual repetition of a nonempty finite Boolean word is invariant under
rotating that word. The proof shifts the starting time and tracks indices
modulo the word length; no bound on the transient is assumed.
-/
namespace Ruliology.CellularAutomata.Rule30WordRotation
open Rule30Realization Rule30FiniteStrips

/-- An eventual word remains eventual when an initial block is moved to the end.
The proof uses only core List operations, with no Mathlib dependency. -/
theorem eventuallyWord_swap {x : Int → Bool} {i : Int} {u v : List Bool}
    (hpos : 0 < (u ++ v).length) (hword : EventuallyWord x i (u ++ v)) :
    EventuallyWord x i (v ++ u) := by
  obtain ⟨T, hT⟩ := hword
  refine ⟨T + u.length, fun t ht => ?_⟩
  rw [hT t (by omega)]
  let P := u.length + v.length
  have hP : 0 < P := by simpa [P] using hpos
  let q := (t - (T + u.length)) % P
  have hq : q < P := Nat.mod_lt _ hP
  have hmod : (t - T) % P = (q + u.length) % P := by
    dsimp [q]
    rw [Nat.mod_add_mod]
    congr 1
    omega
  simp only [List.length_append]
  rw [show v.length + u.length = P by dsimp [P]; omega]
  change (u ++ v).getD ((t - T) % P) false = (v ++ u).getD q false
  rw [hmod]
  simp only [List.getD_eq_getElem?_getD]
  by_cases hqv : q < v.length
  · have hsmall : q + u.length < P := by dsimp [P]; omega
    rw [Nat.mod_eq_of_lt hsmall,
      List.getElem?_append_right (l₁ := u) (l₂ := v) (by omega),
      List.getElem?_append_left hqv, Nat.add_sub_cancel]
  · have hqv' : v.length ≤ q := by omega
    have hsmall : q - v.length < u.length := by dsimp [P] at hq; omega
    have hm : (q + u.length) % P = q - v.length := by
      rw [show q + u.length = q - v.length + P by dsimp [P]; omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp [P]; omega)]
    rw [hm, List.getElem?_append_left hsmall, List.getElem?_append_right hqv']

/-- The eight binary words of length at most four which begin and end black. -/
def shortCores : List (List Bool) :=
  [[true], [true,true], [true,false,true], [true,true,true],
    [true,false,false,true], [true,false,true,true], [true,true,false,true],
    [true,true,true,true]]

private def shortWords : List (List Bool) := (List.range 5).flatMap Rule30Jen.allLists

private theorem short_decomposition_check : shortWords.all (fun u =>
    u.all (! ·) || shortCores.any (fun v => (List.range 5).any (fun a =>
      (List.range 5).any (fun b => u == List.replicate a false ++ v ++ List.replicate b false)))) = true :=
  by decide +kernel

/-- A word of length at most four is either all white or consists of a short black-ended core
with a white prefix and suffix. The finite case split is checked in the kernel. -/
theorem short_decomposition (u : List Bool) (hlen : u.length ≤ 4) :
    (∀ b, b ∈ u → b = false) ∨
      ∃ a b v, v ∈ shortCores ∧ u = List.replicate a false ++ v ++ List.replicate b false := by
  have hmem : u ∈ shortWords := List.mem_flatMap.mpr
    ⟨u.length, List.mem_range.mpr (by omega), Rule30Jen.mem_allLists u⟩
  have h := List.all_eq_true.mp short_decomposition_check u hmem
  rcases Bool.or_eq_true_iff.mp h with hz | hc
  · left
    intro b hb
    have := List.all_eq_true.mp hz b hb
    cases b <;> simp_all
  · right
    obtain ⟨v, hv, hvcheck⟩ := List.any_eq_true.mp hc
    obtain ⟨a, _, hacheck⟩ := List.any_eq_true.mp hvcheck
    obtain ⟨b, _, hbcheck⟩ := List.any_eq_true.mp hacheck
    exact ⟨a, b, v, hv, by simpa only [beq_iff_eq] using hbcheck⟩

/-! ## Unconditional bidirectional rotation equivalences and invariants of `shortCores` -/

/-- **Unconditional Bidirectional Rotation Equivalence for `EventuallyWord` (`eventuallyWord_swap_iff_and_seed`).** -/
theorem eventuallyWord_swap_iff_and_seed (x : Int → Bool) (i : Int) (u v : List Bool) :
    (Rule30FiniteStrips.EventuallyWord x i (u ++ v) ↔
      Rule30FiniteStrips.EventuallyWord x i (v ++ u)) ∧
    (Rule30StripCertificates.EventuallyWord (u ++ v) ↔
      Rule30StripCertificates.EventuallyWord (v ++ u)) := by
  have hswap : ∀ {y : Int → Bool} {a b : List Bool},
      Rule30FiniteStrips.EventuallyWord y i (a ++ b) →
      Rule30FiniteStrips.EventuallyWord y i (b ++ a) := by
    intro y a b hw
    by_cases hpos : 0 < (a ++ b).length
    · exact eventuallyWord_swap hpos hw
    · have hnil : a ++ b = [] := List.eq_nil_of_length_eq_zero (by omega)
      have ha : a = [] := (List.append_eq_nil_iff.mp hnil).1
      have hb : b = [] := (List.append_eq_nil_iff.mp hnil).2
      subst ha; subst hb; exact hw
  have hswap_seed : ∀ {a b : List Bool},
      Rule30StripCertificates.EventuallyWord (a ++ b) →
      Rule30StripCertificates.EventuallyWord (b ++ a) := by
    intro a b hw
    have hw' : Rule30FiniteStrips.EventuallyWord Rule30Realization.seed 0 (a ++ b) := by
      simpa only [Rule30FiniteStrips.EventuallyWord, Rule30StripCertificates.EventuallyWord,
        Rule30Realization.evol_seed] using hw
    by_cases hpos : 0 < (a ++ b).length
    · have hr := eventuallyWord_swap hpos hw'
      simpa only [Rule30FiniteStrips.EventuallyWord, Rule30StripCertificates.EventuallyWord,
        Rule30Realization.evol_seed] using hr
    · have hnil : a ++ b = [] := List.eq_nil_of_length_eq_zero (by omega)
      have ha : a = [] := (List.append_eq_nil_iff.mp hnil).1
      have hb : b = [] := (List.append_eq_nil_iff.mp hnil).2
      subst ha; subst hb; exact hw
  exact ⟨⟨hswap, hswap⟩, ⟨hswap_seed, hswap_seed⟩⟩

/-- **Length Bounds and Black-Endpoint Invariants of `shortCores` (`shortCores_length_and_endpoints`).** -/
theorem shortCores_length_and_endpoints :
    shortCores.all (fun v => decide (1 ≤ v.length ∧ v.length ≤ 4) &&
      v.headD false && v.getD (v.length - 1) false) = true := by decide

end Ruliology.CellularAutomata.Rule30WordRotation
