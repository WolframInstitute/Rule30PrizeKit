module

public import Ruliology.CellularAutomata.Rule30SixTailSharpened
public import Ruliology.CellularAutomata.Rule30WhitePad10111
public import Ruliology.CellularAutomata.Rule30WhiteEndNine
public import Ruliology.CellularAutomata.Rule30WhiteRunEight
public import Ruliology.CellularAutomata.Rule30WordRotation
public import Ruliology.CellularAutomata.Rule30White17Runs
public import Ruliology.CellularAutomata.Rule30GrammarRuns
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30ArbitraryWhitePadding
public import Ruliology.CellularAutomata.Rule30ParametricStripCertificates

/-!
# Padded words: one bound for every tail

The center column of the single seed is never eventually the repeating word `0^r u`, a white run
of length `r` followed by a tail `u`, once `r` reaches a bound that depends on `u`.
`paddedBound u` retains the sharper catalog bounds for tails of at most six cells, adds bounds
7 for `1111` and 17 for other pure black tails of length at least three, and uses
`Rule30ArbitraryWhitePadding.paddingThreshold` for longer tails. `no_padded_word` covers every
tail, including empty and all-white tails:

| Tail `u` | Bound | Proof |
|---|---|---|
| `1111` | 7 | `not_eventuallyWord_zeros_1111`, from the uniform grammar |
| `1^k`, `k ≥ 3`, `k ≠ 4` | 17 | `no_padded_word_black` (any length) |
| `11` | 8 | `Rule30WhiteRunEight.no_white_run_11_ge8` |
| `1011` | 9 | `Rule30ParametricStripCertificates.paramStripCert`, width 6 |
| `10011` | 9 | `Rule30ParametricStripCertificates.paramStripCert`, width 6 |
| `10111` | 9 | `Rule30WhitePad10111.not_eventually_zeros_10111` |
| `11011` | 9 | `Rule30ParametricStripCertificates.paramStripCert`, width 6 |
| `101111` | 9 | `Rule30ParametricStripCertificates.paramStripCert`, width 6 |
| `1` | 9 | `Rule30WhiteEndNine.not_eventually_white_end_ge9`, rotated |
| `1101` | 11 | `Rule30ParametricStripCertificates.paramStripCert`, width 7 |
| any other of at most four cells | 49 | `Rule30ShortTail.no_short_tail_seed` |
| any other of five cells | 69 | `Rule30FiveTail.no_five_tail_seed` |
| any other of six cells | 74 | `Rule30SixTailSharpened.no_six_tail_seed` |
| every longer tail | `paddingThreshold u.length` | `Rule30ArbitraryWhitePadding.not_eventually_padded_word`, rotated; all-white tails use nonconstancy |

For tails of every length ending in `011`, `001001` or `111001`, `Rule30SuffixFamilies` gives the
bounds `10 · |v| + 41` and `10 · |v| + 71`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PaddedWords

open Rule30StripCertificates

/-- A white-padding bound for every tail, retaining the sharper bounds for length at most six. -/
def paddedBound (u : List Bool) : Nat :=
  if u = [true, true] then 8
  else if u = [true, false, true, true] then 9
  else if u = [true, false, false, true, true] then 9
  else if u = [true, false, true, true, true] then 9
  else if u = [true, true, false, true, true] then 9
  else if u = [true, false, true, true, true, true] then 9
  else if u = [true] then 9
  else if u = [true, true, false, true] then 11
  else if u = [true, true, true, true] then 7
  else if u = List.replicate u.length true ∧ 3 ≤ u.length then 17
  else if u.length ≤ 4 then 49
  else if u.length ≤ 5 then 69
  else if u.length ≤ 6 then 74
  else Rule30ArbitraryWhitePadding.paddingThreshold u.length

/-- An eventual word of the single seed's center column may start at any of its cells. -/
theorem eventuallyWord_swap {u v : List Bool} (hpos : 0 < (u ++ v).length)
    (h : EventuallyWord (u ++ v)) : EventuallyWord (v ++ u) := by
  have h' : Rule30FiniteStrips.EventuallyWord Rule30Realization.seed 0 (u ++ v) := by
    simpa only [Rule30FiniteStrips.EventuallyWord, EventuallyWord, Rule30Realization.evol_seed]
      using h
  simpa only [Rule30FiniteStrips.EventuallyWord, EventuallyWord, Rule30Realization.evol_seed] using
    Rule30WordRotation.eventuallyWord_swap hpos h'

/-- `0^q 1` is the white end `1 0^q`, read from its white run. -/
theorem not_eventuallyWord_zeros_one (q : Nat) (hq : 9 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true]) := fun h =>
  Rule30WhiteEndNine.not_eventually_white_end_ge9 q hq (eventuallyWord_swap (by simp) h)

/-- `0^r 1 1` as an eventual word: its white run and its two black cells, with period `r + 2`. -/
theorem not_eventuallyWord_zeros_11 (r : Nat) (hr : 8 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ [true, true]) := by
  rintro ⟨T, hT⟩
  have hlen : (List.replicate r false ++ [true, true]).length = r + 2 := by simp
  have at_ : ∀ i, i < r + 2 →
      Rule30Prize.center (T + i) = (List.replicate r false ++ [true, true]).getD i false := by
    intro i hi
    have := hT (T + i) (by omega)
    rw [hlen, show T + i - T = i by omega, Nat.mod_eq_of_lt hi] at this
    exact this
  refine Rule30WhiteRunEight.no_white_run_11_ge8 T r T hr (fun t ht => ?_) (Nat.le_refl T)
    (fun i hi => ?_) ?_ ?_
  · show Rule30Jen.cell (t + (r + 2)) 0 = Rule30Jen.cell t 0
    rw [hT _ (by omega), hT t ht, hlen, show t + (r + 2) - T = (t - T) + (r + 2) by omega,
      Nat.add_mod_right]
  · rw [at_ i (by omega), List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
    simp [hi]
  · rw [at_ r (by omega), List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  · rw [show T + r + 1 = T + (r + 1) by omega, at_ (r + 1) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp)]
    simp

/-- All pure black tails of length at least three, including lengths beyond the six-cell API. -/
theorem no_padded_word_black (k : Nat) (hk : 3 ≤ k) (q : Nat) (hq : 17 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ List.replicate k true) := by
  intro h
  exact Rule30White17Runs.not_eventually_black_white k q (by omega) hq
    (eventuallyWord_swap (by simp; omega) h)

/-- The singleton four-black grammar block, rotated to start at its white run. -/
theorem not_eventuallyWord_zeros_1111 (q : Nat) (hq : 7 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true, true, true, true]) := by
  intro h
  have hg := Rule30GrammarRuns.not_eventually_grammar [(4, q)] (by simp)
    (by
      intro a ha
      have ha' : a = (4, q) := by simpa using ha
      subst a
      exact Or.inr (Or.inr (Or.inl ⟨rfl, hq⟩)))
  apply hg
  simpa using eventuallyWord_swap (by simp) h

/-- `0^r 1011` as an eventual word: excluded for all `r ≥ 9` by parametric strip certificates. -/
theorem not_eventuallyWord_zeros_1011 (r : Nat) (hr : 9 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ [true, false, true, true]) :=
  Rule30ParametricStripCertificates.not_eventually_param_word false 9 [true, false, true, true] 6 3
    (by decide) (by decide) (by decide +kernel) r hr

/-- `0^r 1101` as an eventual word: excluded for all `r ≥ 11` by parametric strip certificates. -/
theorem not_eventuallyWord_zeros_1101 (r : Nat) (hr : 11 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ [true, true, false, true]) :=
  Rule30ParametricStripCertificates.not_eventually_param_word false 11 [true, true, false, true] 7 2
    (by decide) (by decide) (by decide +kernel) r hr

/-- `0^r 10011` as an eventual word: excluded for all `r ≥ 9` by parametric strip certificates. -/
theorem not_eventuallyWord_zeros_10011 (r : Nat) (hr : 9 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ [true, false, false, true, true]) :=
  Rule30ParametricStripCertificates.not_eventually_param_word false 9 [true, false, false, true, true] 6 2
    (by decide) (by decide) (by decide +kernel) r hr

/-- `0^r 11011` as an eventual word: excluded for all `r ≥ 9` by parametric strip certificates. -/
theorem not_eventuallyWord_zeros_11011 (r : Nat) (hr : 9 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ [true, true, false, true, true]) :=
  Rule30ParametricStripCertificates.not_eventually_param_word false 9 [true, true, false, true, true] 6 2
    (by decide) (by decide) (by decide +kernel) r hr

/-- `0^r 101111` as an eventual word: excluded for all `r ≥ 9` by parametric strip certificates. -/
theorem not_eventuallyWord_zeros_101111 (r : Nat) (hr : 9 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ [true, false, true, true, true, true]) :=
  Rule30ParametricStripCertificates.not_eventually_param_word false 9 [true, false, true, true, true, true] 6 2
    (by decide) (by decide) (by decide +kernel) r hr

private theorem replicate_getD (r n : Nat) : (List.replicate r false).getD n false = false := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    cases n with
    | zero => simp [List.replicate_succ]
    | succ n => simpa only [List.replicate_succ, List.getD_cons_succ] using ih n

/-- An all-white word cannot be an eventual center pattern, including the empty word. -/
theorem not_eventuallyWord_all_white (u : List Bool)
    (hu : ∀ b, b ∈ u → b = false) : ¬ EventuallyWord u := by
  rintro ⟨T, hT⟩
  apply Rule30Prize.no_column_eventually_constant 0
  refine ⟨T, false, fun t ht => ?_⟩
  rw [hT t ht, List.eq_replicate_of_mem hu]
  exact replicate_getD _ _

/-- **No padded word**: for every tail `u`, the center column of the single seed is not
eventually the repeating word `0^r u` once `paddedBound u ≤ r`, whatever the transient. -/
theorem no_padded_word (u : List Bool) (r : Nat) (hr : paddedBound u ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ u) := by
  by_cases h11 : u = [true, true]
  · subst h11; exact not_eventuallyWord_zeros_11 r (by simpa [paddedBound] using hr)
  by_cases h1011 : u = [true, false, true, true]
  · subst h1011
    exact not_eventuallyWord_zeros_1011 r (by simpa [paddedBound, h11] using hr)
  by_cases h10011 : u = [true, false, false, true, true]
  · subst h10011
    exact not_eventuallyWord_zeros_10011 r (by simpa [paddedBound, h11, h1011] using hr)
  by_cases h10111 : u = [true, false, true, true, true]
  · subst h10111
    exact Rule30WhitePad10111.not_eventually_zeros_10111 r (by simpa [paddedBound, h11, h1011, h10011] using hr)
  by_cases h11011 : u = [true, true, false, true, true]
  · subst h11011
    exact not_eventuallyWord_zeros_11011 r (by simpa [paddedBound, h11, h1011, h10011, h10111] using hr)
  by_cases h101111 : u = [true, false, true, true, true, true]
  · subst h101111
    exact not_eventuallyWord_zeros_101111 r (by simpa [paddedBound, h11, h1011, h10011, h10111, h11011] using hr)
  by_cases h1 : u = [true]
  · subst h1
    exact not_eventuallyWord_zeros_one r (by simpa [paddedBound, h11, h1011, h10011, h10111, h11011, h101111] using hr)
  by_cases h1101 : u = [true, true, false, true]
  · subst h1101
    exact not_eventuallyWord_zeros_1101 r (by simpa [paddedBound, h11, h1011, h10011, h10111, h11011, h101111, h1] using hr)
  by_cases h1111 : u = [true, true, true, true]
  · subst h1111
    exact not_eventuallyWord_zeros_1111 r (by simpa [paddedBound, h11, h1011, h10011, h10111, h11011, h101111, h1, h1101] using hr)
  by_cases hblack : u = List.replicate u.length true ∧ 3 ≤ u.length
  · have hq : 17 ≤ r := by
      simpa only [paddedBound, ite_eq_right h11, ite_eq_right h1011, ite_eq_right h10011,
        ite_eq_right h10111, ite_eq_right h11011, ite_eq_right h101111, ite_eq_right h1,
        ite_eq_right h1101, ite_eq_right h1111, ite_eq_left hblack] using hr
    rw [hblack.1]
    exact no_padded_word_black _ hblack.2 r hq
  by_cases h4 : u.length ≤ 4
  · exact Rule30ShortTail.no_short_tail_seed u h4 r
      (by simpa [paddedBound, h11, h1011, h10011, h10111, h11011, h101111, h1, h1101, h1111, hblack, h4] using hr)
  by_cases h5 : u.length ≤ 5
  · exact Rule30FiveTail.no_five_tail_seed u h5 r
      (by simpa [paddedBound, h11, h1011, h10011, h10111, h11011, h101111, h1, h1101, h1111, hblack, h4, h5] using hr)
  by_cases h6 : u.length ≤ 6
  · exact Rule30SixTailSharpened.no_six_tail_seed u h6 r
      (by simpa [paddedBound, h11, h1011, h10011, h10111, h11011, h101111, h1, h1101, h1111, hblack, h4, h5, h6] using hr)
  have hq : Rule30ArbitraryWhitePadding.paddingThreshold u.length ≤ r := by
    simpa [paddedBound, h11, h1011, h10011, h10111, h11011, h101111, h1, h1101, h1111, hblack, h4, h5, h6] using hr
  by_cases hb : ∃ j, j < u.length ∧ u.getD j false = true
  · intro hw
    have hpos : 0 < (List.replicate r false ++ u).length := by
      obtain ⟨j, hj, _⟩ := hb
      simp only [List.length_append, List.length_replicate]
      omega
    exact Rule30ArbitraryWhitePadding.not_eventually_padded_word u r hb hq
      (eventuallyWord_swap hpos hw)
  · apply not_eventuallyWord_all_white
    intro b hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact (List.mem_replicate.mp hmem).2
    · cases b with
      | false => rfl
      | true =>
          obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hmem
          have hget : u.getD j false = true := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, he]
          exact False.elim (hb ⟨j, hj, hget⟩)

end Ruliology.CellularAutomata.Rule30PaddedWords
