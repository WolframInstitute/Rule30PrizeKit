module

public import Ruliology.CellularAutomata.Rule30RankedWords

/-!
# Rule 30: long black runs followed by tails read on a strip

A black run of at least nine cells shields the right half (`Rule30BlackRuns.nine_black`).
This module turns that shield into a composition rule for whole periods. Fix a strip width `K`
and a threshold `r0`, and let `longSet K r0` be the set of `K`-cell strips right of the center
that are reachable after `r0` black center cells, from any strip. Reading a tail `u` from that
set with `Rule30StripCertificates.image`, `tailOK K (longSet K r0) u` asks that before every
white letter of `u` all strips of the current set agree on column `1`.

* `not_eventually_longRunTails`: for every nonempty list of blocks `(r_i, u_i)` with `r_i ≥ r0`
  and `tailOK K (longSet K r0) u_i`, the center column is not eventually
  `1^(r_1) u_1 … 1^(r_k) u_k` repeated, whatever the transient. The number of blocks, every
  `r_i` and every tail length are unbounded.

* `not_eventually_pairTails`: the same for every nonempty list of blocks `(r_i, u_i)` with
  `r_i ≥ 9` and each `u_i` a white run `0^q` or a tail `0^a 1 1 0^c` with `a` odd; one block is
  `not_eventually_run_pair`.

The tails passing `tailOK` form a regular language. At `K = 5`, `r0 = 9` its minimal automaton
has 35 states and about `1.446^n` tails of length `n` pass (computation, not in this module).
Two families are proved here for every length, by lists of five, two and three strip sets that
are closed under the white and black steps and checked by the kernel: the white runs `0^q`
(`tail_white`) and the tails `0^a 1 1 0^c` with `a` odd and any `c` (`tail_odd_pair`). For the
white runs alone this is `Rule30BlackRuns.not_eventuallyPeriodic_of_long_one_runs`. With the
pair tails, for example `1^9 0^3 1 1 0^2` is excluded: its block `1 1` is followed by two white
cells and it has adjacent white letters, so it is neither a word of the pure blocks of
`Rule30GrammarRuns` nor of `Rule30RunTransitions`, whose white letters are isolated. The
language also contains `0 1 0 1^8 0^c`, where eight black cells after a known strip shield
again (checked for `c < 60`, not in this module).
`Rule30ParametricStripCertificates.paramBlackTable` and `Rule30BlackRunBlocks` exclude single
blocks `1^r u` with short tails; here different tails may follow different long runs. Each block
is `Rule30RankedWords.Ranked` with one rank and the full set as envelope, and
`Rule30RankedWords.no_word_ranked` with masked Jen concludes.

Contributed by Katip Kurtuluş with Claude (Anthropic), ChatGPT (OpenAI) and Gemini (Google).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30LongRunTails

open Rule30StripCertificates Rule30RunEnvelopes Rule30RankedWords Rule30MaskedJen Rule30Jen

/-- Reading `u` from the strip set `S`: before every white letter, column `1` is constant on the
current set. -/
def tailOK (K : Nat) : Nat → List Bool → Bool
  | _, [] => true
  | S, a :: u => (a || colConst K S false || colConst K S true) && tailOK K (image K a S) u

/-- The strips reachable after `r0` black center cells, from any strip. -/
def longSet (K r0 : Nat) : Nat := applyWord K (List.replicate r0 true) (fullSet K)

/-- The block `1^r u`. -/
def block (b : Nat × List Bool) : List Bool := List.replicate b.1 true ++ b.2

/-- The predicted masked output of the block `1^r u` at position `i`. -/
def blockOut (K r0 : Nat) (b : Nat × List Bool) (i : Nat) : Bool :=
  if i < b.1 then true
  else b.2.getD (i - b.1) false || colConst K (applyWord K (b.2.take (i - b.1)) (longSet K r0)) true

theorem tailOK_spec (K : Nat) : ∀ (u : List Bool) (S : Nat), tailOK K S u = true →
    ∀ ψ, ψ < u.length → u.getD ψ false = false →
      colConst K (applyWord K (u.take ψ) S) false = true ∨
        colConst K (applyWord K (u.take ψ) S) true = true
  | [], _, _, ψ, hψ, _ => absurd hψ (Nat.not_lt_zero _)
  | a :: u, S, h, ψ, hψ, hw => by
    rw [tailOK, Bool.and_eq_true] at h
    cases ψ with
    | zero =>
      have ha : a = false := by simpa using hw
      subst ha
      have h1 := h.1
      simp only [Bool.false_or, Bool.or_eq_true] at h1
      simpa [applyWord] using h1
    | succ ψ =>
      have hψ' : ψ < u.length := by simp only [List.length_cons] at hψ; omega
      have hw' : u.getD ψ false = false := by simpa using hw
      have := tailOK_spec K u (image K a S) h.2 ψ hψ' hw'
      simpa [List.take_succ_cons, applyWord] using this

theorem colConst_testBit {K S s : Nat} {b : Bool} (hc : colConst K S b = true) (hs : s < 2 ^ K)
    (hS : S.testBit s = true) : s.testBit 0 = b := by
  have h := allBelow_spec hc s hs
  simp only [hS, Bool.not_true, Bool.false_or, beq_iff_eq] at h
  exact h

theorem fullSet_code (K t : Nat) : (fullSet K).testBit (code K t) = true := by
  simp only [fullSet, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true (enc_encRow K t 0).1

theorem code_testBit_zero {K : Nat} (hK : 1 ≤ K) (t : Nat) :
    (code K t).testBit 0 = cell t 1 := by
  have h := (enc_encRow K t 0).2 0 (by omega)
  simpa using h

/-- **One block.** For `r ≥ r0` and a tail with `tailOK K (longSet K r0) u`, the block `1^r u` is
ranked with one rank, the full set as envelope and output `blockOut K r0 (r, u)`. -/
theorem block_ranked {K r0 : Nat} (hK : 1 ≤ K) {r : Nat} {u : List Bool} (hr : r0 ≤ r)
    (hu : tailOK K (longSet K r0) u = true) :
    Ranked K (fullSet K) (fun _ => 0) (block (r, u)) (fun _ i => blockOut K r0 (r, u) i) := by
  intro t ht _
  have hlen : (block (r, u)).length = r + u.length := by simp [block]
  refine ⟨fullSet_code K _, Nat.le_refl _, fun _ i hi => ?_⟩
  rw [hlen] at hi
  have hget : ∀ k, k < r + u.length → cell (t + k) 0 = (block (r, u)).getD k false :=
    fun k hk => ht k (by rw [hlen]; exact hk)
  by_cases hir : i < r
  · have hc : cell (t + i) 0 = true := by
      rw [hget i hi]
      simp [block, List.getD_eq_getElem?_getD, List.getElem?_append, hir]
    simp [blockOut, hir, orCol, hc]
  · have hψ : i - r < u.length := by omega
    have hRu : Reads (t + r) u := by
      intro k hk
      have := hget (r + k) (by omega)
      rw [show t + (r + k) = t + r + k by omega] at this
      rw [this]
      simp [block, List.getD_eq_getElem?_getD, List.getElem?_append, show ¬ r + k < r by omega]
    have hRb : Reads (t + (r - r0)) (List.replicate r0 true) := by
      intro k hk
      simp only [List.length_replicate] at hk
      have := hget (r - r0 + k) (by omega)
      rw [show t + (r - r0 + k) = t + (r - r0) + k by omega] at this
      rw [this]
      simp [block, List.getD_eq_getElem?_getD, List.getElem?_append,
        show r - r0 + k < r by omega, hk]
    have hX : (longSet K r0).testBit (code K (t + r)) = true := by
      have := code_word hRb (fullSet_code K (t + (r - r0)))
      simpa [longSet, show t + (r - r0) + r0 = t + r by omega] using this
    have hRp : Reads (t + r) (u.take (i - r)) := by
      have h2 : Reads (t + r) (u.take (i - r) ++ u.drop (i - r)) := by
        rw [List.take_append_drop]; exact hRu
      exact reads_left h2
    have hY := code_word hRp hX
    have hlt : (u.take (i - r)).length = i - r := by simp; omega
    rw [hlt, show t + r + (i - r) = t + i by omega] at hY
    have hci : cell (t + i) 0 = u.getD (i - r) false := by
      have := hRu (i - r) hψ
      rwa [show t + r + (i - r) = t + i by omega] at this
    have hs : code K (t + i) < 2 ^ K := (enc_encRow K (t + i) 0).1
    simp only [blockOut, hir, ↓reduceIte]
    cases hw : u.getD (i - r) false
    · have hcz : cell (t + i) 0 = false := by rw [hci, hw]
      have h1 : orCol 0 (t + i) = cell (t + i) 1 := by simp [orCol, hcz]
      rw [h1, ← code_testBit_zero hK, Bool.false_or]
      cases hct : colConst K (applyWord K (u.take (i - r)) (longSet K r0)) true
      · have hcf := (tailOK_spec K u _ hu (i - r) hψ hw).resolve_right (by simp [hct])
        exact colConst_testBit hcf hs hY
      · exact colConst_testBit hct hs hY
    · have hco : cell (t + i) 0 = true := by rw [hci, hw]
      simp [orCol, hco]

/-- **Any number of blocks.** -/
theorem blocks_ranked {K r0 : Nat} (hK : 1 ≤ K) :
    ∀ (bs : List (Nat × List Bool)),
      (∀ b ∈ bs, r0 ≤ b.1 ∧ tailOK K (longSet K r0) b.2 = true) →
        ∃ g, Ranked K (fullSet K) (fun _ => 0) (bs.flatMap block) g
  | [], _ => ⟨fun _ _ => false, by simpa using ranked_nil K (fullSet K) (fun _ => 0) _⟩
  | b :: bs, h => by
    obtain ⟨g, hg⟩ := blocks_ranked hK bs (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have hb := h b List.mem_cons_self
    have h1 := block_ranked (r := b.1) (u := b.2) hK hb.1 hb.2
    exact ⟨_, by simpa [List.flatMap_cons] using ranked_append h1 hg⟩

/-- **Long black runs with checked tails are excluded.** For every nonempty list of blocks
`(r_i, u_i)` with `r_i ≥ r0` and `tailOK K (longSet K r0) u_i`, the center column is not
eventually `1^(r_1) u_1 … 1^(r_k) u_k` repeated, whatever the transient. -/
theorem not_eventually_longRunTails {K r0 : Nat} (hK : 1 ≤ K) (hr0 : 1 ≤ r0)
    (bs : List (Nat × List Bool)) (hne : bs ≠ [])
    (h : ∀ b ∈ bs, r0 ≤ b.1 ∧ tailOK K (longSet K r0) b.2 = true) :
    ¬ EventuallyWord (bs.flatMap block) := by
  obtain ⟨g, hg⟩ := blocks_ranked hK bs h
  have hw : 0 < (bs.flatMap block).length := by
    obtain ⟨b, bs', rfl⟩ := List.exists_cons_of_ne_nil hne
    have := (h b List.mem_cons_self).1
    simp [List.flatMap_cons, block]
    omega
  exact no_word_ranked K (fullSet K) 0 (fun _ => 0) _ g hw (fun s hs => by simpa [iterW] using hs) hg

/-- The case `K = 5`, `r0 = 9`: after nine black cells the strip is `0 1 * * *` (`Rule30BlackRuns`'s
Lemma A), and tails are read on five cells. -/
theorem not_eventually_longRunTails_five (bs : List (Nat × List Bool)) (hne : bs ≠ [])
    (h : ∀ b ∈ bs, 9 ≤ b.1 ∧ tailOK 5 (longSet 5 9) b.2 = true) :
    ¬ EventuallyWord (bs.flatMap block) :=
  not_eventually_longRunTails (by decide) (by decide) bs hne h

/-- After nine black cells, the five-cell strip is `0 1 * * *`. -/
theorem longSet_five :
    longSet 5 9 = 2 ^ 2 + 2 ^ 6 + 2 ^ 10 + 2 ^ 14 + 2 ^ 18 + 2 ^ 22 + 2 ^ 26 + 2 ^ 30 := by
  decide +kernel

theorem tail_011000 : tailOK 5 (longSet 5 9) [false, true, true, false, false, false] = true := by
  decide +kernel

theorem tail_000100 : tailOK 5 (longSet 5 9) [false, false, false, true, false, false] = true := by
  decide +kernel

/-- Two different tails after long runs: `1^r 0 1 1 0 0 0 1^s 0 0 0 1 0 0` is excluded for all
`r, s ≥ 9`. -/
theorem not_eventually_two_tails (r s : Nat) (hr : 9 ≤ r) (hs : 9 ≤ s) :
    ¬ EventuallyWord (List.replicate r true ++ [false, true, true, false, false, false] ++
      (List.replicate s true ++ [false, false, false, true, false, false])) := by
  have h := not_eventually_longRunTails_five
    [(r, [false, true, true, false, false, false]), (s, [false, false, false, true, false, false])]
    (by simp) (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact ⟨hr, tail_011000⟩
      · exact ⟨hs, tail_000100⟩)
  simpa [block, List.flatMap_cons, List.append_assoc] using h

/-! ### Tail families for every length

The white step `image 5 false` and the black step `image 5 true` move `longSet 5 9` through a few
strip sets only. Lists of strip sets closed under these steps, checked by the kernel, turn finitely
many evaluations into tails of every length. -/

/-- Reading a tail in two parts. -/
theorem tailOK_append (K : Nat) :
    ∀ (u v : List Bool) (S : Nat),
      tailOK K S (u ++ v) = (tailOK K S u && tailOK K (applyWord K u S) v)
  | [], v, S => by simp [tailOK, applyWord]
  | a :: u, v, S => by
      simp only [List.cons_append, tailOK, applyWord, tailOK_append K u v (image K a S),
        Bool.and_assoc]

/-- A list of strip sets closed under the white step, each fixing column `1`: every white run read
from a member passes `tailOK` and ends in the list. -/
theorem white_closed {K : Nat} {Q : List Nat}
    (hc : ∀ S ∈ Q, image K false S ∈ Q)
    (hk : ∀ S ∈ Q, (colConst K S false || colConst K S true) = true) :
    ∀ (q S : Nat), S ∈ Q →
      tailOK K S (List.replicate q false) = true ∧
        applyWord K (List.replicate q false) S ∈ Q
  | 0, S, hS => by simp [tailOK, applyWord, hS]
  | q + 1, S, hS => by
      obtain ⟨h1, h2⟩ := white_closed hc hk q (image K false S) (hc S hS)
      refine ⟨?_, ?_⟩
      · simp only [List.replicate_succ, tailOK, Bool.false_or, h1, Bool.and_true]
        exact hk S hS
      · simpa only [List.replicate_succ, applyWord] using h2

/-- A list closed under two white steps keeps every even white run read from a member. -/
theorem even_white_closed {K : Nat} {Q : List Nat}
    (hc : ∀ S ∈ Q, image K false (image K false S) ∈ Q) :
    ∀ (k S : Nat), S ∈ Q → applyWord K (List.replicate (2 * k) false) S ∈ Q
  | 0, S, hS => by simpa [applyWord] using hS
  | k + 1, S, hS => by
      have h := even_white_closed hc k _ (hc S hS)
      have e : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [e]
      simpa only [List.replicate_succ, applyWord] using h

/-- The white orbit of `longSet 5 9`: five strip sets, then period two. -/
def whiteOrbit : List Nat := [1145324612, 2290616456, 572654114, 2821234728, 539107874]

/-- The strip sets after an odd white run from `longSet 5 9`. -/
def oddSets : List Nat := [2290616456, 2821234728]

/-- The strip sets after an odd white run, two black cells and any white run. -/
def pairSets : List Nat := [2726469762, 170557994, 2821366314]

theorem longSet_mem : longSet 5 9 ∈ whiteOrbit := by decide +kernel

theorem whiteOrbit_closed : ∀ S ∈ whiteOrbit, image 5 false S ∈ whiteOrbit := by decide +kernel

theorem whiteOrbit_const :
    ∀ S ∈ whiteOrbit, (colConst 5 S false || colConst 5 S true) = true := by decide +kernel

theorem oddSets_start : image 5 false (longSet 5 9) ∈ oddSets := by decide +kernel

theorem oddSets_closed : ∀ S ∈ oddSets, image 5 false (image 5 false S) ∈ oddSets := by
  decide +kernel

theorem pairSets_entry : ∀ S ∈ oddSets, image 5 true (image 5 true S) ∈ pairSets := by
  decide +kernel

theorem pairSets_closed : ∀ S ∈ pairSets, image 5 false S ∈ pairSets := by decide +kernel

theorem pairSets_const :
    ∀ S ∈ pairSets, (colConst 5 S false || colConst 5 S true) = true := by decide +kernel

/-- **White runs.** After nine black cells every white run `0^q` passes. -/
theorem tail_white (q : Nat) : tailOK 5 (longSet 5 9) (List.replicate q false) = true :=
  (white_closed whiteOrbit_closed whiteOrbit_const q _ longSet_mem).1

/-- **Odd white run, two black cells, any white run.** After nine black cells the tail
`0^a 1 1 0^c` passes for every odd `a` and every `c`. -/
theorem tail_odd_pair (a c : Nat) (ha : a % 2 = 1) :
    tailOK 5 (longSet 5 9)
      (List.replicate a false ++ true :: true :: List.replicate c false) = true := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  have hA := (white_closed whiteOrbit_closed whiteOrbit_const (2 * k + 1) _ longSet_mem).1
  have hodd : applyWord 5 (List.replicate (2 * k + 1) false) (longSet 5 9) ∈ oddSets := by
    simpa only [List.replicate_succ, applyWord] using
      even_white_closed oddSets_closed k _ oddSets_start
  rw [tailOK_append, hA, Bool.true_and]
  simp only [tailOK, Bool.true_or, Bool.true_and]
  exact (white_closed pairSets_closed pairSets_const c _ (pairSets_entry _ hodd)).1

/-- The tails proved here for every length: a white run `0^q`, or `0^a 1 1 0^c` with `a` odd. -/
def PairTail (u : List Bool) : Prop :=
  (∃ q, u = List.replicate q false) ∨
    ∃ a c, a % 2 = 1 ∧ u = List.replicate a false ++ true :: true :: List.replicate c false

theorem pairTail_ok {u : List Bool} (h : PairTail u) : tailOK 5 (longSet 5 9) u = true := by
  rcases h with ⟨q, rfl⟩ | ⟨a, c, ha, rfl⟩
  · exact tail_white q
  · exact tail_odd_pair a c ha

/-- **Long runs with pair tails.** For every nonempty list of blocks `(r_i, u_i)` with `r_i ≥ 9`
and each `u_i` a white run or `0^a 1 1 0^c` with `a` odd, the center column is not eventually
`1^(r_1) u_1 … 1^(r_k) u_k` repeated, whatever the transient. -/
theorem not_eventually_pairTails (bs : List (Nat × List Bool)) (hne : bs ≠ [])
    (h : ∀ b ∈ bs, 9 ≤ b.1 ∧ PairTail b.2) : ¬ EventuallyWord (bs.flatMap block) :=
  not_eventually_longRunTails_five bs hne fun b hb => ⟨(h b hb).1, pairTail_ok (h b hb).2⟩

/-- One block: `1^r 0^a 1 1 0^c` is excluded for every `r ≥ 9`, every odd `a` and every `c`. -/
theorem not_eventually_run_pair (r a c : Nat) (hr : 9 ≤ r) (ha : a % 2 = 1) :
    ¬ EventuallyWord (List.replicate r true ++
      (List.replicate a false ++ true :: true :: List.replicate c false)) := by
  have h := not_eventually_pairTails
    [(r, List.replicate a false ++ true :: true :: List.replicate c false)] (by simp) (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨hr, Or.inr ⟨a, c, ha, rfl⟩⟩)
  simpa only [block, List.flatMap_cons, List.flatMap_nil, List.append_nil] using h

end Rule30LongRunTails
end Ruliology.CellularAutomata
