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

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

def reshield11 : List Bool := [false, true, false, true, true, true, true, true, true, true, true]
def reach80Sets : List Nat := [0x44444444, 0x88880888, 0x44440444, 0x22220222, 0x11110111, 0xa828a028, 0x54145014, 0x51415041, 0xa282a082, 0x20222222, 0x10111111, 0xc0c848c8, 0xc0c484c4, 0x9491849, 0x6862486, 0xa2a822a, 0x5154115, 0x15150515, 0x45450545, 0x17962592, 0x45554554, 0xa82aa22a, 0x54155115, 0xd1c95889, 0xe2c6a446, 0xd9c158c1, 0xe6c2a4c2, 0x99891889, 0x66462446, 0xe595e594, 0xd9c85888, 0xe6c4a444, 0xd1c958c9, 0xe2c6a4c6, 0x13972197, 0x44554455, 0x7872587, 0x5154515, 0x13932193, 0x44544454, 0xe7d5a555, 0x11952195, 0x17972597, 0x45554555, 0xe7d7e1d6, 0xc9c94889, 0xc6c68446, 0x67576556, 0xd9c95889, 0xe6c6a446, 0xa797e196, 0xc8c84888, 0xc4c48444, 0xe6d7e457, 0xe3d3a1d2, 0xe7d7e5d6, 0xe7d5e555, 0x13172117, 0x44454445, 0xe6d4e454, 0x11150115, 0x44450445, 0xc6d7c457, 0xa795e515, 0xe6d6e0d6, 0x89890889, 0x46460446, 0xc4d5c455, 0xd1c150c1, 0xe2c2a0c2, 0xc6c7c447, 0xc5d5c555, 0x13132113, 0xc6c78447, 0x46474447, 0xe6c7a447, 0xa696e096, 0x46464446, 0x46574457, 0xc6c6c446]
def reach80To35 : List Nat := [0, 1, 0, 2, 3, 1, 4, 5, 6, 2, 3, 7, 8, 9, 10, 11, 12, 13, 14, 15, 12, 11, 5, 9, 16, 15, 10, 9, 17, 18, 9, 16, 9, 10, 15, 19, 18, 12, 15, 20, 21, 15, 15, 12, 18, 22, 23, 21, 9, 16, 18, 7, 23, 24, 18, 18, 21, 25, 26, 24, 13, 26, 27, 21, 28, 22, 29, 27, 15, 10, 30, 31, 25, 30, 32, 33, 28, 29, 34, 23]
def reach80Next0 : List Nat := [1, 3, 1, 5, 7, 9, 11, 13, 15, 5, 7, 80, 80, 80, 80, 21, 23, 25, 27, 80, 30, 21, 32, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 45, 80, 48, 80, 51, 80, 80, 80, 48, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 65, 80, 68, 65, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80, 80]
def reach80Next1 : List Nat := [2, 4, 2, 6, 8, 10, 12, 14, 16, 6, 8, 17, 18, 19, 20, 22, 24, 26, 28, 29, 31, 22, 33, 34, 35, 36, 37, 38, 39, 40, 41, 35, 42, 43, 44, 46, 47, 49, 50, 52, 53, 54, 55, 49, 56, 57, 58, 59, 34, 35, 56, 60, 61, 62, 63, 56, 53, 64, 66, 67, 69, 66, 70, 53, 71, 72, 0, 73, 36, 37, 74, 75, 76, 74, 77, 78, 71, 0, 79, 58]
def minDfa35Next0 : List Nat := [1, 2, 1, 5, 7, 9, 11, 35, 35, 35, 35, 11, 9, 15, 9, 35, 35, 35, 35, 22, 7, 35, 35, 35, 35, 35, 22, 35, 35, 35, 35, 35, 35, 35, 35]
def minDfa35Next1 : List Nat := [0, 3, 4, 6, 8, 10, 12, 13, 14, 15, 12, 5, 16, 10, 17, 18, 19, 20, 21, 23, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 32, 33, 29, 34, 23]
def minDfa35Wt : List Nat := [1545, 691, 619, 381, 204, 152, 399, 118, 177, 56, 164, 340, 237, 170, 256, 81, 287, 314, 117, 414, 454, 169, 60, 539, 244, 86, 780, 353, 124, 1068, 510, 179, 738, 258, 373]
def tail5DistSuffixes : List (List Bool) := [[false, true, false, false], [true, false, false], [false, false, false], [false, false], [false], [false, true, false], [true, true, true, true, false, false], [true, true, true, true, true, true, false, false], [false, true, true, true, true, true, true, true, true, false], [true, true, false, true, false], [true, true, false, false], [true, true, true, true, true, true, true, false, false], [true, true, true, false, true, false], [true, false], [true, true, true, true, true, false, false], [true, false, true, false], [true, true, true, false, false], [true, true, true, true, true, true, true, true, false], [true, true, true, true, true, true, true, false], [true, true, true, true, true, true, false], [true, true, true, true, true, false], [true, true, true, true, false], [true, true, true, false], [true, true, false]]
def white35Closed : List Nat := [0, 1, 2]

def tail5MinDfaStep (q : Nat) (b : Bool) : Option Nat :=
  let v := if b then minDfa35Next1.getD q 35 else minDfa35Next0.getD q 35
  if v < 35 then some v else none

def tail5MinDfaRun : Nat → List Bool → Option Nat
  | q, [] => some q
  | q, b :: bs => match tail5MinDfaStep q b with
    | some q' => tail5MinDfaRun q' bs
    | none => none

def tail5MinDfaAccepts (q : Nat) (u : List Bool) : Bool := (tail5MinDfaRun q u).isSome

def tail5MinDfaWords (q : Nat) : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let l0 := match tail5MinDfaStep q false with | some q' => (tail5MinDfaWords q' n).map (false :: ·) | none => []
    let l1 := match tail5MinDfaStep q true with | some q' => (tail5MinDfaWords q' n).map (true :: ·) | none => []
    l0 ++ l1

def tail5LoopTile0 : List Bool := [false, true, true, true, true, true, true, true, true, true]
def tail5LoopTile1 : List Bool := [true, true, true, true, true, true, true, true, true, true]
def tail5TileCode (bs : List Bool) : List Bool := bs.flatMap (fun b => if b then tail5LoopTile1 else tail5LoopTile0)

private theorem replicate_snoc_loc : ∀ (n : Nat) (a : Bool), List.replicate (n + 1) a = List.replicate n a ++ [a]
  | 0, _ => rfl
  | n + 1, a => congrArg (a :: ·) (replicate_snoc_loc n a)

private theorem applyWord_append_loc (K : Nat) : ∀ (u v : List Bool) (S : Nat),
    applyWord K (u ++ v) S = applyWord K v (applyWord K u S)
  | [], _, _ => rfl
  | a :: u, v, S => applyWord_append_loc K u v (image K a S)

private theorem tailOK_append_loc (K : Nat) : ∀ (u v : List Bool) (S : Nat),
    tailOK K S (u ++ v) = (tailOK K S u && tailOK K (applyWord K u S) v)
  | [], _, _ => by simp [tailOK, applyWord]
  | a :: u, v, S => by
    simp only [List.cons_append, tailOK, applyWord, tailOK_append_loc K u v (image K a S), Bool.and_assoc]

theorem longSet5_ten_stabilizes (d : Nat) :
    longSet 5 9 = 0x44444444 ∧ longSet 5 (10 + d) = 0x44440444 := by
  refine ⟨by decide +kernel, ?_⟩
  induction d with
  | zero => decide +kernel
  | succ d ih =>
    have hrep : List.replicate (10 + (d + 1)) true = List.replicate (10 + d) true ++ [true] := by
      rw [show 10 + (d + 1) = (10 + d) + 1 by omega]; exact replicate_snoc_loc (10 + d) true
    unfold longSet
    rw [hrep, applyWord_append_loc]
    change image 5 true (longSet 5 (10 + d)) = 0x44440444
    rw [ih]; decide +kernel

private theorem reach80_sim_ok :
    (reach80Sets.getD 0 0 == longSet 5 9) && (reach80To35.getD 0 35 == 0) &&
    (List.range 80).all (fun i =>
      let S := reach80Sets.getD i 0
      let q := reach80To35.getD i 35
      let j0 := reach80Next0.getD i 80
      let j1 := reach80Next1.getD i 80
      q < 35 && j1 < 80 && (image 5 true S == reach80Sets.getD j1 0) &&
      (tail5MinDfaStep q true == some (reach80To35.getD j1 35)) &&
      (if colConst 5 S false || colConst 5 S true then
        j0 < 80 && (image 5 false S == reach80Sets.getD j0 0) &&
        (tail5MinDfaStep q false == some (reach80To35.getD j0 35))
      else tail5MinDfaStep q false == none)) = true := by decide +kernel

private theorem reach80_bisim (u : List Bool) :
    ∀ i, i < 80 → tailOK 5 (reach80Sets.getD i 0) u = tail5MinDfaAccepts (reach80To35.getD i 35) u := by
  induction u with
  | nil => intro i _; rfl
  | cons a rest ih =>
    intro i hi
    have hall := reach80_sim_ok
    simp only [Bool.and_eq_true] at hall
    have h := List.all_eq_true.mp hall.2 i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    cases a
    · simp only [tailOK, Bool.false_or]
      have h2 := h.2
      cases hc : (colConst 5 (reach80Sets.getD i 0) false || colConst 5 (reach80Sets.getD i 0) true)
      · rw [hc] at h2; simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at h2
        unfold tail5MinDfaAccepts tail5MinDfaRun; rw [h2]; rfl
      · rw [hc] at h2; simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
        simp only [Bool.true_and, h2.1.2]
        unfold tail5MinDfaAccepts tail5MinDfaRun; rw [h2.2]
        exact ih _ h2.1.1
    · simp only [tailOK, Bool.true_or, Bool.true_and, h.1.1.2, tail5MinDfaAccepts, tail5MinDfaRun, h.1.2]
      exact ih _ h.1.1.1.2

theorem tailOK5_iff_minDfa35 (u : List Bool) :
    tailOK 5 (longSet 5 9) u = true ↔ tail5MinDfaAccepts 0 u = true := by
  have hall := reach80_sim_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  have h0 := reach80_bisim u 0 (by decide)
  rw [hall.1.1, hall.1.2] at h0
  rw [h0]

theorem tail5MinDfa_minimal_35 :
    ∀ p q : Fin 35, p ≠ q → ∃ w ∈ tail5DistSuffixes, tail5MinDfaAccepts p.val w ≠ tail5MinDfaAccepts q.val w := by
  have hok : (List.range 35).all (fun p => (List.range 35).all (fun q =>
      (p == q) || tail5DistSuffixes.any (fun w => tail5MinDfaAccepts p w != tail5MinDfaAccepts q w))) = true := by
    decide +kernel
  intro p q hpq
  have hp := List.all_eq_true.mp hok p.val (List.mem_range.mpr p.isLt)
  have hq := List.all_eq_true.mp hp q.val (List.mem_range.mpr q.isLt)
  have hne : (p.val == q.val) = false := beq_eq_false_iff_ne.mpr (fun e => hpq (Fin.ext e))
  simp only [hne, Bool.false_or] at hq
  obtain ⟨w, hw, hsep⟩ := List.any_eq_true.mp hq
  exact ⟨w, hw, bne_iff_ne.mp hsep⟩

private theorem white35Closed_ok :
    (0 ∈ white35Closed) ∧
    (white35Closed.all (fun q => match tail5MinDfaStep q false with | some q' => decide (q' ∈ white35Closed) | none => false)) = true := by
  decide +kernel

private theorem tail5MinDfa_run_append : ∀ (u v : List Bool) (q : Nat),
    tail5MinDfaRun q (u ++ v) = match tail5MinDfaRun q u with | some q' => tail5MinDfaRun q' v | none => none
  | [], _, _ => rfl
  | b :: bs, v, q => by
    simp only [List.cons_append, tail5MinDfaRun]
    cases tail5MinDfaStep q b with | none => rfl | some q' => exact tail5MinDfa_run_append bs v q'

private theorem tail5_white_from_zero (c : Nat) : tailOK 5 (longSet 5 9) (List.replicate c false) = true := by
  rw [tailOK5_iff_minDfa35]
  have hclosed : ∀ k, ∃ q ∈ white35Closed, tail5MinDfaRun 0 (List.replicate k false) = some q := by
    intro k; induction k with
    | zero => exact ⟨0, white35Closed_ok.1, rfl⟩
    | succ k ih =>
      obtain ⟨q, hqm, hr⟩ := ih
      have hstep_ok : (match tail5MinDfaStep q false with | some q' => decide (q' ∈ white35Closed) | none => false) = true :=
        List.all_eq_true.mp white35Closed_ok.2 q hqm
      rw [replicate_snoc_loc k false, tail5MinDfa_run_append, hr]
      dsimp only [tail5MinDfaRun]
      cases hst : tail5MinDfaStep q false with
      | none => rw [hst] at hstep_ok; simp at hstep_ok
      | some q' => rw [hst] at hstep_ok; exact ⟨q', decide_eq_true_eq.mp hstep_ok, rfl⟩
  obtain ⟨q, _, hr⟩ := hclosed c
  simp [tail5MinDfaAccepts, hr]

theorem tail_010_eight_black_reshield (r m c : Nat) (hr : 9 ≤ r) :
    tailOK 5 (longSet 5 9) ((List.replicate m reshield11).flatten ++ List.replicate c false) = true ∧
    ¬ EventuallyWord (List.replicate r true ++
        ((List.replicate m reshield11).flatten ++ List.replicate c false)) := by
  have h1 : tailOK 5 (longSet 5 9) reshield11 = true ∧ applyWord 5 reshield11 (longSet 5 9) = longSet 5 9 := by
    decide +kernel
  have hiter : ∀ k (u : List Bool), tailOK 5 (longSet 5 9) u = true →
      tailOK 5 (longSet 5 9) ((List.replicate k reshield11).flatten ++ u) = true := by
    intro k; induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
      rw [tailOK_append_loc, h1.1, h1.2, Bool.true_and]
      exact ih u hu
  have hok := hiter m (List.replicate c false) (tail5_white_from_zero c)
  refine ⟨hok, ?_⟩
  have hex := not_eventually_longRunTails_five [(r, (List.replicate m reshield11).flatten ++ List.replicate c false)]
    (by simp) (by intro b hb; simp only [List.mem_singleton] at hb; subst hb; exact ⟨hr, hok⟩)
  simpa only [block, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hex

private theorem minDfa35_wt_ok :
    (List.range 35).all (fun q =>
      let wq := minDfa35Wt.getD q 0
      let ok0 := match tail5MinDfaStep q false with | some q' => decide (q' < 35) | none => true
      let ok1 := match tail5MinDfaStep q true with | some q' => decide (q' < 35) | none => true
      let s0 := match tail5MinDfaStep q false with | some q' => minDfa35Wt.getD q' 0 | none => 0
      let s1 := match tail5MinDfaStep q true with | some q' => minDfa35Wt.getD q' 0 | none => 0
      ok0 && ok1 && decide (38 * (s0 + s1) ≤ 55 * wq)) = true := by decide +kernel

private theorem mem_tail5MinDfaWords_of_run : ∀ (w : List Bool) (q : Nat),
    (tail5MinDfaRun q w).isSome = true → w ∈ tail5MinDfaWords q w.length
  | [], q, _ => by simp [tail5MinDfaWords]
  | b :: bs, q, hr => by
    simp only [tail5MinDfaRun] at hr
    cases hst : tail5MinDfaStep q b with
    | none => rw [hst] at hr; simp at hr
    | some q' =>
      rw [hst] at hr
      have hsub := mem_tail5MinDfaWords_of_run bs q' hr
      cases b <;> simp [tail5MinDfaWords, hst, hsub]

private theorem nodup_len_le_loc {α : Type} [DecidableEq α] : ∀ (xs ys : List α),
    xs.Nodup → (∀ z ∈ xs, z ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    obtain ⟨hxn, hnd'⟩ := List.nodup_cons.mp hnd
    have hx : x ∈ ys := hsub x List.mem_cons_self
    have hle := nodup_len_le_loc xs (ys.erase x) hnd' (fun z hz =>
      (List.mem_erase_of_ne (fun e => hxn (by subst e; exact hz))).mpr (hsub z (List.mem_cons_of_mem _ hz)))
    have her := List.length_erase_of_mem hx
    have hpos : 0 < ys.length := List.length_pos_of_mem hx
    simp only [List.length_cons]; omega

private def allBoolsLoc : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBoolsLoc k).map (false :: ·) ++ (allBoolsLoc k).map (true :: ·)

private theorem allBoolsLoc_props (k : Nat) : (allBoolsLoc k).length = 2 ^ k ∧ (allBoolsLoc k).Nodup ∧
    ∀ bs ∈ allBoolsLoc k, bs.length = k := by
  induction k with
  | zero => exact ⟨rfl, by decide, by intro bs h; simp [allBoolsLoc] at h; subst h; rfl⟩
  | succ k ih =>
    rcases ih with ⟨hl, hn, hmem⟩
    refine ⟨by simp [allBoolsLoc, hl, Nat.pow_succ]; omega, List.nodup_append.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · exact List.Pairwise.map (false :: ·) (fun _ _ hne heq => hne (List.cons.inj heq).2) hn
    · exact List.Pairwise.map (true :: ·) (fun _ _ hne heq => hne (List.cons.inj heq).2) hn
    · intro x hx y hy heq; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy; cases heq
    · intro bs hbs; simp [allBoolsLoc] at hbs; rcases hbs with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> simp [hmem a ha]

private theorem list_append_cancel_eq {α : Type} : ∀ {u1 u2 v1 v2 : List α},
    u1.length = u2.length → u1 ++ v1 = u2 ++ v2 → u1 = u2 ∧ v1 = v2
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | a :: u1, b :: u2, v1, v2, hl, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨e1, e2⟩ := list_append_cancel_eq (by simp at hl; omega) h.2
    exact ⟨by rw [h.1, e1], e2⟩

theorem tailOK5_pinch_and_excluded_codes (n k r : Nat) (hr : 9 ≤ r) (bs : List Bool) :
    (tail5MinDfaWords 0 n).length * 38 ^ n ≤ 1545 * 55 ^ n ∧
    2 ^ k ≤ (tail5MinDfaWords 0 (10 * k)).length ∧
    ¬ EventuallyWord (List.replicate r true ++ tail5TileCode bs) := by
  have hwt1 : (List.range 35).all (fun q => decide (1 ≤ minDfa35Wt.getD q 0)) = true := by decide +kernel
  have hupper : ∀ m q, q < 35 → (tail5MinDfaWords q m).length * 38 ^ m ≤ (minDfa35Wt.getD q 0) * 55 ^ m := by
    intro m; induction m with
    | zero => intro q hq; simp [tail5MinDfaWords]; exact decide_eq_true_eq.mp (List.all_eq_true.mp hwt1 q (List.mem_range.mpr hq))
    | succ m ih =>
      intro q hq
      have hw := List.all_eq_true.mp minDfa35_wt_ok q (List.mem_range.mpr hq)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      have hb0 : (match tail5MinDfaStep q false with | some q' => (tail5MinDfaWords q' m).map (false :: ·) | none => []).length * 38 ^ m ≤
          (match tail5MinDfaStep q false with | some q' => minDfa35Wt.getD q' 0 | none => 0) * 55 ^ m := by
        cases hst : tail5MinDfaStep q false with
        | none => simp
        | some q' => rw [hst] at hw; simp only [List.length_map]; exact ih q' (by simpa using hw.1.1)
      have hb1 : (match tail5MinDfaStep q true with | some q' => (tail5MinDfaWords q' m).map (true :: ·) | none => []).length * 38 ^ m ≤
          (match tail5MinDfaStep q true with | some q' => minDfa35Wt.getD q' 0 | none => 0) * 55 ^ m := by
        cases hst : tail5MinDfaStep q true with
        | none => simp
        | some q' => rw [hst] at hw; simp only [List.length_map]; exact ih q' (by simpa using hw.1.2)
      simp only [tail5MinDfaWords, List.length_append, Nat.pow_succ]
      have hpf : ∀ {A B W0 W1 Wq pm qm : Nat},
          A * qm ≤ W0 * pm → B * qm ≤ W1 * pm → 38 * (W0 + W1) ≤ 55 * Wq → (A + B) * (qm * 38) ≤ Wq * (pm * 55) := by
        intro A B W0 W1 Wq pm qm g0 g1 gw
        have gsum : (A + B) * qm ≤ (W0 + W1) * pm := by
          rw [Nat.add_mul, Nat.add_mul]; exact Nat.add_le_add g0 g1
        calc (A + B) * (qm * 38) = 38 * ((A + B) * qm) := by rw [← Nat.mul_assoc, Nat.mul_comm _ 38]
          _ ≤ 38 * ((W0 + W1) * pm) := Nat.mul_le_mul_left 38 gsum
          _ = (38 * (W0 + W1)) * pm := by rw [← Nat.mul_assoc]
          _ ≤ (55 * Wq) * pm := Nat.mul_le_mul_right pm gw
          _ = Wq * (pm * 55) := by rw [Nat.mul_comm 55 Wq, Nat.mul_assoc, Nat.mul_comm pm 55]
      exact hpf hb0 hb1 hw.2
  have hloops : tail5MinDfaRun 0 tail5LoopTile0 = some 0 ∧ tail5MinDfaRun 0 tail5LoopTile1 = some 0 ∧
      tail5LoopTile0.length = 10 ∧ tail5LoopTile1.length = 10 ∧ tail5LoopTile0 ≠ tail5LoopTile1 := by decide +kernel
  have hcode_run : ∀ xs : List Bool, tail5MinDfaRun 0 (tail5TileCode xs) = some 0 ∧ (tail5TileCode xs).length = 10 * xs.length := by
    intro xs; induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons b rest ih =>
      have hc : tail5TileCode (b :: rest) = (if b then tail5LoopTile1 else tail5LoopTile0) ++ tail5TileCode rest := rfl
      refine ⟨?_, ?_⟩
      · rw [hc, tail5MinDfa_run_append]; cases b <;> simp [hloops.1, hloops.2.1, ih.1]
      · rw [hc, List.length_append, ih.2, List.length_cons]; cases b <;> simp [hloops.2.2.1, hloops.2.2.2.1] <;> omega
  have hcode_inj : ∀ xs ys : List Bool, tail5TileCode xs = tail5TileCode ys → xs = ys := by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => rfl | cons b rest =>
      have hc := (hcode_run (b :: rest)).2; rw [← h] at hc; simp [tail5TileCode] at hc
    | cons a xs ih =>
      intro ys h; cases ys with
      | nil => have hc := (hcode_run (a :: xs)).2; rw [h] at hc; simp [tail5TileCode] at hc
      | cons b ys =>
        have ha : tail5TileCode (a :: xs) = (if a then tail5LoopTile1 else tail5LoopTile0) ++ tail5TileCode xs := rfl
        have hb : tail5TileCode (b :: ys) = (if b then tail5LoopTile1 else tail5LoopTile0) ++ tail5TileCode ys := rfl
        rw [ha, hb] at h
        have hlen_eq : (if a then tail5LoopTile1 else tail5LoopTile0).length = (if b then tail5LoopTile1 else tail5LoopTile0).length := by
          cases a <;> cases b <;> rfl
        obtain ⟨ht, hrest⟩ := list_append_cancel_eq hlen_eq h
        have hab : a = b := by cases a <;> cases b <;> simp_all [hloops.2.2.2.2, Ne.symm hloops.2.2.2.2]
        rw [hab, ih ys hrest]
  obtain ⟨hlen_b, hnd_b, hmem_b⟩ := allBoolsLoc_props k
  let img := (allBoolsLoc k).map tail5TileCode
  have hnd_img : img.Nodup := List.Pairwise.map tail5TileCode (fun _ _ hne heq => hne (hcode_inj _ _ heq)) hnd_b
  have hsub_img : ∀ w ∈ img, w ∈ tail5MinDfaWords 0 (10 * k) := by
    intro w hw; obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hr_xs, hl_xs⟩ := hcode_run xs
    have hmem_w := mem_tail5MinDfaWords_of_run (tail5TileCode xs) 0 (by simp [hr_xs])
    rwa [hl_xs, hmem_b xs hxs] at hmem_w
  have hlow : 2 ^ k ≤ (tail5MinDfaWords 0 (10 * k)).length := by
    have hle := nodup_len_le_loc img (tail5MinDfaWords 0 (10 * k)) hnd_img hsub_img
    simpa [img, List.length_map, hlen_b] using hle
  have hok_bs : tailOK 5 (longSet 5 9) (tail5TileCode bs) = true := by
    rw [tailOK5_iff_minDfa35]; simp [tail5MinDfaAccepts, (hcode_run bs).1]
  have hex := not_eventually_longRunTails_five [(r, tail5TileCode bs)] (by simp) (by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact ⟨hr, hok_bs⟩)
  have hu0 : (tail5MinDfaWords 0 n).length * 38 ^ n ≤ 1545 * 55 ^ n := by
    have h0 := hupper n 0 (by decide)
    rwa [show minDfa35Wt.getD 0 0 = 1545 from rfl] at h0
  exact ⟨hu0, hlow, by simpa only [block, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hex⟩

end Rule30LongRunTails
end Ruliology.CellularAutomata
