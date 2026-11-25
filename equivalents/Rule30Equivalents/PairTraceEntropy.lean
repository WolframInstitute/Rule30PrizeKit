module

public import Rule30Equivalents.Mixing

/-!
# Rule 30 entropy from two adjacent columns

Let Nₐ(n) count the words of length n observed at columns a and a + 1 as the initial
configuration ranges over all Boolean rows on ℤ. The full map has topological entropy
equal to the exponential growth rate of Nₐ. Every positive block length k gives the
upper bound log(Nₐ(k))/k.

The pair identity appears in catalogue §7 item 11 and in the October 2026
[Rule 30 notes, §8.77](https://github.com/ghywel/placego/blob/main/archived/reports/rule30-prize/RULE30-PRIZE-8.2.md).
For the width-(2r+1) trace of a permutive cellular automaton, see Di Lena and Margara,
[Row subshifts and topological entropy of cellular automata](https://www.cs.unibo.it/~margara/page14/assets/01-JCA07.pdf)
(2007), Corollary 4.6.
Here left permutivity lets the kit's window-cover proof work with two columns.

A weighted reverse cover gives an upper bound for all block lengths at once. Reading
pair letters backwards, it covers each physical word. If the four successor weights
sum to at most p/q times the current weight, the entropy is at most log(p/q).
A five-site strip with 140 states gives p/q = 1679211/714866, below 47/20.
The logs in the Lean statements are natural logarithms.

Contributed by Gareth Herbert with Claude (Anthropic) and GPT (OpenAI).
-/

@[expose] public section

namespace Rule30Equivalents.PairTraceEntropy

open Filter Topology Dynamics Uniformity Ruliology.CellularAutomata Rule30Realization
open Rule30Equivalents.Mixing

/-- A pair word of length m+n injects into its prefix and restarted suffix. -/
theorem card_pairWords_add_le (a : ℤ) (m n : ℕ) :
    (pairWords a (m + n)).card ≤ (pairWords a m).card * (pairWords a n).card := by
  classical
  let split (w : Fin (m + n) → Bool × Bool) :=
    ((fun i : Fin m => w ⟨i.val, by omega⟩), (fun i : Fin n => w ⟨m + i.val, by omega⟩))
  have inject : Function.Injective split := by
    intro u v h
    funext i
    by_cases hlt : i.val < m
    · exact congrFun (congrArg Prod.fst h) ⟨i.val, hlt⟩
    · have e := congrFun (congrArg Prod.snd h) ⟨i.val - m, by omega⟩
      simpa [split, Nat.add_sub_of_le (by omega : m ≤ i.val)] using e
  have maps : (pairWords a (m + n)).image split ⊆ (pairWords a m) ×ˢ (pairWords a n) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨x, rfl⟩ := mem_pairWords.mp hv
    refine Finset.mem_product.mpr ⟨mem_pairWords.mpr ⟨x, rfl⟩, mem_pairWords.mpr ⟨evol x m, ?_⟩⟩
    funext i
    simp [split, pairWord, Rule30ZeroBoundaryBarriers.evol_restart]
  simpa [Finset.card_image_of_injective _ inject] using Finset.card_le_card maps

/-- Spatial translation preserves the set of pair words, including the letters themselves. -/
theorem pairWords_translate (a b : ℤ) (n : ℕ) : pairWords a n = pairWords b n := by
  have sub (i j : ℤ) : pairWords i n ⊆ pairWords j n := by
    intro w hw
    obtain ⟨x, rfl⟩ := mem_pairWords.mp hw
    let y := fun p : ℤ => x (p + (i - j))
    have eqn : ∀ t k, evol y t k = evol x t (k + (i - j)) :=
      fun t k => (Rule30ZeroBoundaryBarriers.evol_shift_all (x := y) (x' := x)
        (d := i - j) (fun _ => rfl) t k).symm
    refine mem_pairWords.mpr ⟨y, ?_⟩
    funext k
    simp only [pairWord, eqn, show j + (i - j) = i by omega, show j + 1 + (i - j) = i + 1 by omega]
  exact Finset.Subset.antisymm (sub a b) (sub b a)

/-- The full topological entropy is exactly the exponential growth rate of a single
adjacent pair, with both the alphabet and its physical language fixed. -/
theorem entropy_eq_pair_growth (a : ℤ) :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ =
      ExpGrowth.expGrowthSup fun n => ((pairWords a n).card : ENNReal) := by
  classical
  apply le_antisymm
  · -- One representative of each sufficiently long pair word covers a spatial window.
    refine iSup₂_le fun U hU => ?_
    obtain ⟨N, hN⟩ := exists_windowRel_subset hU
    refine (coverEntropyEntourage_antitone _ _ hN).trans ?_
    refine ExpGrowth.expGrowthSup_le_of_eventually_le
      (b := ((pairWords a (2 * N + 1)).card : ENNReal)) (by simp) (Eventually.of_forall fun n => ?_)
    have h := ENat.toENNReal_le.2 (coverMincard_le_card_pairWords N n)
    calc _ ≤ ((pairWords N (n + 2 * N + 1)).card : ENNReal) := by simpa using h
         _ = ((pairWords a (n + (2 * N + 1))).card : ENNReal) := by rw [pairWords_translate (↑N) a, Nat.add_assoc]
         _ ≤ (pairWords a n).card * (pairWords a (2 * N + 1)).card := by exact_mod_cast card_pairWords_add_le a n (2 * N + 1)
         _ = _ := mul_comm _ _
  · -- Conversely, a dynamical cover on the observed pair must realize every pair word.
    let coord (i : ℤ) : SetRel (ℤ → Bool) (ℤ → Bool) := {p | p.1 i = p.2 i}
    have coord_mem (i : ℤ) : coord i ∈ 𝓤 (ℤ → Bool) :=
      (Pi.uniformContinuous_proj (fun _ : ℤ => Bool) i)
        (UniformSpace.uniformSpace_eq_bot.mp rfl : SetRel.id ∈ 𝓤 Bool)
    let V := coord a ∩ coord (a + 1)
    have hV : V ∈ 𝓤 (ℤ → Bool) := inter_mem (coord_mem _) (coord_mem _)
    refine le_trans ?_ (coverEntropyEntourage_le_coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ hV)
    refine ExpGrowth.expGrowthSup_monotone fun n => ?_
    have bound (s : Finset (ℤ → Bool)) (hs : IsDynCoverOf (fun x : ℤ → Bool => evol x 1) Set.univ V n s) :
        (pairWords a n).card ≤ s.card := by
      have sub : pairWords a n ⊆ s.image (pairWord a n) := by
        intro w hw
        obtain ⟨x, rfl⟩ := mem_pairWords.mp hw
        obtain ⟨y, hy, hxy⟩ := hs (x := x) (Set.mem_univ _)
        refine Finset.mem_image.mpr ⟨y, hy, ?_⟩
        funext k
        simp only [dynEntourage, Set.mem_iInter, Set.mem_preimage, Prod.map_iterate,
          Prod.map_apply, V, coord, Set.mem_inter_iff, Set.mem_ofPred_eq, iterate_evol_one] at hxy
        have eqs := hxy k k.isLt
        exact Prod.ext eqs.1.symm eqs.2.symm
      exact (Finset.card_le_card sub).trans Finset.card_image_le
    have hm : ((pairWords a n).card : ℕ∞) ≤ coverMincard (fun x : ℤ → Bool => evol x 1) Set.univ V n :=
      le_iInf₂ fun s hs => by exact_mod_cast bound s hs
    simpa using ENat.toENNReal_le.2 hm

/-- An exponential bound on the pair words at any one spatial origin bounds the entropy. -/
theorem entropy_of_growth (a : ℤ) (C r : ENNReal) (hc : C ≠ ⊤)
    (bound : ∀ n, ((pairWords a n).card : ENNReal) ≤ C * r ^ n) :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤ ENNReal.log r := by
  rw [entropy_eq_pair_growth a]
  exact (ExpGrowth.expGrowthSup_le_of_eventually_le hc (Eventually.of_forall bound)).trans_eq
    ExpGrowth.expGrowthSup_pow

/-- Any certified upper bound r^k on a positive block length bounds topological entropy by log r. -/
theorem entropy_of_block (a : ℤ) {k : ℕ} (hk : 0 < k) (r : ENNReal) (hr : 1 ≤ r)
    (blocks : ((pairWords a k).card : ENNReal) ≤ r ^ k) :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤ ENNReal.log r := by
  have bound (n : ℕ) : ((pairWords a n).card : ENNReal) ≤ 4 ^ k * r ^ n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases small : n < k
      · have base : (pairWords a n).card ≤ 4 ^ n := by
          simpa [Fintype.card_fun, Fintype.card_prod] using Finset.card_le_univ (pairWords a n)
        calc ((pairWords a n).card : ENNReal) ≤ 4 ^ n := by exact_mod_cast base
             _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
             _ ≤ 4 ^ k * r ^ n := le_mul_of_one_le_right' (one_le_pow₀ hr)
      · obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt small)
        have hb' : b < n := by omega
        calc ((pairWords a n).card : ENNReal) ≤ (pairWords a k).card * (pairWords a b).card := by
               rw [hb]; exact_mod_cast card_pairWords_add_le a k b
             _ ≤ r ^ k * (4 ^ k * r ^ b) := mul_le_mul' blocks (ih b hb')
             _ = 4 ^ k * r ^ n := by rw [hb, pow_add]; ring
  exact entropy_of_growth a _ _ (ENNReal.pow_ne_top (by norm_num)) bound

/-- The physical word count at a single positive length and a single origin gives an upper rate. -/
theorem entropy_le_block_root (a : ℤ) (k : ℕ) (hk : 0 < k) :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤
      ENNReal.log (((pairWords a k).card : ENNReal) ^ (1 / (k : ℝ))) := by
  have pos : 0 < (pairWords a k).card := Finset.card_pos.mpr
    ⟨pairWord a k (fun _ => false), mem_pairWords.mpr ⟨_, rfl⟩⟩
  have one : 1 ≤ ((pairWords a k).card : ENNReal) := by exact_mod_cast pos
  apply entropy_of_block a hk _ (ENNReal.one_le_rpow one (by positivity))
  rw [← ENNReal.rpow_mul_natCast]
  simp [Nat.ne_of_gt hk]

/-! ## Weighted covers of the pair language -/

/-- The observed values at two adjacent sites, ordered from west to east. -/
abbrev Letter := Bool × Bool

/-- The four pair letters in transition-table order. -/
def alphabet : List Letter := [(false, false), (false, true), (true, false), (true, true)]

/-- Append the read letter at the latest time. The recursion reads backwards. -/
def addLetter {n : ℕ} (l : Letter) (w : Fin n → Letter) : Fin (n + 1) → Letter := Fin.lastCases l w

/-- A reverse table. At each time the state accepts certain current rows. The initial
state accepts all terminal rows. A single transition must lift the actual physical
predecessor at the letter formed by columns a and a+1. A blank table entry is none. -/
structure ReverseCover (σ : Type) where
  start : σ
  step : σ → Letter → Option σ
  accepts : σ → ℤ → (ℤ → Bool) → Prop
  terminal : ∀ a x, accepts start a x
  lift : ∀ s a x, accepts s a (evol x 1) →
    ∃ q, step s (x a, x (a + 1)) = some q ∧ accepts q a x

namespace ReverseCover

variable {σ : Type} (M : ReverseCover σ)

/-- Append a letter to each path from its destination, if the transition exists. -/
def extensions {n : ℕ} (s : σ) (l : Letter) (old : σ → List (Fin n → Letter)) :=
  (M.step s l).elim [] (fun q => (old q).map (addLetter l))

/-- Accepted words of length n, in physical time order. -/
def paths : (n : ℕ) → σ → List (Fin n → Letter)
  | 0, _ => [Fin.elim0]
  | n + 1, s => alphabet.flatMap fun l => M.extensions s l (paths n)

/-- Each accepted terminal row supplies a reverse path for its physical history. -/
theorem physical_mem (a : ℤ) (x : ℤ → Bool) (n : ℕ) (s : σ)
    (hs : M.accepts s a (evol x n)) : pairWord a n x ∈ M.paths n s := by
  induction n generalizing s with
  | zero => simp only [paths, List.mem_singleton]; funext i; exact Fin.elim0 i
  | succ n ih =>
    let l : Letter := (evol x n a, evol x n (a + 1))
    have restart : evol (evol x n) 1 = evol x (n + 1) := by
      funext p; rw [Rule30ZeroBoundaryBarriers.evol_restart]
    obtain ⟨q, hq, accept⟩ := M.lift s a (evol x n) (restart ▸ hs)
    have snoc : addLetter l (pairWord a n x) = pairWord a (n + 1) x := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [addLetter, pairWord, l]
    refine List.mem_flatMap.mpr ⟨l, ?_, ?_⟩
    · rcases l with ⟨b, g⟩; cases b <;> cases g <;> decide
    · have table : M.step s l = some q := hq
      simpa [extensions, table] using (List.mem_map.mpr ⟨pairWord a n x, ih q accept, snoc⟩ :
        pairWord a (n + 1) x ∈ (M.paths n q).map (addLetter l))

/-- Weight of the destination, counting a missing transition as zero. -/
def cost (w : σ → ℕ) (s : σ) (l : Letter) : ℕ := (M.step s l).elim 0 w

/-- Each state supplies its positive integer weight and an integer bound on the
sum of its four outgoing weights. Several different letters can have the same destination. -/
structure Weights (p q : ℕ) where
  weight : σ → ℕ
  positive : ∀ s, 0 < weight s
  row : ∀ s, q * ((alphabet.map fun l => M.cost weight s l).sum) ≤ p * weight s

variable {p q : ℕ}

/-- The weight of a state bounds the number of length-n paths from it. -/
theorem path_bound (W : M.Weights p q) (hq : 0 < q) (n : ℕ) (s : σ) :
    ((M.paths n s).length : ℝ) ≤ (W.weight s : ℝ) * ((p : ℝ) / q) ^ n := by
  induction n generalizing s with
  | zero =>
    simp only [paths, List.length_singleton, Nat.cast_one, pow_zero, mul_one]
    exact_mod_cast W.positive s
  | succ n ih =>
    have le (l : Letter) : ((M.extensions s l (M.paths n)).length : ℝ) ≤
        (M.cost W.weight s l : ℝ) * ((p : ℝ) / q) ^ n := by
      cases h : M.step s l with
      | none => simp [extensions, cost, h]
      | some t => simpa [extensions, cost, h] using ih t
    let c := M.cost W.weight s
    have hn : q * (c (false, false) + c (false, true) + c (true, false) + c (true, true)) ≤ p * W.weight s := by
      simpa [alphabet, c, Nat.add_assoc] using W.row s
    have hreal : (q : ℝ) * ((c (false, false) : ℝ) + c (false, true) + c (true, false) + c (true, true))
        ≤ p * W.weight s := by exact_mod_cast hn
    have cert : ((c (false, false) : ℝ) + c (false, true) + c (true, false) + c (true, true)) ≤
        ((p : ℝ) / q) * W.weight s := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hq)]
      simpa [mul_comm] using hreal
    have parts := add_le_add (add_le_add (add_le_add (le (false, false)) (le (false, true)))
      (le (true, false))) (le (true, true))
    simp only [paths, alphabet, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, Nat.cast_add]
    simp only [c] at cert
    calc _ ≤ (((M.cost W.weight s (false, false) : ℝ) + M.cost W.weight s (false, true)+
                  M.cost W.weight s (true, false) + M.cost W.weight s (true, true)) * ((p : ℝ) / q) ^ n) := by
              rw [add_mul, add_mul, add_mul]; simpa only [add_assoc] using parts
         _ ≤ (((p : ℝ) / q) * W.weight s) * ((p : ℝ) / q) ^ n :=
              mul_le_mul_of_nonneg_right cert (by positivity)
         _ = _ := by rw [pow_succ]; ring

/-- An exact integer row certificate bounds the entire physical language at every time. -/
theorem pair_count (W : M.Weights p q) (hq : 0 < q) (a : ℤ) (n : ℕ) :
    ((pairWords a n).card : ℝ) ≤ (W.weight M.start : ℝ) * ((p : ℝ) / q) ^ n := by
  classical
  have incl : pairWords a n ⊆ (M.paths n M.start).toFinset := by
    intro w hw; obtain ⟨x, rfl⟩ := mem_pairWords.mp hw
    exact List.mem_toFinset.mpr (M.physical_mem a x _ _ (M.terminal _ _))
  have hn := (Finset.card_le_card incl).trans (List.toFinset_card_le _)
  exact (Nat.cast_le.mpr hn).trans (M.path_bound W hq _ _)

/-- A sound reverse table and its positive integer weights bound full topological entropy. -/
theorem entropy_le (W : M.Weights p q) (hq : 0 < q) :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤ ENNReal.log (ENNReal.ofReal ((p : ℝ) / q)) := by
  apply entropy_of_growth 0 (W.weight M.start) _ (by simp)
  intro n
  have h := ENNReal.ofReal_le_ofReal (M.pair_count W hq 0 n)
  simpa [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ W.weight M.start),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (p : ℝ) / q)] using h

end ReverseCover

/-! ## Certificates on a finite eastern strip -/

/-- A nonempty physical window east of a. Its low-indexed site is a+1. -/
def eastWindow (k : ℕ) (a : ℤ) (x : ℤ → Bool) : Fin (k + 1) → Bool :=
  fun i => x (a + i.val + 1)

/-- One physical tick of a k+1-site strip, for specified left and right exterior cells. -/
def stripStep {k : ℕ} (b e : Bool) (u : Fin (k + 1) → Bool) : Fin (k + 1) → Bool :=
  fun i => xor (if h : 0 < i.val then u ⟨i.val - 1, by omega⟩ else b)
    (u i || (if h : i.val + 1 < k + 1 then u ⟨i.val + 1, h⟩ else e))

theorem physical_strip_step (k : ℕ) (a : ℤ) (x : ℤ → Bool) :
    stripStep (x a) (x (a + k + 2)) (eastWindow k a x) = eastWindow k a (evol x 1) := by
  funext i
  have hi := i.isLt
  have left : (if h : 0 < i.val then x (a + (↑(i.val - 1) : ℤ) + 1) else x a) =
      x (a + i.val + 1 - 1) := by
    split
    · rename_i h
      rw [Int.natCast_sub (by omega : 1 ≤ i.val)]; congr 1; omega
    · congr 1; omega
  have right : (if h : i.val + 1 < k + 1 then x (a + (↑(i.val + 1) : ℤ) + 1) else x (a + k + 2)) =
      x (a + i.val + 1 + 1) := by
    split <;> congr 1 <;> omega
  simp only [stripStep, eastWindow, evol, Rule30Jen.rule]
  simpa only [stripStep, eastWindow, evol, Rule30Jen.rule, Fin.val_mk] using
    congrArg₂ (fun l r => xor l (x (a + i.val + 1) || r)) left right

/-- A strip certificate only needs finite tests of the Rule 30 truth table. -/
structure StripTable (k : ℕ) (σ : Type) where
  start : σ
  step : σ → Letter → Option σ
  accepts : σ → (Fin (k + 1) → Bool) → Bool
  terminal : ∀ u, accepts start u = true
  lift : ∀ s b e u, accepts s (stripStep b e u) = true →
    (step s (b, u 0)).elim false (fun t => accepts t u) = true

/-- A local strip certificate lifts actual predecessors on the entire lattice. -/
def StripTable.cover {k : ℕ} {σ : Type} (D : StripTable k σ) : ReverseCover σ where
  start := D.start
  step := D.step
  accepts s a x := D.accepts s (eastWindow k a x) = true
  terminal a x := D.terminal _
  lift s a x hs := by
    have h := D.lift s (x a) (x (a + k + 2)) (eastWindow k a x) (physical_strip_step k a x ▸ hs)
    simp only [eastWindow, Fin.val_zero, Nat.cast_zero, add_zero] at h
    cases he : D.step s (x a, x (a + 1)) with
    | none => simp [he] at h
    | some t => exact ⟨t, rfl, by simpa [he, eastWindow] using h⟩

/-- Encode a strip with its site nearest the observed wall as bit zero. -/
private def stripCode : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, u => (u 0).toNat + 2 * stripCode (fun i : Fin n => u i.succ)

/-- Enumerate the two possible heads before recursively testing all smaller words. -/
private def allBits : {n : ℕ} → ((Fin n → Bool) → Bool) → Bool
  | 0, P => P Fin.elim0
  | k + 1, P => allBits (n := k) (fun u => P (Fin.cons false u)) &&
              allBits (n := k) (fun u => P (Fin.cons true u))

private theorem allBits_sound {n : ℕ} (P : (Fin n → Bool) → Bool) (h : allBits P = true) :
    ∀ u, P u = true := by
  induction n with
  | zero =>
    intro u
    have e : u = Fin.elim0 := by funext i; exact Fin.elim0 i
    simpa [e, allBits] using h
  | succ k ih =>
    have hp : allBits (fun v : Fin k → Bool => P (Fin.cons false v)) = true ∧
        allBits (fun v : Fin k → Bool => P (Fin.cons true v)) = true := by
      simpa [allBits] using h
    intro u
    have eta : Fin.cons (u 0) (fun i => u i.succ) = u := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [← eta]
    cases ht : u 0 with
    | false => exact ih _ hp.1 _
    | true => exact ih _ hp.2 _

/-! ## A five-site certificate -/

namespace FiveSite

/- Each row stores a five-site mask, a positive integer weight and four destination indices
in the order 00, 01, 10, 11. Bit i of the mask accepts the strip with code i.
A destination equal to the number of rows means the transition is absent. -/
private def rows : Array (ℕ × ℕ × (ℕ × ℕ × ℕ × ℕ)) := #[
  (4294967295, 2859464, 1, 2, 1, 2),
  (1431655765, 1679211, 3, 140, 4, 2),
  (2863311530, 1679211, 4, 2, 3, 140),
  (286331153, 1013305, 5, 140, 140, 6),
  (1145324612, 1250506, 7, 140, 4, 8),
  (16843009, 797489, 9, 140, 140, 10),
  (2829625512, 1581547, 4, 11, 12, 140),
  (269488144, 886815, 13, 140, 140, 14),
  (33686018, 797489, 140, 10, 9, 140),
  (65537, 671908, 15, 140, 140, 16),
  (2290124928, 1199416, 17, 18, 7, 140),
  (573186602, 1459735, 19, 20, 5, 140),
  (286265616, 1002691, 21, 140, 140, 22),
  (16777472, 739403, 23, 140, 140, 24),
  (539500584, 1341862, 19, 25, 13, 140),
  (1, 608459, 15, 140, 140, 26),
  (2155905024, 967905, 27, 28, 29, 140),
  (67372100, 1130521, 30, 140, 31, 32),
  (33686016, 797489, 140, 33, 9, 140),
  (1077952512, 967905, 29, 140, 27, 28),
  (2829625514, 1661531, 4, 34, 35, 140),
  (16843008, 797489, 9, 140, 140, 33),
  (673720488, 1556513, 31, 36, 37, 140),
  (65536, 660389, 15, 140, 140, 38),
  (134219904, 1074524, 39, 40, 30, 140),
  (539500586, 1442055, 19, 41, 42, 140),
  (2147516416, 818995, 43, 28, 44, 140),
  (262148, 671908, 140, 140, 19, 45),
  (33554944, 739403, 140, 24, 23, 140),
  (1052688, 859780, 13, 140, 140, 46),
  (268439552, 730630, 13, 140, 140, 47),
  (1145062468, 1250506, 7, 140, 48, 8),
  (131074, 671908, 140, 16, 15, 140),
  (142641280, 1199416, 39, 18, 7, 140),
  (2720703018, 1637549, 49, 50, 51, 140),
  (286265617, 1013305, 5, 140, 140, 52),
  (539631658, 1456103, 19, 53, 42, 140),
  (285217024, 947412, 21, 140, 140, 54),
  (8421376, 940870, 55, 28, 29, 140),
  (67109956, 1130521, 30, 140, 56, 32),
  (131072, 660389, 140, 38, 15, 140),
  (2687017002, 1619869, 49, 57, 58, 140),
  (16777473, 797489, 9, 140, 140, 59),
  (262144, 660389, 140, 140, 60, 45),
  (16, 521904, 140, 140, 140, 61),
  (2, 608459, 140, 26, 15, 140),
  (538976296, 1278413, 62, 25, 13, 140),
  (524320, 975393, 60, 63, 140, 140),
  (1141130308, 1250506, 64, 140, 4, 8),
  (1078214656, 1218929, 29, 140, 65, 66),
  (2863180458, 1679211, 4, 67, 3, 140),
  (16843025, 946957, 9, 140, 140, 68),
  (2821236904, 1581547, 4, 11, 69, 140),
  (2695405610, 1652992, 70, 57, 71, 140),
  (134744224, 1426540, 72, 73, 30, 140),
  (4, 608459, 140, 140, 62, 45),
  (1140868164, 1250506, 64, 140, 48, 8),
  (2720571946, 1637549, 49, 74, 51, 140),
  (16777489, 946957, 9, 140, 140, 75),
  (2281736320, 1199416, 17, 18, 64, 140),
  (4210688, 940870, 29, 140, 55, 28),
  (536879112, 1224933, 62, 76, 13, 140),
  (1073758208, 818995, 44, 140, 43, 28),
  (536879114, 1348579, 62, 77, 42, 140),
  (268439568, 886815, 13, 140, 140, 78),
  (4472836, 1203413, 29, 140, 79, 66),
  (33554946, 797489, 140, 59, 9, 140),
  (2854922922, 1679211, 4, 2, 80, 140),
  (2827004040, 1551105, 48, 81, 12, 140),
  (285217040, 1002691, 21, 140, 140, 82),
  (1078214660, 1230448, 29, 140, 70, 66),
  (17830161, 1013305, 5, 140, 140, 83),
  (71320644, 1250506, 7, 140, 56, 8),
  (537010186, 1367534, 62, 84, 42, 140),
  (2854791850, 1679211, 4, 67, 80, 140),
  (2818615432, 1551105, 48, 81, 69, 140),
  (524322, 1316435, 60, 85, 15, 140),
  (2148040738, 1549311, 86, 87, 88, 140),
  (537403432, 1341862, 19, 89, 13, 140),
  (1077952516, 1166999, 29, 140, 90, 66),
  (285282577, 1013305, 5, 140, 140, 91),
  (34210338, 1388185, 60, 92, 9, 140),
  (671623336, 1556513, 31, 93, 37, 140),
  (2820712616, 1581547, 48, 11, 69, 140),
  (2156429346, 1593953, 65, 87, 94, 140),
  (2684395530, 1540907, 95, 96, 58, 140),
  (4472832, 1191894, 29, 140, 97, 66),
  (2717950474, 1573308, 95, 98, 51, 140),
  (17, 872537, 15, 140, 140, 99),
  (537403434, 1442055, 19, 100, 42, 140),
  (1074020356, 1081538, 44, 140, 49, 66),
  (2827528360, 1581547, 4, 101, 12, 140),
  (2827004042, 1646018, 48, 102, 35, 140),
  (537534506, 1456103, 19, 103, 42, 140),
  (1052689, 965920, 42, 140, 140, 104),
  (1074020352, 1070019, 44, 140, 86, 66),
  (2181595682, 1601115, 86, 105, 106, 140),
  (4210692, 1139964, 29, 140, 107, 66),
  (2315815586, 1677334, 108, 109, 110, 140),
  (2684395528, 1439727, 95, 111, 112, 140),
  (2684919850, 1619869, 49, 113, 58, 140),
  (571089450, 1459735, 19, 114, 5, 140),
  (2181726754, 1601115, 86, 115, 106, 140),
  (2693308458, 1652992, 70, 113, 71, 140),
  (2686492712, 1470169, 95, 116, 112, 140),
  (2852170378, 1678419, 48, 117, 80, 140),
  (65553, 889255, 15, 140, 140, 118),
  (1073758212, 1018089, 44, 140, 95, 66),
  (71582788, 1250506, 7, 140, 31, 8),
  (2852301450, 1678419, 48, 119, 80, 140),
  (268505105, 1009673, 42, 140, 140, 120),
  (34079266, 1388185, 60, 121, 9, 140),
  (16777488, 921622, 23, 140, 140, 122),
  (2718474794, 1637549, 49, 123, 51, 140),
  (2827528362, 1661531, 4, 124, 35, 140),
  (2860558986, 1678419, 48, 117, 3, 140),
  (573055530, 1459735, 19, 125, 5, 140),
  (2315946658, 1677334, 108, 126, 110, 140),
  (2692784136, 1479117, 90, 111, 127, 140),
  (2324335266, 1677334, 108, 126, 128, 140),
  (2693308456, 1573008, 70, 129, 127, 140),
  (2818615434, 1646018, 48, 102, 130, 140),
  (671099016, 1503033, 56, 131, 37, 140),
  (2852694698, 1679211, 4, 132, 80, 140),
  (2718605866, 1637549, 49, 133, 51, 140),
  (2821236906, 1661531, 4, 34, 130, 140),
  (2860690058, 1678419, 48, 119, 3, 140),
  (17830160, 1002691, 21, 140, 140, 134),
  (269553681, 1009673, 42, 140, 140, 135),
  (570958378, 1459735, 19, 136, 5, 140),
  (285217041, 1013305, 5, 140, 140, 137),
  (655394, 1330483, 60, 138, 15, 140),
  (2852825770, 1679211, 4, 139, 80, 140),
  (2861083306, 1679211, 4, 132, 3, 140),
  (673196200, 1556513, 56, 36, 37, 140),
  (2695405608, 1573008, 70, 116, 127, 140),
  (2819139754, 1661531, 4, 124, 130, 140),
  (2819139752, 1581547, 4, 101, 69, 140),
  (2692784138, 1574030, 90, 96, 71, 140),
  (2861214378, 1679211, 4, 139, 3, 140)
]
private abbrev S := Fin 140
private def row (s : S) := rows[s.val]!
private def wt (s : S) := (row s).2.1
private def accept (s : S) (u : Fin 5 → Bool) := (row s).1.testBit (stripCode u)
private def next (s : S) (l : Letter) : Option S := Id.run do
  let t := (row s).2.2
  let dest := match l with
    | (false, false) => t.1 | (false, true) => t.2.1
    | (true, false) => t.2.2.1 | (true, true) => t.2.2.2
  if h : dest < 140 then return some ⟨dest, h⟩ else return none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem local_check : ∀ (s : S) (b e : Bool), allBits (fun u : Fin 5 → Bool =>
    !accept s (stripStep b e u) || (next s (b, u 0)).elim false (fun t => accept t u)) = true := by
  decide +kernel

private def table : StripTable 4 S where
  start := 0
  step := next
  accepts := accept
  terminal := allBits_sound _ (by decide +kernel)
  lift s b e u h := by
    have v := allBits_sound _ (local_check s b e) u
    simpa [h] using v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def weights : table.cover.Weights 1679211 714866 where
  weight := wt
  positive := by decide +kernel
  row := by decide +kernel

/-- The five-site table bounds the entropy by log(1679211/714866). -/
theorem entropy_width_5 :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤ ENNReal.log (ENNReal.ofReal (1679211 / 714866)) :=
  table.cover.entropy_le weights (by decide)

/-- A simpler rational upper bound, with strict inequality. -/
theorem entropy_lt_log_forty_seven_twentieths :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ <
      ENNReal.log (ENNReal.ofReal (47 / 20)) := by
  apply entropy_width_5.trans_lt
  apply ENNReal.log_strictMono
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

end FiveSite

end Rule30Equivalents.PairTraceEntropy
