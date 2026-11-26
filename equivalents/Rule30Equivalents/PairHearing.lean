module

public import Rule30Equivalents.PairTraceEntropy
public import Ruliology.CellularAutomata.Rule30HorizontalDiversity

/-!
# What a wall hears

Fix the readings of column 0 (the wall) and count the words read by the OR of columns 0 and 1. The column to the west is the
wall a tick later plus that reading, so a pair word of columns -1 and 0 is a wall word with an OR word. The topological entropy
is therefore the growth rate of the OR words summed over all walls, `log 2` plus the growth of their mean
(`entropy_eq_mask_growth`). A bound on the OR words beside every wall, uniform in the wall, bounds the entropy
(`entropy_le_of_mask`). The core bounds of `Rule30MaskedForkRate`, `Rule30HorizontalDiversity` and Quint's six-cell strip are of
this kind; the four- and five-cell certificates give `log (5/2)` and `log (39/16)` (`entropy_galindo_four`, `entropy_galindo`).

Contributed by Gareth Herbert with Claude (Anthropic) and GPT (OpenAI).
-/

@[expose] public section

open Filter Topology Dynamics Uniformity Ruliology.CellularAutomata Rule30Realization
open Rule30Equivalents.Mixing Rule30Equivalents.PairTraceEntropy

namespace Rule30Equivalents.PairHearing

local notation "segment" => Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity.segment

/-- The OR readings beside column 0, as a list. -/
abbrev orWord (x : ℤ → Bool) (n : ℕ) : List Bool := segment (fun k => evol x k 0 || evol x k 1) 0 n

theorem segment_eq_ofFn (f : ℕ → Bool) (t n : ℕ) :
    segment f t n = List.ofFn (fun i : Fin n => f (t + i)) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity.segment, ih, List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 2
    funext i
    congr 1
    omega

/-- The readings of column 0 at the times `0, …, n`. -/
def wall (x : ℤ → Bool) (n : ℕ) : Fin (n + 1) → Bool := fun s => evol x s 0

/-- Its first `n` letters as a list. -/
def front {n : ℕ} (c : Fin (n + 1) → Bool) : List Bool := List.ofFn (fun i : Fin n => c i.castSucc)

theorem front_length {n : ℕ} (c : Fin (n + 1) → Bool) : (front c).length = n := by simp [front]

theorem front_wall (x : ℤ → Bool) (n : ℕ) : front (wall x n) = segment (fun k => evol x k 0) 0 n := by
  rw [segment_eq_ofFn]; simp [front, wall]

/-- The column to the west of the wall is the wall a tick later, plus the OR reading. -/
theorem west (x : ℤ → Bool) (t : ℕ) :
    evol x t (-1) = xor (evol x (t + 1) 0) (evol x t 0 || evol x t 1) := by
  have h := Rule30ZeroBoundaryBarriers.evol_succ x t 0
  simp only [Rule30Jen.rule, zero_sub, zero_add] at h
  rw [h]
  cases evol x t (-1) <;> cases evol x t 0 <;> cases evol x t 1 <;> rfl

theorem pairWord_eq {x y : ℤ → Bool} {n : ℕ} (hc : wall x n = wall y n) (ho : orWord x n = orWord y n) :
    pairWord (-1) n x = pairWord (-1) n y := by
  have hor (i : Fin n) : (evol x i 0 || evol x i 1) = (evol y i 0 || evol y i 1) := by
    simp only [orWord, segment_eq_ofFn, Nat.zero_add] at ho
    exact congrFun (List.ofFn_injective ho) i
  funext s
  have h0 : evol x s 0 = evol y s 0 := congrFun hc s.castSucc
  have h1 : evol x (s + 1) 0 = evol y (s + 1) 0 := congrFun hc s.succ
  refine Prod.ext ?_ ?_
  · show evol x s (-1) = evol y s (-1)
    rw [west, west, h1, hor s]
  · show evol x s (-1 + 1) = evol y s (-1 + 1)
    simpa using h0

/-- `K p^n / q^n` candidates for the OR word beside every wall word of length `n`, for every row. -/
def MaskBound (K p q : ℕ) : Prop := ∀ c : List Bool, ∃ L : List (List Bool),
  L.length * q ^ c.length ≤ K * p ^ c.length ∧
  ∀ (x : ℤ → Bool) (t : ℕ), segment (fun k => evol x k 0) t c.length = c →
    segment (fun k => evol x k 0 || evol x k 1) t c.length ∈ L

theorem card_pairWords_le_of_mask {K p q : ℕ} (hb : MaskBound K p q) (n : ℕ) :
    (pairWords (-1) n).card * q ^ n ≤ 2 ^ (n + 1) * (K * p ^ n) := by
  classical
  choose L hlen hmem using hb
  let S : Finset (Σ _ : Fin (n + 1) → Bool, List Bool) := Finset.univ.sigma fun c => (L (front c)).toFinset
  have hex : ∀ w ∈ pairWords (-1) n, ∃ x, pairWord (-1) n x = w := fun w hw => mem_pairWords.mp hw
  choose! row hrow using hex
  have hcard : (pairWords (-1) n).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun w => ⟨wall (row w) n, orWord (row w) n⟩) ?_ ?_
    · intro w hw
      simp only [S, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ, true_and, Finset.mem_coe, List.mem_toFinset]
      have h := hmem (front (wall (row w) n)) (row w) 0 (by rw [front_length, front_wall])
      rwa [front_length] at h
    · intro u hu v hv h
      simp only [Sigma.mk.injEq, heq_eq_eq] at h
      rw [← hrow u hu, ← hrow v hv]
      exact pairWord_eq h.1 h.2
  calc (pairWords (-1) n).card * q ^ n ≤ S.card * q ^ n := Nat.mul_le_mul_right _ hcard
    _ = ∑ c : Fin (n + 1) → Bool, (L (front c)).toFinset.card * q ^ n := by
        rw [Finset.card_sigma, Finset.sum_mul]
    _ ≤ ∑ _c : Fin (n + 1) → Bool, K * p ^ n := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h := hlen (front c)
        rw [front_length] at h
        exact (Nat.mul_le_mul_right _ (List.toFinset_card_le _)).trans h
    _ = 2 ^ (n + 1) * (K * p ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, smul_eq_mul]

/-- **A uniform bound on what any wall hears bounds the topological entropy.** -/
theorem entropy_le_of_mask {K p q : ℕ} (hq : 0 < q) (hb : MaskBound K p q) :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤
      ENNReal.log (ENNReal.ofReal (2 * ((p : ℝ) / q))) := by
  apply entropy_of_growth (-1) ((2 * K : ℕ) : ENNReal) _ (ENNReal.natCast_ne_top _)
  intro n
  have hn := card_pairWords_le_of_mask hb n
  have hqr : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hr : ((pairWords (-1) n).card : ℝ) ≤ (2 * K : ℕ) * (2 * ((p : ℝ) / q)) ^ n := by
    have h : ((pairWords (-1) n).card : ℝ) * (q : ℝ) ^ n ≤ 2 ^ (n + 1) * (K * (p : ℝ) ^ n) := by exact_mod_cast hn
    calc ((pairWords (-1) n).card : ℝ) = ((pairWords (-1) n).card * (q : ℝ) ^ n) / (q : ℝ) ^ n := by field_simp
      _ ≤ (2 ^ (n + 1) * (K * (p : ℝ) ^ n)) / (q : ℝ) ^ n := by gcongr
      _ = _ := by push_cast; rw [mul_pow, div_pow, pow_succ]; field_simp
  have h := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)] at h
  simpa using h

/-- Galindo's five-cell bound (R30-20261125-70fb8c): entropy at most `log (39/16)`, 1.2854 bits. -/
theorem entropy_galindo : coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤
    ENNReal.log (ENNReal.ofReal (39 / 16)) := by
  have h := entropy_le_of_mask (K := 9) (p := 39) (q := 32) (by norm_num) Rule30HorizontalDiversity.five_cell_mask_bound
  convert h using 3
  norm_num

/-- The four-cell bound: `log (5/2)`, 1.3219 bits. -/
theorem entropy_galindo_four : coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤
    ENNReal.log (ENNReal.ofReal (5 / 2)) := by
  have h := entropy_le_of_mask (K := 6) (p := 5) (q := 4) (by norm_num) Rule30HorizontalDiversity.uniform_mask_bound
  convert h using 3
  norm_num

/-! ### The exact form: entropy is the growth of the OR words summed over all walls -/

open Classical in
/-- The words of wall readings and OR readings of length `n` that occur. -/
noncomputable def maskWords (n : ℕ) : Finset (Fin n → Bool × Bool) :=
  Finset.univ.filter fun w => ∃ x : ℤ → Bool, (fun s : Fin n => (evol x s 0, evol x s 0 || evol x s 1)) = w

theorem mem_maskWords {n : ℕ} {w : Fin n → Bool × Bool} :
    w ∈ maskWords n ↔ ∃ x : ℤ → Bool, (fun s : Fin n => (evol x s 0, evol x s 0 || evol x s 1)) = w := by
  simp [maskWords]

open Classical in
/-- The number of OR words beside the wall word `c`. -/
noncomputable def heard {n : ℕ} (c : Fin n → Bool) : ℕ := ((maskWords n).filter fun w => (fun s => (w s).1) = c).card

theorem card_maskWords_eq_sum (n : ℕ) : (maskWords n).card = ∑ c : Fin n → Bool, heard c := by
  classical
  let walls : (Fin n → Bool × Bool) → (Fin n → Bool) := fun w s => (w s).1
  have h := Finset.card_eq_sum_card_fiberwise (s := maskWords n) (t := (Finset.univ : Finset (Fin n → Bool)))
    (f := walls) (fun w _ => Finset.mem_coe.mpr (Finset.mem_univ (walls w)))
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold heard
  congr 1

theorem card_pairWords_le_mask (n : ℕ) : (pairWords (-1) n).card ≤ (maskWords n).card * 2 := by
  classical
  have hex : ∀ w ∈ pairWords (-1) n, ∃ x, pairWord (-1) n x = w := fun w hw => mem_pairWords.mp hw
  choose! row hrow using hex
  have h := Finset.card_le_card_of_injOn (s := pairWords (-1) n) (t := maskWords n ×ˢ (Finset.univ : Finset Bool))
    (fun w => ((fun s : Fin n => (evol (row w) s 0, evol (row w) s 0 || evol (row w) s 1)), evol (row w) n 0)) ?_ ?_
  · simpa [Finset.card_product] using h
  · intro w hw
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨mem_maskWords.mpr ⟨row w, rfl⟩, Finset.mem_univ _⟩)
  · intro u hu v hv h
    simp only [Prod.mk.injEq] at h
    have hz (s : Fin n) := Prod.mk.inj (congrFun h.1 s)
    have hnext (s : Fin n) : evol (row u) (s + 1) 0 = evol (row v) (s + 1) 0 := by
      by_cases hs : s.val + 1 < n
      · exact (hz ⟨s + 1, hs⟩).1
      · have e : s.val + 1 = n := by omega
        rw [e]; exact h.2
    rw [← hrow u hu, ← hrow v hv]
    funext s
    refine Prod.ext ?_ ?_
    · show evol (row u) s (-1) = evol (row v) s (-1)
      rw [west, west, hnext s, (hz s).2]
    · show evol (row u) s (-1 + 1) = evol (row v) s (-1 + 1)
      simpa using (hz s).1

theorem card_maskWords_le_pair (n : ℕ) : (maskWords n).card ≤ (pairWords (-1) (n + 1)).card := by
  classical
  let read (w : Fin (n + 1) → Bool × Bool) : Fin n → Bool × Bool := fun s =>
    ((w s.castSucc).2, xor (w s.castSucc).1 (w s.succ).2)
  have sub : maskWords n ⊆ (pairWords (-1) (n + 1)).image read := by
    intro w hw
    obtain ⟨x, rfl⟩ := mem_maskWords.mp hw
    refine Finset.mem_image.mpr ⟨pairWord (-1) (n + 1) x, mem_pairWords.mpr ⟨x, rfl⟩, ?_⟩
    funext s
    have hw := west x s
    refine Prod.ext ?_ ?_
    · show evol x s (-1 + 1) = evol x s 0
      simp
    · show xor (evol x s (-1)) (evol x (s + 1) (-1 + 1)) = (evol x s 0 || evol x s 1)
      rw [hw, show ((-1 : ℤ) + 1) = 0 by norm_num]
      cases evol x (s + 1) 0 <;> cases evol x s 0 <;> cases evol x s 1 <;> rfl
  exact (Finset.card_le_card sub).trans Finset.card_image_le

/-- **The topological entropy of rule 30 is the growth rate of the OR words, summed over all walls.** Since there are `2^n`
walls, it is `log 2` plus the growth rate of the mean number of OR words beside a wall. -/
theorem entropy_eq_mask_growth :
    coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ =
      ExpGrowth.expGrowthSup fun n => ((∑ c : Fin n → Bool, heard c : ℕ) : ENNReal) := by
  rw [entropy_eq_pair_growth (-1)]
  apply le_antisymm
  · refine ExpGrowth.expGrowthSup_le_of_eventually_le (b := 2) (by simp) (Eventually.of_forall fun n => ?_)
    have h := card_pairWords_le_mask n
    rw [card_maskWords_eq_sum] at h
    calc ((pairWords (-1) n).card : ENNReal) ≤ ((∑ c : Fin n → Bool, heard c) * 2 : ℕ) := by exact_mod_cast h
      _ = 2 * ((∑ c : Fin n → Bool, heard c : ℕ) : ENNReal) := by push_cast; ring
  · refine ExpGrowth.expGrowthSup_le_of_eventually_le (b := ((pairWords (-1) 1).card : ENNReal)) (by simp) (Eventually.of_forall fun n => ?_)
    have h := (card_maskWords_le_pair n).trans (card_pairWords_add_le (-1) n 1)
    rw [card_maskWords_eq_sum] at h
    calc ((∑ c : Fin n → Bool, heard c : ℕ) : ENNReal) ≤ ((pairWords (-1) n).card * (pairWords (-1) 1).card : ℕ) := by exact_mod_cast h
      _ = _ := by push_cast; ring

end Rule30Equivalents.PairHearing
