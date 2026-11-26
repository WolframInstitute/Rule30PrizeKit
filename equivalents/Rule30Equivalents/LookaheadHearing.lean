module

public import Rule30Equivalents.ExactHearingStrip
public import Rule30Equivalents.PairHearing

/-!
# Integer certificates for what a wall hears

A finite table of integer weights on sets of strips, knowing the next wall bits, bounds the OR words beside every wall, and so
both the full-map entropy and the single seed's horizontal words under an eventual centre period (`both_of_certificate`).
Conversely every rational rate strictly above the physical worst-wall rate has such a table, with width and look-ahead read off a
single block count (`strict_rate_has_certificate`, `physical_block_certificate`); a wall of period P needs P block tests
(`periodic_phase_bound`). At the limiting rate itself a constant need not exist: beside the all-white wall the count is n + 1.
The finite-memory hierarchy for joint spectral radii of nonnegative matrices is due to Gaubert and Stott (MTNS 2018).

Contributed by Gareth Herbert with Claude (Anthropic) and GPT (OpenAI).
-/

@[expose] public section

namespace Rule30Equivalents.LookaheadHearing
open Rule30Equivalents.ExactHearingStrip Rule30Equivalents.PairHearing
open Ruliology.CellularAutomata Rule30Realization
local notation "segment" => Rule30Certificates.HorizontalDiversity.segment

/-- Number of distinct OR words from a set of strips along the given wall. -/
noncomputable def count {d : ℕ} (S : Set (Strip d)) (c : ℕ → Bool) (t n : ℕ) :=
  (words S (segment c t n)).length

private theorem count_succ {d : ℕ} (S : Set (Strip d)) (c : ℕ → Bool) (t n : ℕ) :
    count S c t (n+1) =
    count (child S (c t) false) c (t+1) n + count (child S (c t) true) c (t+1) n := by
  simp [count,Rule30Certificates.HorizontalDiversity.segment,words]

private theorem count_le {d : ℕ} (S : Set (Strip d)) (c : ℕ → Bool) (t n : ℕ) :
    count S c t n ≤ 2^n := by
  classical
  induction n generalizing S t with
  | zero => by_cases h : S.Nonempty <;> simp [count,Rule30Certificates.HorizontalDiversity.segment,words,h]
  | succ n ih =>
    rw [count_succ,pow_succ]
    have h := Nat.add_le_add (ih (child S (c t) false) (t+1)) (ih (child S (c t) true) (t+1))
    omega

/-- Natural-number potential from continuation counts through length j. -/
noncomputable def weight {d : ℕ} (p q : ℕ) (S : Set (Strip d)) (c : ℕ → Bool) (t : ℕ) : ℕ → ℕ
  | 0 => count S c t 0
  | j+1 => p * weight p q S c t j + q^(j+1) * count S c t (j+1)

def ceiling (p q : ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 => p * ceiling p q j + q^(j+1) * 2^(j+1)

theorem weight_bounds {d : ℕ} (p q : ℕ) (hp : 0 < p) (S : Set (Strip d))
    (c : ℕ → Bool) (t j : ℕ) :
    count S c t 0 ≤ weight p q S c t j ∧ weight p q S c t j ≤ ceiling p q j := by
  induction j with
  | zero => exact ⟨le_rfl,by simpa [weight,ceiling] using count_le S c t 0⟩
  | succ j ih =>
    unfold weight ceiling
    exact ⟨by nlinarith [ih.1, Nat.zero_le (q^(j+1) * count S c t (j+1))],
      Nat.add_le_add (Nat.mul_le_mul_left _ ih.2) (Nat.mul_le_mul_left _ (count_le _ _ _ _))⟩

/-- All interior levels cancel. The block cap at length j+1 is the sole remaining test. -/
theorem balance {d : ℕ} (p q : ℕ) (S : Set (Strip d)) (c : ℕ → Bool) (t j : ℕ) :
    q * (weight p q (child S (c t) false) c (t+1) j +
         weight p q (child S (c t) true) c (t+1) j) + p^(j+1) * count S c t 0 =
    p * weight p q S c t j + q^(j+1) * count S c t (j+1) := by
  induction j with
  | zero => simp [weight,count_succ,Nat.add_comm]
  | succ j ih =>
    simp only [weight]
    rw [count_succ S c t (j+1)]
    linear_combination (norm := ring_nf) p * ih

private theorem segment_agree {c v : ℕ → Bool} (t u n : ℕ) (h : ∀ i < n, c (t+i) = v (u+i)) :
    segment c t n = segment v u n := by
  rw [segment_eq_ofFn,segment_eq_ofFn]
  congr 1
  funext i
  exact h i i.isLt

/-- Writing the potential as a function of a stream uses only j bits from time t. -/
theorem weight_agree {d : ℕ} (p q : ℕ) (S : Set (Strip d)) {c v : ℕ → Bool}
    (t u j : ℕ) (h : ∀ i < j, c (t+i) = v (u+i)) :
    weight p q S c t j = weight p q S v u j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [weight,ih (fun i hi => h i (by omega)),count,segment_agree t u (j+1) h]

/-- Finite physical premise, with duplicate candidates allowed. The whole infinite wall
is prescribed, but its continuation is freely chosen by the quantifier. -/
def BlockAt (c : ℕ → Bool) (k p q : ℕ) : Prop := ∃ L : List (List Bool),
  L.length * q^k ≤ p^k ∧ ∀ x : ℤ → Bool, (∀ t, evol x t 0 = c t) → actualMask x 0 k ∈ L

def PhysicalBlock (k p q : ℕ) : Prop := ∀ c : ℕ → Bool, BlockAt c k p q

private theorem shift_segment (c : ℕ → Bool) (t n : ℕ) :
    segment (fun i => c (t+i)) 0 n = segment c t n := by
  simp [segment_eq_ofFn]

private theorem block_strip_cap {d p q : ℕ} (S : Set (Strip d)) (c : ℕ → Bool) (t : ℕ)
    (hb : BlockAt (fun i => c (t+i)) (d+1) p q) :
    q^(d+1) * count S c t (d+1) ≤ p^(d+1) * count S c t 0 := by
  classical
  obtain ⟨L,hL,covers⟩ := hb
  let bs := segment c t (d+1)
  by_cases hs : S.Nonempty
  · have sub : words S bs ⊆ L := by
      intro os hm
      obtain ⟨s,_,hp⟩ := (mem_words _ _ _).1 hm
      have hu := (mem_words _ _ (Set.univ : Set (Strip d))).2 ⟨s,Set.mem_univ _,hp⟩
      rw [show bs = segment (fun i => c (t+i)) 0 (d+1) from (shift_segment _ _ _).symm] at hu
      obtain ⟨x,hc,hout⟩ := realize_word _ (le_refl (d+1)) hu
      exact hout ▸ covers x hc
    have h := (words_nodup bs S).length_le_of_subset sub
    have hz : count S c t 0 = 1 := by simp [count,words,Rule30Certificates.HorizontalDiversity.segment,hs]
    rw [hz,Nat.mul_one,Nat.mul_comm]
    exact (Nat.mul_le_mul_right _ h).trans hL
  · have no : words S bs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro os hm
      obtain ⟨s,hm,_⟩ := (mem_words _ _ _).1 hm
      exact hs ⟨s,hm⟩
    change q^(d+1) * (words S bs).length ≤ _
    simp [no]

/-- Every physical block cap produces a finite-width, finite-look-ahead, integer
one-step certificate. Both possible next wall bits are covered. -/
theorem physical_block_certificate {d p q : ℕ} (hb : PhysicalBlock (d+1) p q)
    (S : Set (Strip d)) (c : ℕ → Bool) (t : ℕ) :
    q * (weight p q (child S (c t) false) c (t+1) d +
         weight p q (child S (c t) true) c (t+1) d) ≤ p * weight p q S c t d := by
  have h := balance p q S c t d
  have hcap := block_strip_cap S c t (hb _)
  omega

/-- Soundness applies to any width, clock dependence and potential obeying the local test. -/
theorem count_of_certificate {d p q : ℕ} (V : Set (Strip d) → ℕ → ℕ) (c : ℕ → Bool)
    (base : ∀ S t, count S c t 0 ≤ V S t)
    (step : ∀ S t, q * (V (child S (c t) false) (t+1) + V (child S (c t) true) (t+1)) ≤ p * V S t)
    (S : Set (Strip d)) (t n : ℕ) : q^n * count S c t n ≤ p^n * V S t := by
  induction n generalizing S t with
  | zero => simpa using base S t
  | succ n ih =>
    rw [count_succ,pow_succ,pow_succ]
    have h := Nat.add_le_add (ih (child S (c t) false) (t+1)) (ih (child S (c t) true) (t+1))
    calc
      _ = q * (q^n * count (child S (c t) false) c (t+1) n + q^n * count (child S (c t) true) c (t+1) n) := by ring
      _ ≤ q * _ := Nat.mul_le_mul_left _ h
      _ = p^n * (q * (V (child S (c t) false) (t+1) + V (child S (c t) true) (t+1))) := by ring
      _ ≤ _ := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (p^n) (step S t)

/-- A wall with period P requires only P physical block tests. The bound covers
all starting phases and all durations, including durations shorter than P. -/
theorem periodic_phase_bound {d p q P : ℕ} (hp : 0 < p) (hP : 0 < P) (c : ℕ → Bool)
    (phase : ∀ t, c t = c (t % P))
    (hb : ∀ r < P, BlockAt (fun i => c (r+i)) (d+1) p q) :
    ∃ K, ∀ t n, q^n * count (Set.univ : Set (Strip d)) c t n ≤ p^n * K := by
  refine ⟨ceiling p q d,?_⟩
  intro t n
  have step (S : Set (Strip d)) (u : ℕ) := balance p q S c u d
  have cap (S : Set (Strip d)) (u : ℕ) :
      q^(d+1) * count S c u (d+1) ≤ p^(d+1) * count S c u 0 := by
    have eqc : (fun i => c (u+i)) = (fun i => c (u%P+i)) := by
      funext i
      rw [phase (u+i),phase (u%P+i)]
      simp [Nat.add_mod]
    exact block_strip_cap S c u (eqc ▸ hb (u%P) (Nat.mod_lt _ hP))
  have one (S : Set (Strip d)) (u : ℕ) :
      q * (weight p q (child S (c u) false) c (u+1) d +
           weight p q (child S (c u) true) c (u+1) d) ≤ p * weight p q S c u d := by
    have := step S u
    have := cap S u
    omega
  exact (count_of_certificate (fun S u => weight p q S c u d) c
    (fun S u => (weight_bounds p q hp S c u d).1) one Set.univ t n).trans
    (Nat.mul_le_mul_left _ (weight_bounds p q hp Set.univ c t d).2)

private theorem maskBound_of_counts {d K p q : ℕ}
    (counts : ∀ c n, q^n * count (Set.univ : Set (Strip d)) c 0 n ≤ p^n * K) :
    MaskBound K p q := by
  intro wall
  let c : ℕ → Bool := fun i => wall[i]?.getD false
  have hw : segment c 0 wall.length = wall := by
    rw [segment_eq_ofFn]
    simp [c]
  let S : Set (Strip d) := Set.univ
  refine ⟨words S wall, ?_, ?_⟩
  · simpa [S,count,hw,Nat.mul_comm] using counts c wall.length
  · intro x t he
    simpa only [S,actualWall,actualMask,he] using physical_mem d x t wall.length

theorem maskBound_of_physical_block {d p q : ℕ} (hp : 0 < p) (hb : PhysicalBlock (d+1) p q) :
    ∃ K, MaskBound K p q := by
  refine ⟨ceiling p q d, maskBound_of_counts (d := d) ?_⟩
  intro c n
  exact (count_of_certificate (fun A t => weight p q A c t d) c
    (fun A t => (weight_bounds p q hp A c t d).1)
    (fun A t => physical_block_certificate hb A c t) Set.univ 0 n).trans
    (Nat.mul_le_mul_left _ (weight_bounds p q hp Set.univ c 0 d).2)

def window (a : ℕ) (c : ℕ → Bool) (t : ℕ) : Fin a → Bool := fun i => c (t+i)

/-- A finite table on subsets of width d+1 and a future of any chosen length a.
The step test uses at most a+1 consecutive wall bits, including when a is zero. -/
structure Certificate (d a K p q : ℕ) where
  V : Set (Strip d) → (Fin a → Bool) → ℕ
  base : ∀ S c t, count S c t 0 ≤ V S (window a c t)
  top : ∀ f, V Set.univ f ≤ K
  step : ∀ S c t, q * (V (child S (c t) false) (window a c (t+1)) +
    V (child S (c t) true) (window a c (t+1))) ≤ p * V S (window a c t)

theorem Certificate.maskBound {d a K p q : ℕ} (C : Certificate d a K p q) : MaskBound K p q := by
  apply maskBound_of_counts (d := d)
  intro c n
  exact (count_of_certificate (fun S t => C.V S (window a c t)) c (fun S t => C.base S c t)
    (fun S t => C.step S c t) Set.univ 0 n).trans (Nat.mul_le_mul_left _ (C.top _))

/-- Compile a physical block bound to an actual finite table with width d+1 and d bits ahead. -/
noncomputable def certificateOfBlock {d p q : ℕ} (hp : 0 < p) (hb : PhysicalBlock (d+1) p q) :
    Certificate d d (ceiling p q d) p q := by
  let pad (f : Fin d → Bool) (i : ℕ) := if hi : i < d then f ⟨i,hi⟩ else false
  let V (S : Set (Strip d)) (f : Fin d → Bool) := weight p q S (pad f) 0 d
  have readV (S : Set (Strip d)) (c : ℕ → Bool) (t : ℕ) :
      V S (window d c t) = weight p q S c t d := by
    apply weight_agree
    intro i hi
    simp [pad,window,hi]
  exact { V := V
          base := fun S c t => by rw [readV]; exact (weight_bounds p q hp S c t d).1
          top := fun f => (weight_bounds p q hp Set.univ (pad f) 0 d).2
          step := fun S c t => by simp only [readV]; exact physical_block_certificate hb S c t }

def Consequences (K p q : ℕ) : Prop :=
    (Dynamics.coverEntropy (fun x : ℤ → Bool => evol x 1) Set.univ ≤
      ENNReal.log (ENNReal.ofReal (2 * ((p : ℝ) / q)))) ∧
    ∀ {T P : ℕ}, 0 < P → (∀ t, T ≤ t → Rule30Jen.cell (t+P) 0 = Rule30Jen.cell t 0) →
      ∀ w, Rule30HorizontalDiversity.H w ≤ T + P * (K * p^w / q^w)

theorem both_of_mask {K p q : ℕ} (hq : 0 < q) (hK : MaskBound K p q) : Consequences K p q := by
  refine ⟨entropy_le_of_mask hq hK,?_⟩
  choose L hlen hmem using hK
  intro T P hP per w
  apply Rule30HorizontalDiversity.horizontal_count_of_channel L
      (budget := fun n => K * p^n / q^n) _ _ hP per w
  · intro bs
    exact (Nat.le_div_iff_mul_le (Nat.pow_pos hq)).2 (hlen bs)
  · intro x t n
    let bs := actualWall x t n
    have len : bs.length = n := by simp [bs,actualWall,segment_eq_ofFn]
    have h := hmem bs x t (by rw [len]; rfl)
    rw [len] at h
    exact h

/-- One table at any width and look-ahead bounds both the full-map entropy and the
horizontal vocabulary of the single seed under an eventual centre period. -/
theorem both_of_certificate {d a K p q : ℕ} (hq : 0 < q) (C : Certificate d a K p q) :
    Consequences K p q := both_of_mask hq C.maskBound

theorem both_of_physical_block {d p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hb : PhysicalBlock (d+1) p q) :
    ∃ K, Consequences K p q := by
  obtain ⟨K,hK⟩ := maskBound_of_physical_block hp hb
  exact ⟨K,both_of_mask hq hK⟩

/-- Largest number of physical masks at length d+1. Exactness is `exact_at_width`. -/
noncomputable def peak (d : ℕ) : ℕ :=
  Finset.univ.sup fun v : Fin (d+1) → Bool => (words (Set.univ : Set (Strip d)) (List.ofFn v)).length

theorem physical_block_of_peak {d p q : ℕ} (h : peak d * q^(d+1) ≤ p^(d+1)) :
    PhysicalBlock (d+1) p q := by
  intro c
  let v : Fin (d+1) → Bool := fun i => c i
  have eqw : segment c 0 (d+1) = List.ofFn v := by simp [segment_eq_ofFn,v]
  let L := words (Set.univ : Set (Strip d)) (List.ofFn v)
  have hL : L.length ≤ peak d := Finset.le_sup (f := fun u : Fin (d+1) → Bool =>
    (words (Set.univ : Set (Strip d)) (List.ofFn u)).length) (Finset.mem_univ v)
  refine ⟨L,(Nat.mul_le_mul_right _ hL).trans h,?_⟩
  intro x hc
  simpa only [L,← eqw] using (exact_at_width c (le_refl (d+1)) _).2 ⟨x,hc,rfl⟩

/-- Infimum of the finite physical worst-wall log rates, in nats per tick. -/
noncomputable def worstLog : ℝ := ⨅ d : ℕ, Real.log (peak d) / ((d : ℝ)+1)

/-- Each rational base strictly above the physical block infimum has a finite-block
witness and therefore the integer certificate and both consequences above. -/
theorem strict_rate_has_block {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hr : worstLog < Real.log ((p : ℝ)/q)) : ∃ d, PhysicalBlock (d+1) p q := by
  have hex : ∃ d : ℕ, Real.log (peak d) / ((d : ℝ)+1) < Real.log ((p : ℝ)/q) := by
    by_contra! h
    exact (not_le_of_gt hr) (le_ciInf h)
  obtain ⟨d,hd⟩ := hex
  refine ⟨d,physical_block_of_peak ?_⟩
  by_cases hz : peak d = 0
  · simp [hz]
  have hpos : (0 : ℝ) < peak d := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he := (div_lt_iff₀ (show (0 : ℝ) < d+1 by positivity)).mp hd
  rw [Real.log_div hpr.ne' hqr.ne'] at he
  have hl : Real.log ((peak d : ℝ) * (q : ℝ)^(d+1)) ≤ Real.log ((p : ℝ)^(d+1)) := by
    rw [Real.log_mul hpos.ne' (by positivity),Real.log_pow,Real.log_pow]
    push_cast
    nlinarith
  have hn := (Real.log_le_log_iff (by positivity) (by positivity)).mp hl
  exact_mod_cast hn

/-- Every strict rational upper rate has a finite integer witness, with both physical conclusions. -/
theorem strict_rate_has_certificate {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hr : worstLog < Real.log ((p : ℝ)/q)) :
    ∃ d K, Nonempty (Certificate d d K p q) ∧ Consequences K p q := by
  obtain ⟨d,hb⟩ := strict_rate_has_block hp hq hr
  let C := certificateOfBlock hp hb
  exact ⟨d,_,⟨C⟩,both_of_certificate hq C⟩

end Rule30Equivalents.LookaheadHearing
