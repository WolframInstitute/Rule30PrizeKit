module

public import Ruliology.CellularAutomata.Rule30EveryKCascade
public import Ruliology.CellularAutomata.Rule30EveryKInverse
public import Ruliology.CellularAutomata.Rule30RelaxedWindows
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Inverse ticks for every k, without the wall

The kit's every-k chain is stated beside the white wall (`Rule30EveryKStatement.PhysicalEdge`, for finite rows
of the zero-boundary left half). Its argument lives at the edge: a full band of `w` cells from the last black
cell settles onto a cycle of `bandStep w`, and the reset schedule of `Rule30EveryKCascade` (Lowry's PR #60)
fixes the edge of every `k`-tick predecessor once `k ≤ K1 w`. This module states and proves it on the line,
for every configuration `x : Int → Bool` with a leftmost black cell (`Rule30Realization.evol`):

* `kTick_edge_line`: if `0 < w` and `k ≤ K1 w`, then from age `2 ^ w` every `k`-tick predecessor `V` of the
  image (`evol V k = evol x t`) has its leftmost black cell at `lo - t + k`, the edge of `evol x (t - k)`.
* `every_k_line_of_cap`: `CAP` gives, for every `k`, an age from which this holds.
* `every_k_line_of_lInfinity`, `every_k_line_of_dlMinusOne`: the same from `LInfinity` (S4) and from the
  relaxed doubling lemma `DLMinusOne` (S5), through the kit's `cap_of_unbounded_resets` and
  `lInfinity_of_dlMinusOne`.

Nothing is assumed of the predecessors. On the line the band is full from age 0, so the settling age is the
finite-state bound `2 ^ w` alone, where the wall's version needs `w - 1 + 2 ^ w`.

**What changes from the wall.** Only the drive. `Rule30EveryKCascade.scheduled_edge` reads the layers as
`zrow P k`; here `scheduled_edge_rows` takes any chain of rows each driven by the next (`Drives`), and the
layers of a predecessor on the line, read in depth from an anchor right of the band, are such a chain
(`drives_line`). The band of the line evolves by the kit's `stepK` (`bandK_step`); pigeonhole on its `2 ^ w`
values puts it on a cycle by age `2 ^ w` (`on_cycle`, restating the kit's private `collision`); and the kit's
public `capacity_on_cycle` gives the capacity. Credit: the reset schedule and its cascade are Lowry's
(`Rule30EveryKCascade`, PR #60); `K1`, `CAP` and the statement are the kit's (`Rule30EveryKStatement`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EveryKLine

open Rule30Jen Rule30Realization Rule30FiniteConfigs Rule30EveryKStatement Rule30EveryKCascade
  Rule30EveryKInverse Rule30UniversalLeftSide

/-! ## The band of the line, in the kit's every-k order: bit `j` is the cell `j` places in from the edge -/

def bandK (c : Int → Bool) (f : Int) : Nat → Nat
  | 0 => 0
  | w + 1 => (if c (f + w) then 2 ^ w else 0) + bandK c f w

theorem bandK_lt (c : Int → Bool) (f : Int) : ∀ w, bandK c f w < 2 ^ w
  | 0 => by simp [bandK]
  | w + 1 => by
    have := bandK_lt c f w
    simp only [bandK, Nat.pow_succ]
    split <;> omega

theorem testBit_bandK (c : Int → Bool) (f : Int) : ∀ (w j : Nat),
    (bandK c f w).testBit j = (decide (j < w) && c (f + j))
  | 0, j => by simp [bandK]
  | w + 1, j => by
    have hlt := bandK_lt c f w
    rcases Nat.lt_trichotomy j w with h | rfl | h
    · have ih := testBit_bandK c f w j
      simp only [bandK]
      split
      · rw [Nat.testBit_two_pow_add_gt h, ih]; simp [h, show j < w + 1 by omega]
      · rw [Nat.zero_add, ih]; simp [h, show j < w + 1 by omega]
    · simp only [bandK]
      split <;> rename_i hc
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; simp [hc]
      · rw [Nat.zero_add, Nat.testBit_lt_two_pow hlt]
        simp only [Bool.not_eq_true] at hc; simp [hc]
    · have hb := bandK_lt c f (w + 1)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) h))]
      simp [show ¬ j < w + 1 by omega]

/-- One step of rule 30 on the line. -/
def stepLine (c : Int → Bool) : Int → Bool := fun p => rule (c (p - 1)) (c p) (c (p + 1))

theorem evol_succ (x : Int → Bool) (t : Nat) : evol x (t + 1) = stepLine (evol x t) := rfl

/-- **The band moves out by one and updates by the kit's `stepK`**, for a configuration white left of `f`. -/
theorem bandK_step (c : Int → Bool) (f : Int) (w : Nat) (hw : ∀ p, p < f → c p = false) :
    bandK (stepLine c) (f - 1) w = stepK w (bandK c f w) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bandK]
  simp only [stepK, Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
    testBit_bandK]
  by_cases hj : j < w
  · simp only [hj, decide_true, Bool.true_and, stepLine, rule]
    by_cases h2 : 2 ≤ j
    · have p1 : f - 1 + (j : Int) - 1 = f + ((j - 2 : Nat) : Int) := by omega
      have p2 : f - 1 + (j : Int) = f + ((j - 1 : Nat) : Int) := by omega
      have p3 : f - 1 + (j : Int) + 1 = f + (j : Int) := by omega
      rw [p3, p1, p2]
      simp [show j ≥ 2 by omega, show j ≥ 1 by omega, show j - 2 < w by omega, show j - 1 < w by omega]
    · by_cases h1 : j = 1
      · subst h1
        rw [show f - 1 + ((1 : Nat) : Int) + 1 = f + ((1 : Nat) : Int) by omega,
          show f - 1 + ((1 : Nat) : Int) - 1 = f - 1 by omega, show f - 1 + ((1 : Nat) : Int) = f + ((0 : Nat) : Int) by omega,
          hw (f - 1) (by omega)]
        simp [show (0 : Nat) < w by omega]
      · have h0 : j = 0 := by omega
        subst h0
        rw [show f - 1 + ((0 : Nat) : Int) + 1 = f + ((0 : Nat) : Int) by omega,
          show f - 1 + ((0 : Nat) : Int) - 1 = f - 2 by omega, show f - 1 + ((0 : Nat) : Int) = f - 1 by omega,
          hw (f - 2) (by omega), hw (f - 1) (by omega)]
        simp
  · simp [hj]

section Edge

variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)

include hzero in
theorem bandK_evol (w : Nat) : ∀ t : Nat, bandK (evol x t) (lo - t) w = rowAt w (bandK x lo w) t
  | 0 => by simp [evol, rowAt]
  | t + 1 => by
    rw [evol_succ, show lo - ((t + 1 : Nat) : Int) = lo - t - 1 by push_cast; omega,
      bandK_step _ _ _ (fun p hp => evol_eq_false_of_lt hzero t p hp), bandK_evol w t]
    rfl

end Edge

/-! ## On a cycle by age `2 ^ w` -/

/-- Pigeonhole, as the kit's private `Rule30EveryKInverse.collision`. -/
theorem collision (N : Nat) (a : Nat → Nat) (h : ∀ t, a t < N) :
    ∃ i j, i < j ∧ j ≤ N ∧ a i = a j := by
  apply Classical.byContradiction
  intro hn
  have nd := Rule30Jen.nodup_map_of_inj a (List.nodup_range (n := N+1)) (by
    intro i hi j hj e
    simp only [List.mem_range] at hi hj
    rcases Nat.lt_trichotomy i j with lt | eq | gt
    · exact (hn ⟨i,j,lt,by omega,e⟩).elim
    · exact eq
    · exact (hn ⟨j,i,gt,by omega,e.symm⟩).elim)
  have size := Rule30Jen.length_le_of_subset (l₂ := List.range N) nd (by
    intro x hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (h t))
  simp at size
  omega

theorem rowAt_add (w v i n : Nat) : rowAt w v (i + n) = rowAt w (rowAt w v i) n := by
  induction n with
  | zero => rfl
  | succ n ih => show stepK w (rowAt w v (i + n)) = stepK w (rowAt w (rowAt w v i) n); rw [ih]

theorem stepK_lt (w v : Nat) : stepK w v < 2 ^ w := Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem rowAt_lt (w v : Nat) (hv : v < 2 ^ w) : ∀ t, rowAt w v t < 2 ^ w
  | 0 => hv
  | _ + 1 => stepK_lt w _

/-- From step `2 ^ w` on, an orbit of `stepK w` is on a cycle. -/
theorem on_cycle (w v : Nat) (hv : v < 2 ^ w) (t : Nat) (ht : 2 ^ w ≤ t) :
    ∃ q, 0 < q ∧ rowAt w (rowAt w v t) q = rowAt w v t := by
  obtain ⟨i, j, hij, hj, e⟩ := collision (2 ^ w) (fun s => rowAt w v s) (rowAt_lt w v hv)
  refine ⟨j - i, by omega, ?_⟩
  rw [← rowAt_add]
  have shift : ∀ n, rowAt w v (i + n) = rowAt w v (j + n) := fun n => by
    rw [rowAt_add, rowAt_add w v j, show rowAt w v i = rowAt w v j from e]
  rw [show t + (j - i) = j + (t - i) by omega, ← shift (t - i), show i + (t - i) = t by omega]

/-! ## The schedule, for any chain of driven rows -/

/-- `Rule30EveryKCascade.scheduled_edge`, with the layers given as any chain of rows each driven by the next. -/
theorem scheduled_edge_rows {w v q : Nat} (hq : 0 < q) (cycle : bandAt w v q = v)
    (Ps : Nat → Row) (drive : ∀ i, Drives (Ps (i + 1)) (Ps i) 0)
    (fuel d a k e : Nat) (width : a ≤ w) (full : a ≤ e)
    (matched : Matches (Ps k) e (earlier w v q d) a)
    (closed : k ≤ schedule w v q fuel d a) :
    Ps 0 (e - k) = true ∧ ∀ x, e - k < x → Ps 0 x = false := by
  induction fuel generalizing d a k e with
  | zero =>
    have hk : k = 0 := by simpa [schedule] using closed
    subst k
    exact ⟨matched.1, fun x hx => (matched.2 x (by omega)).trans
      (by simp [reference, show ¬ x ≤ e by omega])⟩
  | succ fuel ih =>
    cases k with
    | zero => exact ⟨matched.1, fun x hx => (matched.2 x (by omega)).trans
        (by simp [reference, show ¬ x ≤ e by omega])⟩
    | succ k =>
      simp only [schedule] at closed
      cases h : firstReset (earlier w v q d) a with
      | none =>
        unfold earlier at h
        simp only [h] at closed
        omega
      | some j =>
        have fj := h
        unfold earlier at h
        simp only [h] at closed
        obtain ⟨m, bound, _⟩ := firstReset_spec fj
        rw [← earlier_step hq cycle d] at fj matched
        have next := scheduled_layer full width (drive k) matched fj
        have result := ih (d+1) j k (e-1) (by omega) (by omega) next (by omega)
        simpa [show e-(k+1) = e-1-k by omega] using result

/-! ## The line, read in depth from an anchor -/

/-- The cells of `z` at depth `d` from the anchor `c`: position `c - d`. -/
def depthRow (c : Int) (z : Int → Bool) : Row := fun d => z (c - d)

/-- Under rule 30, a predecessor is fixed leftward by its image: `z (p - 1) = y p ⊕ (z p ∨ z (p + 1))`. -/
theorem left_of (z : Int → Bool) (p : Int) : z (p - 1) = xor (stepLine z p) (z p || z (p + 1)) := by
  simp only [stepLine, rule]
  cases z (p - 1) <;> cases z p <;> cases z (p + 1) <;> rfl

/-- **On the line, every layer is driven by the next at every depth.** -/
theorem drives_line (c : Int) (z : Int → Bool) : Drives (depthRow c (stepLine z)) (depthRow c z) 0 := by
  intro n _
  refine Prod.ext rfl ?_
  show z (c - ((n + 1 + 1 : Nat) : Int)) = xor (stepLine z (c - ((n + 1 : Nat) : Int)))
    (z (c - ((n + 1 : Nat) : Int)) || z (c - (n : Int)))
  have h := left_of z (c - ((n + 1 : Nat) : Int))
  rw [show c - ((n + 1 : Nat) : Int) - 1 = c - ((n + 1 + 1 : Nat) : Int) by push_cast; omega,
    show c - ((n + 1 : Nat) : Int) + 1 = c - (n : Int) by push_cast; omega] at h
  exact h

/-! ## Inverse ticks for every k on the line -/

section Edge

variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

/-- **The `k`-tick edge on the line.** If `0 < w` and `k ≤ K1 w`, then from age `2 ^ w` every `k`-tick
predecessor of the image of `x` has its leftmost black cell at `lo - t + k`. -/
theorem kTick_edge_line (k w : Nat) (hw : 0 < w) (cap : k ≤ K1 w) (t : Nat) (ht : 2 ^ w ≤ t)
    (V : Int → Bool) (hV : ∀ p, evol V k p = evol x t p) :
    V (lo - t + k) = true ∧ ∀ p, p < lo - t + k → V p = false := by
  let f : Int := lo - t
  let v := bandK (evol x t) f w
  have hband : v = rowAt w (bandK x lo w) t := bandK_evol hzero w t
  have odd : OddBand w v := by
    refine ⟨bandK_lt _ _ w, ?_⟩
    rw [testBit_bandK]
    simp only [hw, decide_true, Bool.true_and, Int.natCast_zero, Int.add_zero]
    exact evol_left_edge hlo hzero t
  obtain ⟨q0, hq0, per0⟩ := on_cycle w (bandK x lo w) (bandK_lt _ _ w) t ht
  rw [← hband] at per0
  obtain ⟨q, hq, per, capq⟩ := capacity_on_cycle hw odd ⟨q0, hq0, per0⟩
  -- the anchor `c`, `w + k` cells right of the image's edge
  let c : Int := f + w + k
  let e : Nat := w + k
  let Ps : Nat → Row := fun i => depthRow c (evol V i)
  have drive : ∀ i, Drives (Ps (i + 1)) (Ps i) 0 := fun i => by
    show Drives (depthRow c (evol V (i + 1))) (depthRow c (evol V i)) 0
    rw [evol_succ]
    exact drives_line c (evol V i)
  have e0 : earlier w v q 0 = v := by
    unfold earlier
    rw [Nat.zero_mod, Nat.sub_zero, Nat.mod_self]
    rfl
  have matched : Matches (Ps k) e (earlier w v q 0) w := by
    rw [e0]
    refine ⟨?_, fun d hd => ?_⟩
    · show evol V k (c - (e : Int)) = true
      rw [hV, show c - (e : Int) = lo - t by simp only [c, e, f]; push_cast; omega]
      exact evol_left_edge hlo hzero t
    · show evol V k (c - (d : Int)) = reference e v d
      rw [hV]
      unfold reference
      split
      · rename_i hde
        rw [testBit_bandK]
        simp only [show e - d < w by omega, decide_true, Bool.true_and]
        congr 1
        simp only [c, e, f]; push_cast; omega
      · exact evol_eq_false_of_lt hzero t _ (by simp only [c]; push_cast; omega)
  have closed : k ≤ schedule w v q w 0 w := Nat.le_trans cap capq
  obtain ⟨hedge, hwhite⟩ := scheduled_edge_rows hq per Ps drive w 0 w k e (Nat.le_refl _) (by omega) matched closed
  refine ⟨?_, fun p hp => ?_⟩
  · have : Ps 0 (e - k) = V (lo - t + k) := by
      show V (c - ((e - k : Nat) : Int)) = V (lo - t + k)
      congr 1; simp only [c, e, f]; push_cast; omega
    rw [← this]; exact hedge
  · have h := hwhite (c - p).toNat (by simp only [c, e, f] at *; omega)
    have : Ps 0 (c - p).toNat = V p := by
      show V (c - (((c - p).toNat : Nat) : Int)) = V p
      congr 1; omega
    rwa [this] at h

end Edge

/-- **Every k on the line, from `CAP`.** -/
theorem every_k_line_of_cap (capacity : CAP) (k : Nat) :
    ∃ age : Nat, ∀ (x : Int → Bool) (lo : Int), x lo = true → (∀ p, p < lo → x p = false) →
      ∀ t, age ≤ t → ∀ V : Int → Bool, (∀ p, evol V k p = evol x t p) →
        V (lo - t + k) = true ∧ ∀ p, p < lo - t + k → V p = false := by
  obtain ⟨w, hw, hk⟩ := capacity k
  exact ⟨2 ^ w, fun x lo hlo hzero t ht V hV => kTick_edge_line hlo hzero k w hw hk t ht V hV⟩

/-- **Every k on the line, from `LInfinity`** (S4's hypothesis). -/
theorem every_k_line_of_lInfinity (deep : Rule30ResetCompactness.LInfinity) (k : Nat) :
    ∃ age : Nat, ∀ (x : Int → Bool) (lo : Int), x lo = true → (∀ p, p < lo → x p = false) →
      ∀ t, age ≤ t → ∀ V : Int → Bool, (∀ p, evol V k p = evol x t p) →
        V (lo - t + k) = true ∧ ∀ p, p < lo - t + k → V p = false :=
  every_k_line_of_cap (Rule30ResetCompactness.cap_of_unbounded_resets deep) k

/-- **Every k on the line, from the relaxed doubling lemma** (S5's hypothesis). -/
theorem every_k_line_of_dlMinusOne (h : Rule30RelaxedWindows.DLMinusOne) (k : Nat) :
    ∃ age : Nat, ∀ (x : Int → Bool) (lo : Int), x lo = true → (∀ p, p < lo → x p = false) →
      ∀ t, age ≤ t → ∀ V : Int → Bool, (∀ p, evol V k p = evol x t p) →
        V (lo - t + k) = true ∧ ∀ p, p < lo - t + k → V p = false :=
  every_k_line_of_lInfinity (Rule30RelaxedWindows.lInfinity_of_dlMinusOne h) k

end Ruliology.CellularAutomata.Rule30EveryKLine
