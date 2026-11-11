module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Rule 30, zero-boundary left half: unrestricted tail closing fails on the constrained class

Three starts of the zero-boundary left half (`Rule30ZeroBoundary.zrow`), read from depth `1`
(depth `0` is the white wall):

* `rowA`: the period-`7` word `1011111`;
* `rowB`: black at depths `1, 2`, then the period-`14` word `01001011001000` from depth `3`;
* `rowC`: the period-`7` word `1100001`.

**The cycle.** Write `G` for two ticks. Then `G A = C`, `G B = C` and `G C = A` at every depth
(`two_A`, `two_B`, `two_C`, `two_cycle`). Two ticks at depth `k ≥ 3` read the start at depths
`k - 2, …, k + 2` only (`zrow_two`), so each identity passes from `k` to `k + 7` (or `k + 14`)
(`two_shift`, `periodic_ind`), and one period of depths is checked by `decide`.

**Membership of the constrained class `K = InX`.** The even-tick rows cycle `A, C, A, C, …` and
`B, C, A, C, …`, and each of these rows is black at depth `1`, so all three starts are in `InX`
(`inX_A`, `inX_B`, `inX_C`). Their free words (depth `1` at the odd ticks) are `fA = 1010…`,
`fB = 001010…` and `fC = 0101…` (`free_A`, `free_B`, `free_C`), so `zrow rowA 0 = Theta fA`, and
likewise for `B` and `C` (`theta_A`, `theta_B`, `theta_C`, by `Theta_unique`).

**Infinite mismatch.** `A` and `B` differ at every depth `14 q + 3` (`differ_AB`), so they agree on
no tail of depths. One tick already separates them at every depth `14 q + 4`, where the
neighbourhoods read `111` in `A` and `010` in `B` (`differ_one_tick`).

**Unrestricted closing fails on `K`.** `not_unrestricted_closing`: two starts in `K` with the same
row after one double step need not agree on any tail. So the unrestricted eventual-tail closing
property, with no hypothesis on the gate streams, fails on `K`.

Context, not a theorem of this module: this does not contradict the guarded `HomoclinicClosing`
and `AllPastClosing` of open kit pull request 52, which assume `GateLegal` gate streams. In the
convention of that pull request the gate words are the complemented even heads one tick later, and
the common future here starts with the window value `85`, outside its ten legal windows.

Nothing here decides `Q01` or period 2.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30UnrestrictedClosing

open Rule30ZeroBoundary

/-! ### Locality of one and two ticks -/

/-- One tick at depth `j + 2` reads the start at depths `j + 1, j + 2, j + 3`. -/
theorem zrow_one (L : Nat → Bool) (j : Nat) :
    zrow L 1 (j + 2) = xor (L (j + 3)) (L (j + 2) || L (j + 1)) :=
  rfl

/-- Two ticks at depth `j + 3` read the start at depths `j + 1, …, j + 5` only. -/
theorem zrow_two (L : Nat → Bool) (j : Nat) :
    zrow L 2 (j + 3) =
      xor (xor (L (j + 5)) (L (j + 4) || L (j + 3)))
        (xor (L (j + 4)) (L (j + 3) || L (j + 2)) || xor (L (j + 3)) (L (j + 2) || L (j + 1))) :=
  rfl

/-- Two ticks commute with a shift by `p` of a start that is `p`-periodic from depth `a ≥ 1` on,
at the depths `k ≥ a + 2`. -/
theorem two_shift {L : Nat → Bool} {a p : Nat} (ha : 1 ≤ a) (hL : ∀ d, a ≤ d → L (d + p) = L d)
    {k : Nat} (hk : a + 2 ≤ k) : zrow L 2 (k + p) = zrow L 2 k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have h : ∀ i, 1 ≤ i → L (j + p + i) = L (j + i) := fun i hi => by
    rw [show j + p + i = (j + i) + p by omega]
    exact hL _ (by omega)
  rw [show j + 3 + p = (j + p) + 3 by omega, zrow_two, zrow_two, h 1 (by omega), h 2 (by omega),
    h 3 (by omega), h 4 (by omega), h 5 (by omega)]

/-- **Periodic induction.** A property that holds below `m + p` and passes from `k` to `k + p` for
every `k ≥ m` holds everywhere. -/
theorem periodic_ind {P : Nat → Prop} {m p : Nat} (hp : 0 < p) (base : ∀ k, k < m + p → P k)
    (step : ∀ k, m ≤ k → P k → P (k + p)) : ∀ k, P k := by
  have h : ∀ n k, k < n → P k := by
    intro n
    induction n with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ n ih =>
      intro k hk
      by_cases hb : k < m + p
      · exact base k hb
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + p := ⟨k - p, by omega⟩
        exact step j (by omega) (ih j (by omega))
  exact fun k => h (k + 1) k (by omega)

/-! ### The three rows -/

/-- Row `A`: the period-`7` word `1011111`, read from depth `1`. Depth `0` is the white wall. -/
def rowA (d : Nat) : Bool :=
  if d = 0 then false else [1, 0, 1, 1, 1, 1, 1].getD ((d - 1) % 7) 0 == 1

/-- Row `B`: black at depths `1, 2`, then the period-`14` word `01001011001000` from depth `3`. -/
def rowB (d : Nat) : Bool :=
  if d = 0 then false else if d ≤ 2 then true else
    [0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0].getD ((d - 3) % 14) 0 == 1

/-- Row `C`: the period-`7` word `1100001`, read from depth `1`. -/
def rowC (d : Nat) : Bool :=
  if d = 0 then false else [1, 1, 0, 0, 0, 0, 1].getD ((d - 1) % 7) 0 == 1

theorem rowA_add (d q : Nat) (hd : 1 ≤ d) : rowA (d + 7 * q) = rowA d := by
  unfold rowA
  rw [ite_eq_right (show ¬ d + 7 * q = 0 by omega), ite_eq_right (show ¬ d = 0 by omega),
    show (d + 7 * q - 1) % 7 = (d - 1) % 7 by omega]

theorem rowB_add (d q : Nat) (hd : 3 ≤ d) : rowB (d + 14 * q) = rowB d := by
  unfold rowB
  rw [ite_eq_right (show ¬ d + 14 * q = 0 by omega), ite_eq_right (show ¬ d + 14 * q ≤ 2 by omega),
    ite_eq_right (show ¬ d = 0 by omega), ite_eq_right (show ¬ d ≤ 2 by omega),
    show (d + 14 * q - 3) % 14 = (d - 3) % 14 by omega]

theorem rowC_add (d q : Nat) (hd : 1 ≤ d) : rowC (d + 7 * q) = rowC d := by
  unfold rowC
  rw [ite_eq_right (show ¬ d + 7 * q = 0 by omega), ite_eq_right (show ¬ d = 0 by omega),
    show (d + 7 * q - 1) % 7 = (d - 1) % 7 by omega]

theorem rowA_period (d : Nat) (hd : 1 ≤ d) : rowA (d + 7) = rowA d := rowA_add d 1 hd

theorem rowB_period (d : Nat) (hd : 3 ≤ d) : rowB (d + 14) = rowB d := rowB_add d 1 hd

theorem rowC_period (d : Nat) (hd : 1 ≤ d) : rowC (d + 7) = rowC d := rowC_add d 1 hd

/-! ### The two-tick cycle -/

/-- `G A = C`: two ticks take row `A` to row `C`, at every depth. -/
theorem two_A : ∀ k, zrow rowA 2 k = rowC k := by
  refine periodic_ind (m := 3) (p := 7) (by decide) (by decide) fun k hk ih => ?_
  rw [two_shift (Nat.le_refl 1) rowA_period (by omega), ih, rowC_period k (by omega)]

/-- `G B = C`: two ticks take row `B` to row `C`, at every depth. -/
theorem two_B : ∀ k, zrow rowB 2 k = rowC k := by
  refine periodic_ind (m := 5) (p := 14) (by decide) (by decide) fun k hk ih => ?_
  have hC : rowC (k + 14) = rowC k := rowC_add k 2 (by omega)
  rw [two_shift (a := 3) (by decide) rowB_period (by omega), ih, hC]

/-- `G C = A`: two ticks take row `C` to row `A`, at every depth. -/
theorem two_C : ∀ k, zrow rowC 2 k = rowA k := by
  refine periodic_ind (m := 3) (p := 7) (by decide) (by decide) fun k hk ih => ?_
  rw [two_shift (Nat.le_refl 1) rowC_period (by omega), ih, rowA_period k (by omega)]

/-- The cycle as equalities of rows: `G A = G B = C` and `G C = A`. -/
theorem two_cycle : zrow rowA 2 = rowC ∧ zrow rowB 2 = rowC ∧ zrow rowC 2 = rowA :=
  ⟨funext two_A, funext two_B, funext two_C⟩

/-! ### Membership of the constrained class -/

theorem inX_AC (s : Nat) : zrow rowA (2 * s) 1 = true ∧ zrow rowC (2 * s) 1 = true := by
  induction s with
  | zero => exact ⟨rfl, rfl⟩
  | succ s ih =>
    rw [show 2 * (s + 1) = 2 + 2 * s by omega, zrow_shift rowA 2, zrow_shift rowC 2,
      two_cycle.1, two_cycle.2.2]
    exact ⟨ih.2, ih.1⟩

theorem inX_A : InX rowA := fun s => (inX_AC s).1

theorem inX_C : InX rowC := fun s => (inX_AC s).2

theorem inX_B : InX rowB := by
  intro s
  cases s with
  | zero => rfl
  | succ s =>
    rw [show 2 * (s + 1) = 2 + 2 * s by omega, zrow_shift rowB 2, two_cycle.2.1]
    exact inX_C s

/-! ### The free words -/

/-- The free word `1010…` of row `A`. -/
def fA (s : Nat) : Bool := decide (s % 2 = 0)

/-- The free word `001010…` of row `B`. -/
def fB (s : Nat) : Bool := decide (2 ≤ s ∧ s % 2 = 0)

/-- The free word `0101…` of row `C`. -/
def fC (s : Nat) : Bool := decide (s % 2 = 1)

theorem fA_succ (s : Nat) : fA (s + 1) = fC s := by
  unfold fA fC; exact decide_eq_decide.mpr (by omega)

theorem fB_succ (s : Nat) : fB (s + 1) = fC s := by
  unfold fB fC; exact decide_eq_decide.mpr (by omega)

theorem fC_succ (s : Nat) : fC (s + 1) = fA s := by
  unfold fC fA; exact decide_eq_decide.mpr (by omega)

theorem free_AC (s : Nat) : zrow rowA (2 * s + 1) 1 = fA s ∧ zrow rowC (2 * s + 1) 1 = fC s := by
  induction s with
  | zero => exact ⟨rfl, rfl⟩
  | succ s ih =>
    rw [show 2 * (s + 1) + 1 = 2 + (2 * s + 1) by omega, zrow_shift rowA 2, zrow_shift rowC 2,
      two_cycle.1, two_cycle.2.2, fA_succ, fC_succ]
    exact ⟨ih.2, ih.1⟩

theorem free_A : ∀ s, zrow rowA (2 * s + 1) 1 = fA s := fun s => (free_AC s).1

theorem free_C : ∀ s, zrow rowC (2 * s + 1) 1 = fC s := fun s => (free_AC s).2

theorem free_B : ∀ s, zrow rowB (2 * s + 1) 1 = fB s := by
  intro s
  cases s with
  | zero => rfl
  | succ s =>
    rw [show 2 * (s + 1) + 1 = 2 + (2 * s + 1) by omega, zrow_shift rowB 2, two_cycle.2.1,
      fB_succ]
    exact free_C s

theorem theta_A : zrow rowA 0 = Theta fA := Theta_unique inX_A free_A

theorem theta_B : zrow rowB 0 = Theta fB := Theta_unique inX_B free_B

theorem theta_C : zrow rowC 0 = Theta fC := Theta_unique inX_C free_C

/-! ### The mismatch -/

/-- Rows `A` and `B` differ at every depth `14 q + 3`: `A` is black there and `B` is white. -/
theorem differ_AB : ∀ q, rowA (14 * q + 3) ≠ rowB (14 * q + 3) := by
  intro q
  rw [show 14 * q + 3 = 3 + 7 * (2 * q) by omega, rowA_add 3 (2 * q) (by decide),
    show 3 + 7 * (2 * q) = 3 + 14 * q by omega, rowB_add 3 q (Nat.le_refl 3)]
  decide

/-- One tick separates `A` and `B` at every depth `14 q + 4`: the neighbourhoods read `111` in `A`
and `010` in `B`. -/
theorem differ_one_tick : ∀ q, zrow rowA 1 (14 * q + 4) = false ∧ zrow rowB 1 (14 * q + 4) = true := by
  intro q
  have hA : ∀ i, 1 ≤ i → rowA (14 * q + 2 + i) = rowA (2 + i) := fun i hi => by
    rw [show 14 * q + 2 + i = (2 + i) + 7 * (2 * q) by omega, rowA_add _ _ (by omega)]
  have hB : ∀ i, 1 ≤ i → rowB (14 * q + 2 + i) = rowB (2 + i) := fun i hi => by
    rw [show 14 * q + 2 + i = (2 + i) + 14 * q by omega, rowB_add _ _ (by omega)]
  rw [show 14 * q + 4 = (14 * q + 2) + 2 by omega, zrow_one, zrow_one, hA 1 (by omega),
    hA 2 (by omega), hA 3 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega)]
  decide

/-! ### Closing -/

/-- **Unrestricted tail closing fails on the constrained class.** It is not true that any two
constrained starts (`InX`) with the same row after one double step (two ticks) agree on a tail of
depths: `rowA` and `rowB` are constrained, have the common image `rowC`, and differ at every depth
`14 q + 3`.

This negates the unrestricted eventual-tail closing property on `K`, after one double step, with no
hypothesis on the gate streams. The legal-gate formulations, which assume legality of the gate
streams, are not contradicted. -/
theorem not_unrestricted_closing :
    ¬ ∀ L L' : Nat → Bool, InX L → InX L' → (∀ k, zrow L 2 k = zrow L' 2 k) →
      ∃ N, ∀ k, N ≤ k → L k = L' k := by
  intro h
  obtain ⟨N, hN⟩ := h rowA rowB inX_A inX_B fun k => by rw [two_A, two_B]
  exact differ_AB N (hN (14 * N + 3) (by omega))

/-! ### Exact free-tail characterization of `2m`-tick collisions, full-trajectory coalescence for `t ≥ 2`, and infinite violation of minimum-gap-3 gate spacing -/

/-- **Full-Trajectory Coalescence of `rowA` and `rowB` from Tick `2` Onward (`zrow_rowA_eq_zrow_rowB_of_ge_two`):**
although `rowA` and `rowB` differ infinitely often at `t = 0` (`differ_AB`) and `t = 1`
(`differ_one_tick`), for every time `t ≥ 2` and every depth `k : Nat`, `zrow rowA t k = zrow rowB t k`. -/
theorem zrow_rowA_eq_zrow_rowB_of_ge_two {t : Nat} (ht : 2 ≤ t) (k : Nat) :
    zrow rowA t k = zrow rowB t k := by
  obtain ⟨d, rfl⟩ : ∃ d, t = 2 + d := ⟨t - 2, by omega⟩
  rw [zrow_shift rowA 2 d, zrow_shift rowB 2 d, two_cycle.1, two_cycle.2.1]

/-- **Exact `4`-Tick Periodicity of `rowA` and `rowC` (`four_tick_cycle_AC`):**
for every `m, k : Nat`, `zrow rowA (4 * m) k = rowA k`, `zrow rowA (4 * m + 2) k = rowC k`,
`zrow rowC (4 * m) k = rowC k`, and `zrow rowC (4 * m + 2) k = rowA k`. -/
theorem four_tick_cycle_AC (m : Nat) :
    zrow rowA (4 * m) = rowA ∧ zrow rowA (4 * m + 2) = rowC ∧
    zrow rowC (4 * m) = rowC ∧ zrow rowC (4 * m + 2) = rowA := by
  induction m with
  | zero =>
    refine ⟨?_, two_cycle.1, ?_, two_cycle.2.2⟩
    · funext k; cases k <;> rfl
    · funext k; cases k <;> rfl
  | succ m ih =>
    have hA0 : zrow rowA (4 * (m + 1)) = rowA := by
      funext k
      rw [show 4 * (m + 1) = 2 + (4 * m + 2) by omega, zrow_shift rowA 2, two_cycle.1]
      exact congrFun ih.2.2.2 k
    have hC0 : zrow rowC (4 * (m + 1)) = rowC := by
      funext k
      rw [show 4 * (m + 1) = 2 + (4 * m + 2) by omega, zrow_shift rowC 2, two_cycle.2.2]
      exact congrFun ih.2.1 k
    have hA2 : zrow rowA (4 * (m + 1) + 2) = rowC := by
      funext k
      rw [show 4 * (m + 1) + 2 = (4 * (m + 1)) + 2 by omega, zrow_shift rowA (4 * (m + 1)) 2, hA0, two_A]
    have hC2 : zrow rowC (4 * (m + 1) + 2) = rowA := by
      funext k
      rw [show 4 * (m + 1) + 2 = (4 * (m + 1)) + 2 by omega, zrow_shift rowC (4 * (m + 1)) 2, hC0, two_C]
    exact ⟨hA0, hA2, hC0, hC2⟩

/-- **Single-Bit Initial Discrepancy Between `fA` and `fB` (`fA_eq_fB_iff`):**
the free words `fA` and `fB` disagree at `s = 0` (`fA 0 = true`, `fB 0 = false`) and agree at
every `s ≥ 1` (`fA s = fB s ↔ s ≠ 0`). -/
theorem fA_eq_fB_iff (s : Nat) : (fA s = fB s) ↔ s ≠ 0 := by
  cases s with
  | zero => decide
  | succ s =>
    rw [fA_succ, fB_succ]
    exact ⟨fun _ h => Nat.noConfusion h, fun _ => rfl⟩

/-- **`InX` and Free-Word Shift Law Under `2 * m` Ticks (`inX_and_free_shift`):**
if `InX L`, then `InX (zrow L (2 * m))` holds and its free word is the `m`-shifted free word
`zrow (zrow L (2 * m)) (2 * s + 1) 1 = zrow L (2 * (m + s) + 1) 1`. -/
theorem inX_and_free_shift {L : Nat → Bool} (hL : InX L) (m : Nat) :
    InX (zrow L (2 * m)) ∧
      ∀ s : Nat, zrow (zrow L (2 * m)) (2 * s + 1) 1 = zrow L (2 * (m + s) + 1) 1 := by
  refine ⟨fun s => ?_, fun s => ?_⟩
  · rw [← zrow_shift L (2 * m) (2 * s), show 2 * m + 2 * s = 2 * (m + s) by omega]
    exact hL (m + s)
  · rw [← zrow_shift L (2 * m) (2 * s + 1), show 2 * m + (2 * s + 1) = 2 * (m + s) + 1 by omega]

/-- **Exact Free-Tail Characterization of `2 * m`-Tick Collisions on `InX`
(`zrow_two_mul_eq_iff_free_tail_eq`):** for any two constrained starts `L, L'` (`InX L`, `InX L'`)
and any `m : Nat`, their rows after `m` double steps agree everywhere
(`∀ k, zrow L (2 * m) k = zrow L' (2 * m) k`) if and only if their odd-tick free words agree
from index `m` onward (`∀ s, zrow L (2 * (m + s) + 1) 1 = zrow L' (2 * (m + s) + 1) 1`). -/
theorem zrow_two_mul_eq_iff_free_tail_eq {L L' : Nat → Bool} (hL : InX L) (hL' : InX L') (m : Nat) :
    (∀ k : Nat, zrow L (2 * m) k = zrow L' (2 * m) k) ↔
      (∀ s : Nat, zrow L (2 * (m + s) + 1) 1 = zrow L' (2 * (m + s) + 1) 1) := by
  obtain ⟨hLm, hfL⟩ := inX_and_free_shift hL m
  obtain ⟨hL'm, hfL'⟩ := inX_and_free_shift hL' m
  constructor
  · intro heq s
    rw [← hfL s, ← hfL' s, show zrow L (2 * m) = zrow L' (2 * m) from funext heq]
  · intro hfree k
    have hθL := Theta_unique hLm hfL
    have hθL' := Theta_unique hL'm (fun s => by rw [hfL' s, ← hfree s])
    have heq0 : zrow (zrow L (2 * m)) 0 k = zrow (zrow L' (2 * m)) 0 k := by
      rw [hθL, hθL']
    cases k with
    | zero => rw [zrow_wall, zrow_wall]
    | succ k => exact heq0

/-- The complemented odd-tick gate stream of a zero-boundary start `L`:
`gateOf L s = !zrow L (2 * s + 1) 1`. -/
def gateOf (L : Nat → Bool) (s : Nat) : Bool := !zrow L (2 * s + 1) 1

/-- Minimum-gap-`3` spacing on a gate stream `G` from index `S₀` onward: no two `true` values
occur at distance `1` or `2` at or after `S₀`. -/
def SpacedFrom (S₀ : Nat) (G : Nat → Bool) : Prop :=
  ∀ s : Nat, S₀ ≤ s → G s = true → G (s + 1) = false ∧ G (s + 2) = false

/-- **Every Double-Step Preimage of `rowA` or `rowC` Violates `SpacedFrom` on Every Tail
(`not_spacedFrom_gateOf_rowA_rowB_rowC`):** for every threshold `S₀ : Nat`, none of
`gateOf rowA`, `gateOf rowB`, or `gateOf rowC` satisfies `SpacedFrom S₀` (since each has
consecutive black gates at distance `2` at arbitrarily large indices). -/
theorem not_spacedFrom_gateOf_rowA_rowB_rowC (S₀ : Nat) :
    ¬ SpacedFrom S₀ (gateOf rowA) ∧
    ¬ SpacedFrom S₀ (gateOf rowB) ∧
    ¬ SpacedFrom S₀ (gateOf rowC) := by
  refine ⟨fun hA => ?_, fun hB => ?_, fun hC => ?_⟩
  · have hs : S₀ ≤ 2 * S₀ + 1 := by omega
    have h1 : gateOf rowA (2 * S₀ + 1) = true := by
      unfold gateOf; rw [free_A]; unfold fA; rw [decide_eq_false (by omega)]; rfl
    have h3 : gateOf rowA (2 * S₀ + 1 + 2) = true := by
      unfold gateOf; rw [free_A]; unfold fA; rw [decide_eq_false (by omega)]; rfl
    have hsp := (hA (2 * S₀ + 1) hs h1).2
    rw [h3] at hsp; exact Bool.noConfusion hsp
  · have hs : S₀ ≤ 2 * S₀ + 1 := by omega
    have h1 : gateOf rowB (2 * S₀ + 1) = true := by
      unfold gateOf; rw [free_B]; unfold fB; rw [decide_eq_false (by omega)]; rfl
    have h3 : gateOf rowB (2 * S₀ + 1 + 2) = true := by
      unfold gateOf; rw [free_B]; unfold fB; rw [decide_eq_false (by omega)]; rfl
    have hsp := (hB (2 * S₀ + 1) hs h1).2
    rw [h3] at hsp; exact Bool.noConfusion hsp
  · have hs : S₀ ≤ 2 * S₀ := by omega
    have h0 : gateOf rowC (2 * S₀) = true := by
      unfold gateOf; rw [free_C]; unfold fC; rw [decide_eq_false (by omega)]; rfl
    have h2 : gateOf rowC (2 * S₀ + 2) = true := by
      unfold gateOf; rw [free_C]; unfold fC; rw [decide_eq_false (by omega)]; rfl
    have hsp := (hC (2 * S₀) hs h0).2
    rw [h2] at hsp; exact Bool.noConfusion hsp

end Rule30UnrestrictedClosing
end Ruliology.CellularAutomata
