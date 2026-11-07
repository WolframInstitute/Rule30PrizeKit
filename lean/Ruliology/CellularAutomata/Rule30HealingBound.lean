module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Jen

/-!
# The universal healing bound for rule 30

For any rule-30 evolution `E` of the whole line (a background orbit: periodic or not) and any rule-30 evolution `G` that
agrees with `E` at time 0 on the columns `x ≤ -1`, define the **recruitment frontier** `K t` on diagonals `x + t`:
`K 0 = -1`, and `K (t + 1) = K t + 1` if the background cell `E t (K t - t)` is black, else `K t`. Then `G` agrees with
`E` at every cell on a diagonal `x + t ≤ K t` (`healing_bound`). A black centre masks its right neighbour, so a diagonal
whose newest known cell is black is recruited at the next tick. The leftmost disagreement at time `t` therefore lies at
`x ≥ K t - t + 1` (`front_ge`). Where the frontier's climb rate has a long-run mean (for a periodic background it is a
cycle mean of a finite walk on its torus), the leftward speed is at most one minus that mean.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30HealingBound
open Rule30Jen

/-- A rule-30 evolution of the whole line. -/
def IsR30Z (G : Nat → Int → Bool) : Prop :=
  ∀ t x, G (t + 1) x = rule (G t (x - 1)) (G t x) (G t (x + 1))

/-- The recruitment frontier of the background `E`, a diagonal index (`x + t`). -/
def K (E : Nat → Int → Bool) : Nat → Int
  | 0 => -1
  | t + 1 => if E t (K E t - t) then K E t + 1 else K E t

/-- **The universal healing bound.** -/
theorem healing_bound {E G : Nat → Int → Bool} (hE : IsR30Z E) (hG : IsR30Z G) (h0 : ∀ x, x ≤ -1 → G 0 x = E 0 x) :
    ∀ t x, x + t ≤ K E t → G t x = E t x := by
  intro t
  induction t with
  | zero => intro x hx; exact h0 x (by simpa [K] using hx)
  | succ t ih =>
    intro x hx
    rw [hG, hE]
    by_cases hin : x + (t : Int) + 1 ≤ K E t
    · rw [ih (x - 1) (by omega), ih x (by omega), ih (x + 1) (by omega)]
    · -- the recruited diagonal: x = K t - t and the background centre is black
      have hK : K E (t + 1) = (if E t (K E t - t) then K E t + 1 else K E t) := rfl
      cases hc : E t (K E t - t) with
      | false =>
        rw [hK, hc] at hx
        simp at hx
        omega
      | true =>
        rw [hK, hc] at hx
        simp at hx
        have hx' : x = K E t - t := by omega
        have hcen : G t x = E t x := ih x (by omega)
        have hcb : E t x = true := by rw [hx']; exact hc
        rw [ih (x - 1) (by omega), hcen, hcb]
        simp [rule]

/-- Hence the leftmost cell where `G` differs from `E` at time `t` lies at `x ≥ K t - t + 1`. -/
theorem front_ge {E G : Nat → Int → Bool} (hE : IsR30Z E) (hG : IsR30Z G) (h0 : ∀ x, x ≤ -1 → G 0 x = E 0 x)
    (t : Nat) (x : Int) (hne : G t x ≠ E t x) : K E t - t + 1 ≤ x := by
  by_cases h : x + (t : Int) ≤ K E t
  · exact absurd (healing_bound hE hG h0 t x h) hne
  · omega

/-- The frontier never falls and climbs at most one diagonal per tick. -/
theorem K_succ_bounds (E : Nat → Int → Bool) (t : Nat) : K E t ≤ K E (t + 1) ∧ K E (t + 1) ≤ K E t + 1 := by
  show K E t ≤ (if E t (K E t - t) then K E t + 1 else K E t) ∧ (if E t (K E t - t) then K E t + 1 else K E t) ≤ K E t + 1
  cases E t (K E t - t) <;> simp <;> omega

/-! ### Cumulative Frontier Bounds, Recruitment Counting, and Arbitrary-Anchor Healing -/

/-- **Multi-Step Frontier Growth Bounds (`K_add_bounds`):** for any background `E`, start time `t`,
and duration `d : Nat`, `K E t ≤ K E (t + d)` and `K E (t + d) ≤ K E t + d`. -/
theorem K_add_bounds (E : Nat → Int → Bool) (t : Nat) :
    ∀ d : Nat, K E t ≤ K E (t + d) ∧ K E (t + d) ≤ K E t + (d : Int)
  | 0 => by simp
  | d + 1 => by
    have ih := K_add_bounds E t d
    have hs := K_succ_bounds E (t + d)
    rw [show t + (d + 1) = (t + d) + 1 by omega]
    constructor <;> omega

/-- **Global Frontier Envelope (`K_bounds`):** for every background `E` and time `t : Nat`,
`-1 ≤ K E t` and `K E t ≤ (t : Int) - 1`. -/
theorem K_bounds (E : Nat → Int → Bool) (t : Nat) :
    -1 ≤ K E t ∧ K E t ≤ (t : Int) - 1 := by
  have h := K_add_bounds E 0 t
  rw [Nat.zero_add] at h
  have h0 : K E 0 = -1 := rfl
  rw [h0] at h
  omega

/-- **Monotonic Leftward Drift of the Spatial Healing Front (`front_pos_nonincreasing`):** the spatial
healing front `K E t - t` never moves right (`K E (t + 1) - (t + 1 : Int) ≤ K E t - (t : Int)`). -/
theorem front_pos_nonincreasing (E : Nat → Int → Bool) (t : Nat) :
    K E (t + 1) - ((t + 1 : Nat) : Int) ≤ K E t - (t : Int) := by
  have hs := (K_succ_bounds E t).2
  omega

/-- **Cumulative Frontier Recruitment Count (`recruitCount`):** number of ticks in `[0, t)` at which
the recruitment frontier encounters a black background cell `E s (K E s - s) = true`. -/
def recruitCount (E : Nat → Int → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => recruitCount E t + if E t (K E t - t) then 1 else 0

/-- **Exact Recruitment Identity (`K_eq_sub_one_add_recruitCount`):** at every time `t : Nat`,
`K E t = -1 + (recruitCount E t : Int)`. -/
theorem K_eq_sub_one_add_recruitCount (E : Nat → Int → Bool) :
    ∀ t : Nat, K E t = -1 + (recruitCount E t : Int)
  | 0 => rfl
  | t + 1 => by
    have ih := K_eq_sub_one_add_recruitCount E t
    show (if E t (K E t - t) then K E t + 1 else K E t) =
      -1 + ((recruitCount E t + if E t (K E t - t) then 1 else 0 : Nat) : Int)
    cases E t (K E t - t) <;> simp [ih] <;> omega

/-- **Unrecruited Light-Cone Regime (`K_eq_neg_one_of_all_white`):** if the frontier cell
`E s (K E s - s)` is white for all `s < t`, then `K E t = -1`. -/
theorem K_eq_neg_one_of_all_white (E : Nat → Int → Bool) :
    ∀ t : Nat, (∀ s, s < t → E s (K E s - s) = false) → K E t = -1
  | 0, _ => rfl
  | t + 1, hw => by
    have ih := K_eq_neg_one_of_all_white E t (fun s hs => hw s (by omega))
    have hlast := hw t (by omega)
    show (if E t (K E t - t) then K E t + 1 else K E t) = -1
    rw [hlast, ih]
    rfl

/-- **Maximally Recruited Stationary Regime (`K_eq_sub_one_of_all_black`):** if column `-1` of `E`
is black for all `s < t`, then `K E t = (t : Int) - 1`. -/
theorem K_eq_sub_one_of_all_black (E : Nat → Int → Bool) :
    ∀ t : Nat, (∀ s, s < t → E s (-1) = true) → K E t = (t : Int) - 1
  | 0, _ => rfl
  | t + 1, hb => by
    have ih := K_eq_sub_one_of_all_black E t (fun s hs => hb s (by omega))
    have hpos : K E t - (t : Int) = -1 := by omega
    have hlast : E t (K E t - t) = true := by rw [hpos]; exact hb t (by omega)
    show (if E t (K E t - t) then K E t + 1 else K E t) = ((t + 1 : Nat) : Int) - 1
    rw [hlast, ih]
    simp <;> omega

/-- **Arbitrary-Anchor Recruitment Frontier (`KFrom`):** recruitment frontier starting from any
initial agreement anchor `a : Int` at time `0`. -/
def KFrom (E : Nat → Int → Bool) (a : Int) : Nat → Int
  | 0 => a
  | t + 1 => if E t (KFrom E a t - t) then KFrom E a t + 1 else KFrom E a t

/-- **Consistency of `KFrom` at Anchor `-1` (`KFrom_neg_one_eq_K`):** `KFrom E (-1) t = K E t`. -/
theorem KFrom_neg_one_eq_K (E : Nat → Int → Bool) :
    ∀ t : Nat, KFrom E (-1) t = K E t
  | 0 => rfl
  | t + 1 => by
    show (if E t (KFrom E (-1) t - t) then KFrom E (-1) t + 1 else KFrom E (-1) t) =
      (if E t (K E t - t) then K E t + 1 else K E t)
    rw [KFrom_neg_one_eq_K E t]

/-- **Universal Healing Bound from an Arbitrary Anchor (`healing_bound_from`):** if two Rule 30
evolutions `E` and `G` agree at `t = 0` on `x ≤ a`, then at every time `t` they agree on
`x + t ≤ KFrom E a t`. -/
theorem healing_bound_from {E G : Nat → Int → Bool} (hE : IsR30Z E) (hG : IsR30Z G) {a : Int}
    (h0 : ∀ x, x ≤ a → G 0 x = E 0 x) :
    ∀ t x, x + t ≤ KFrom E a t → G t x = E t x := by
  intro t
  induction t with
  | zero => intro x hx; exact h0 x (by simpa [KFrom] using hx)
  | succ t ih =>
    intro x hx
    rw [hG, hE]
    by_cases hin : x + (t : Int) + 1 ≤ KFrom E a t
    · rw [ih (x - 1) (by omega), ih x (by omega), ih (x + 1) (by omega)]
    · have hK : KFrom E a (t + 1) = (if E t (KFrom E a t - t) then KFrom E a t + 1 else KFrom E a t) := rfl
      cases hc : E t (KFrom E a t - t) with
      | false =>
        rw [hK, hc] at hx; simp at hx; omega
      | true =>
        rw [hK, hc] at hx; simp at hx
        have hx' : x = KFrom E a t - t := by omega
        have hcen : G t x = E t x := ih x (by omega)
        have hcb : E t x = true := by rw [hx']; exact hc
        rw [ih (x - 1) (by omega), hcen, hcb]
        simp [rule]

/-- **Leftmost Disagreement Lower Bound from an Arbitrary Anchor (`front_ge_from`):** any cell `x`
where `G t x ≠ E t x` satisfies `KFrom E a t - t + 1 ≤ x`. -/
theorem front_ge_from {E G : Nat → Int → Bool} (hE : IsR30Z E) (hG : IsR30Z G) {a : Int}
    (h0 : ∀ x, x ≤ a → G 0 x = E 0 x) (t : Nat) (x : Int) (hne : G t x ≠ E t x) :
    KFrom E a t - t + 1 ≤ x := by
  by_cases h : x + (t : Int) ≤ KFrom E a t
  · exact absurd (healing_bound_from hE hG h0 t x h) hne
  · omega

/-- **Exact Anchor-Pinned Frontier Under Persistent Black Column (`KFrom_eq_add_of_col_black`):** if
column `a` of `E` is black for all `s < t`, then `KFrom E a t = a + t`. -/
theorem KFrom_eq_add_of_col_black (E : Nat → Int → Bool) (a : Int) :
    ∀ t : Nat, (∀ s, s < t → E s a = true) → KFrom E a t = a + (t : Int)
  | 0, _ => by simp [KFrom]
  | t + 1, hb => by
    have ih := KFrom_eq_add_of_col_black E a t (fun s hs => hb s (by omega))
    have hpos : KFrom E a t - (t : Int) = a := by omega
    have hlast : E t (KFrom E a t - t) = true := by rw [hpos]; exact hb t (by omega)
    show (if E t (KFrom E a t - t) then KFrom E a t + 1 else KFrom E a t) = a + ((t + 1 : Nat) : Int)
    rw [hlast, ih]
    simp <;> omega

/-- **Stationary Black-Column Shielding (`stationary_wall_of_col_black`):** if column `a` of `E` is
black at every step (`∀ t, E t a = true`) and `G` agrees with `E` on `x ≤ a` at `t = 0`, then `G`
agrees with `E` on `x ≤ a` at every time `t`. -/
theorem stationary_wall_of_col_black {E G : Nat → Int → Bool} (hE : IsR30Z E) (hG : IsR30Z G) {a : Int}
    (h0 : ∀ x, x ≤ a → G 0 x = E 0 x) (hb : ∀ t, E t a = true) (t : Nat) (x : Int) (hx : x ≤ a) :
    G t x = E t x := by
  have hK := KFrom_eq_add_of_col_black E a t (fun s _ => hb s)
  exact healing_bound_from hE hG h0 t x (by omega)

/-! ### `KFrom` Envelope Bounds, Perturbation Invariance, Zero-Recruitment Equivalence, and Boundary-Twin Sharpness -/

/-- **One-Step Growth Bounds for `KFrom` (`KFrom_succ_bounds`):** at every step `t : Nat`,
`KFrom E a t ≤ KFrom E a (t + 1)` and `KFrom E a (t + 1) ≤ KFrom E a t + 1`. -/
theorem KFrom_succ_bounds (E : Nat → Int → Bool) (a : Int) (t : Nat) :
    KFrom E a t ≤ KFrom E a (t + 1) ∧ KFrom E a (t + 1) ≤ KFrom E a t + 1 := by
  show KFrom E a t ≤ (if E t (KFrom E a t - t) then KFrom E a t + 1 else KFrom E a t) ∧
    (if E t (KFrom E a t - t) then KFrom E a t + 1 else KFrom E a t) ≤ KFrom E a t + 1
  cases E t (KFrom E a t - t) <;> simp <;> omega

/-- **Global Envelope Bounds for `KFrom` (`KFrom_bounds`):** for every background `E`, anchor
`a : Int`, and time `t : Nat`, `a ≤ KFrom E a t` and `KFrom E a t ≤ a + t`. -/
theorem KFrom_bounds (E : Nat → Int → Bool) (a : Int) :
    ∀ t : Nat, a ≤ KFrom E a t ∧ KFrom E a t ≤ a + (t : Int)
  | 0 => by simp [KFrom]
  | t + 1 => by
    have ih := KFrom_bounds E a t
    have hs := KFrom_succ_bounds E a t
    omega

/-- **Exact Perturbation Invariance of `KFrom` (`KFrom_eq_of_init_agree`):** if two Rule 30
evolutions `E` and `G` agree at `t = 0` on `x ≤ a`, then `KFrom G a t = KFrom E a t` at every
time `t : Nat`. -/
theorem KFrom_eq_of_init_agree {E G : Nat → Int → Bool} (hE : IsR30Z E) (hG : IsR30Z G) {a : Int}
    (h0 : ∀ x : Int, x ≤ a → G 0 x = E 0 x) :
    ∀ t : Nat, KFrom G a t = KFrom E a t
  | 0 => rfl
  | t + 1 => by
    have ih := KFrom_eq_of_init_agree hE hG h0 t
    have hcell : G t (KFrom E a t - t) = E t (KFrom E a t - t) :=
      healing_bound_from hE hG h0 t (KFrom E a t - t) (by omega)
    show (if G t (KFrom G a t - t) then KFrom G a t + 1 else KFrom G a t) =
      (if E t (KFrom E a t - t) then KFrom E a t + 1 else KFrom E a t)
    rw [ih, hcell]

/-- **Perturbation Invariance of `K` (`K_eq_of_init_agree`):** if two Rule 30 evolutions `E`
and `G` agree at `t = 0` on `x ≤ -1`, then `K G t = K E t` at every time `t : Nat`. -/
theorem K_eq_of_init_agree {E G : Nat → Int → Bool} (hE : IsR30Z E) (hG : IsR30Z G)
    (h0 : ∀ x : Int, x ≤ -1 → G 0 x = E 0 x) (t : Nat) :
    K G t = K E t := by
  rw [← KFrom_neg_one_eq_K G t, ← KFrom_neg_one_eq_K E t]
  exact KFrom_eq_of_init_agree hE hG h0 t

/-- **Exact Characterization of Zero Recruitment (`KFrom_eq_anchor_iff_all_white`):** at any
time `t : Nat`, `KFrom E a t = a` if and only if `∀ s < t, E s (a - s) = false`. -/
theorem KFrom_eq_anchor_iff_all_white (E : Nat → Int → Bool) (a : Int) :
    ∀ t : Nat, KFrom E a t = a ↔ (∀ s : Nat, s < t → E s (a - s) = false)
  | 0 => by simp [KFrom]
  | t + 1 => by
    have ih := KFrom_eq_anchor_iff_all_white E a t
    have hb := (KFrom_bounds E a t).1
    have hstep : KFrom E a (t + 1) = (if E t (KFrom E a t - t) then KFrom E a t + 1 else KFrom E a t) := rfl
    constructor
    · intro hKt1
      have hKt : KFrom E a t = a ∧ E t (a - t) = false := by
        rw [hstep] at hKt1
        cases hc : E t (KFrom E a t - t)
        · rw [hc] at hKt1; simp at hKt1
          refine ⟨hKt1, ?_⟩
          rwa [hKt1] at hc
        · rw [hc] at hKt1; simp at hKt1; omega
      intro s hs
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with hlt | rfl
      · exact (ih.mp hKt.1) s hlt
      · exact hKt.2
    · intro hall
      have hKt : KFrom E a t = a := ih.mpr (fun s hs => hall s (by omega))
      have hlast : E t (a - t) = false := hall t (Nat.lt_succ_self t)
      rw [hstep, hKt, hlast]
      rfl

/-- **Exact Sharpness of the Healing Bound for Boundary Twins
(`twin_flip_at_front_iff_KFrom_eq_anchor`):** if `E` and `G` are Rule 30 evolutions agreeing at
`t = 0` on `x ≤ a` and flipping at `a + 1` (`G 0 (a + 1) = !E 0 (a + 1)`), then at any time
`t : Nat`, `G t (a + 1 - t) = !E t (a + 1 - t)` if and only if `KFrom E a t = a`. -/
theorem twin_flip_at_front_iff_KFrom_eq_anchor {E G : Nat → Int → Bool}
    (hE : IsR30Z E) (hG : IsR30Z G) {a : Int}
    (h0 : ∀ x : Int, x ≤ a → G 0 x = E 0 x)
    (hflip : G 0 (a + 1) = !E 0 (a + 1)) (t : Nat) :
    G t (a + 1 - (t : Int)) = !E t (a + 1 - (t : Int)) ↔ KFrom E a t = a := by
  constructor
  · intro hft
    have hne : G t (a + 1 - (t : Int)) ≠ E t (a + 1 - (t : Int)) := by
      rw [hft]; cases E t (a + 1 - (t : Int)) <;> decide
    have hge := front_ge_from hE hG h0 t (a + 1 - (t : Int)) hne
    have hlo := (KFrom_bounds E a t).1
    omega
  · revert t
    intro t
    induction t with
    | zero =>
      intro _
      simpa using hflip
    | succ t ih =>
      intro hKt1
      have hall := (KFrom_eq_anchor_iff_all_white E a (t + 1)).mp hKt1
      have hKt : KFrom E a t = a :=
        (KFrom_eq_anchor_iff_all_white E a t).mpr (fun s hs => hall s (by omega))
      have hright := ih hKt
      have hwhite : E t (a - (t : Int)) = false := hall t (Nat.lt_succ_self t)
      have hleft_ag : G t (a - (t : Int) - 1) = E t (a - (t : Int) - 1) :=
        healing_bound_from hE hG h0 t (a - (t : Int) - 1) (by omega)
      have hcen_ag : G t (a - (t : Int)) = E t (a - (t : Int)) :=
        healing_bound_from hE hG h0 t (a - (t : Int)) (by omega)
      have hpos : a + 1 - ((t + 1 : Nat) : Int) = a - (t : Int) := by omega
      have hpos_r : a - (t : Int) + 1 = a + 1 - (t : Int) := by omega
      rw [hpos, hG t (a - (t : Int)), hE t (a - (t : Int)), hleft_ag, hcen_ag, hwhite, hpos_r, hright]
      cases E t (a - (t : Int) - 1) <;> cases E t (a + 1 - (t : Int)) <;> rfl

end Ruliology.CellularAutomata.Rule30HealingBound
