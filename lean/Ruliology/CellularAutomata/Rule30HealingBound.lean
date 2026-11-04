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

end Ruliology.CellularAutomata.Rule30HealingBound
