module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Certificates.AlternatingEmptyWall
public import Ruliology.CellularAutomata.Rule30SpacingRenormalization

/-!
# Nonabsorption of the empty right half under an alternating boundary

The literal four-slot word `[true, false, true, false]` does not satisfy
`Rule30Ether.Absorption` for any list of its genuine alignments: the empty
right half at phase zero never enters any such ether-and-wall family.

A kernel-checked forward invariant gives black gate gaps three or five
after cycle 146. The symbolic argument excludes eventual gate period two;
an aligned ether-and-wall entry would impose that period. The three named
least-period-four absorption cases and Prize Problem 1 remain open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EmptyAlternating


open Rule30DrivenPrefix Rule30Certificates.AlternatingEmptyWall
open Rule30PeriodTwoSideways Rule30SpacingRenormalization

theorem wall_trim (a : Nat) : wall (a % 2^18)=wall a := by
  unfold wall
  rw [Nat.mod_mod_of_dvd a (by decide : 65536 ∣ 2^18)]

/-- The two unseen right cells range over every possibility in `good_all`. -/
theorem wall_step (a : Nat) (ha : wall a=true) : Observe a ∧ wall (double a)=true := by
  have ht : wall (a % 262144)=true := by
    change wall (a % 2^18)=true
    rw [wall_trim]
    exact ha
  have hg := good_all (a%262144) (Nat.mod_lt _ (by decide)) ht
  refine ⟨(observe_trim a).mp hg.1,?_⟩
  have he : wall (double (a % 2^18))=wall (double a) := by
    unfold wall
    rw [← double_prefix a 16]
  rw [he] at hg
  exact hg.2

theorem white_wall : ∀ n, wall (white (146+n))=true
  | 0 => entry
  | n+1 => by
      rw [show 146+(n+1)=(146+n)+1 by omega,white]
      exact (wall_step _ (white_wall n)).2

def gate (r : Nat) : Bool := u empty (146+r)

/-- Every six-cycle window obeys the exact gate restrictions, at all later times. -/
theorem empty_windows (r : Nat) : Window gate r := by
  have ho := (wall_step _ (white_wall r)).1
  simpa only [Observe,Window,gate,Nat.zero_add,Nat.add_zero,iterate_white,white_gate,Nat.add_assoc] using ho

/-- Black gate positions are never separated by one or two cycles. -/
theorem empty_spaced : Spaced gate := by
  intro r
  exact ⟨(empty_windows r).1,(empty_windows r).2.1⟩

/-- After a black observation, the next black observation is exactly three or five cycles later. -/
theorem empty_next_gap (r : Nat) (hr : gate r=true) :
    (gate (r+3)=true ∧ gate (r+4)=false ∧ gate (r+5)=false) ∨
    (gate (r+3)=false ∧ gate (r+4)=false ∧ gate (r+5)=true) :=
  (empty_windows r).2.2.1 hr

theorem empty_no_six_white (r : Nat) :
    (gate r || gate (r+1) || gate (r+2) || gate (r+3) || gate (r+4) || gate (r+5))=true :=
  (empty_windows r).2.2.2

theorem empty_black_after (r : Nat) : ∃ s, r≤s ∧ gate s=true := by
  have h := empty_no_six_white r
  simp only [Bool.or_eq_true] at h
  rcases h with ((((ha | hb) | hc) | hd) | he) | hf
  · exact ⟨r,Nat.le_refl _,ha⟩
  · exact ⟨r+1,by omega,hb⟩
  · exact ⟨r+2,by omega,hc⟩
  · exact ⟨r+3,by omega,hd⟩
  · exact ⟨r+4,by omega,he⟩
  · exact ⟨r+5,by omega,hf⟩

open Ruliology.CellularAutomata
open Rule30Ether Rule30PeriodTwoCoupled Rule30PeriodTwoSideways

/-- Ether.wordAt uses a four-slot period, irrespective of the list length. -/
def wAlt4 : List Bool := [true, false, true, false]

theorem wordAt_alt (t : Nat) : wordAt wAlt4 t = altCol t := by
  have h : t % 4 < 4 := Nat.mod_lt _ (by decide)
  have hm : t % 2 = (t % 4) % 2 := by omega
  unfold wordAt wAlt4 altCol
  rw [hm]
  have ht : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases ht with ht | ht | ht | ht <;> simp [ht]

private theorem aligned_alt_small :
    ∀ j, j < 7 → ∀ s, s < 4 → aligned wAlt4 j s = true → j = 3 := by decide

theorem aligned_alt_column (j s : Nat) (h : aligned wAlt4 j s = true) :
    j % 7 = 3 := by
  apply aligned_alt_small (j % 7) (Nat.mod_lt _ (by decide))
    (s % 4) (Nat.mod_lt _ (by decide))
  simpa only [aligned, ether, Nat.add_mod, Nat.mod_mod] using h

/-- The gate-cycle period two would repeat a late black gate at distance two,
contradicting the already certified spacing. -/
theorem empty_not_eventually_two :
    ¬ ∃ T, ∀ r, T ≤ r → u empty (r + 2) = u empty r := by
  rintro ⟨T, hp⟩
  obtain ⟨s, hs, hb⟩ := Rule30EmptyAlternating.empty_black_after T
  have hsp := (Rule30EmptyAlternating.empty_spaced s).2
  have hb2 : Rule30EmptyAlternating.gate (s + 2) = true := by
    unfold Rule30EmptyAlternating.gate at hb ⊢
    rw [show 146 + (s + 2) = (146 + s) + 2 by omega, hp _ (by omega)]
    exact hb
  rw [hb, hb2] at hsp
  contradiction

/-- A positive-width ether prefix at entry protects physical column one.
Its four physical time steps are two gate cycles. -/
theorem gate_two_of_family (R : Nat → Bool) (j s t1 : Nat)
    (h0 : ∀ t, t1 ≤ t → drv altCol R t 0 = ether j (t + s))
    (hj : j % 7 = 3) (hf : InFamily (drv altCol R) j s t1) :
    ∀ r, t1 ≤ r → u R (r + 2) = u R r := by
  obtain ⟨k, hk, he, hw⟩ := hf
  have hk1 : 1 ≤ k := by omega
  have inv := trap_invariant (drv_isR30 altCol R) j s k t1 hk h0 he hw
  have col : ∀ t, t1 ≤ t → drv altCol R t 1 = ether (j + 1) (t + s) := by
    intro t ht
    have h := (inv (t - t1)).1 1 hk1
    simpa only [show t1 + (t - t1) = t by omega] using h
  intro r hr
  unfold u
  rw [col _ (by omega), col _ (by omega),
    show 2 * (r + 2) + 1 + s = (2 * r + 1 + s) + 4 by omega, ether_period]

theorem empty_no_aligned_family (j s t1 : Nat)
    (hal : aligned wAlt4 j s = true) :
    ¬ InFamily (drv altCol empty) j s t1 := by
  intro hf
  apply empty_not_eventually_two
  refine ⟨t1, gate_two_of_family empty j s t1 ?_ (aligned_alt_column j s hal) hf⟩
  intro t _
  rw [drv_col0, aligned_spec hal, wordAt_alt]

/-- The empty initial right half at phase zero refutes absorption for every
list whose entries are genuine alignments of the literal alternating word. -/
theorem not_absorption_alt (A : List (Nat × Nat))
    (hal : ∀ a ∈ A, aligned wAlt4 a.1 a.2 = true) :
    ¬ Absorption wAlt4 A := by
  intro hA
  obtain ⟨⟨j, s⟩, ha, t1, hf⟩ := hA empty 0 (fun _ _ => rfl) 0
  have hc : (fun t => wordAt wAlt4 (t + 0)) = altCol := by
    funext t
    simpa only [Nat.add_zero] using wordAt_alt t
  rw [hc, Nat.add_zero] at hf
  exact empty_no_aligned_family j s t1 (hal (j, s) ha) hf

end Ruliology.CellularAutomata.Rule30EmptyAlternating
