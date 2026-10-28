module

public import Ruliology.CellularAutomata.Rule30AgedLeftDiagonals
public import Ruliology.CellularAutomata.Rule30BlackRuns
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# Arbitrary blocks with sufficiently long white padding

For every Boolean list `u` containing a black cell, the single-seed Rule 30
center cannot eventually repeat `u ++ List.replicate q false` once
`paddingThreshold u.length <= q` (`not_eventually_padded_word`). The block's
length and arrangement are unrestricted, and the eventual-word predicate is
the official `Rule30StripCertificates.EventuallyWord`.

For `n = u.length`, the explicit bound is
```
L = 20*n
F = L + 2^(L+1)
N = (2^L - 1) + 2*2^L*2^L
W = N + 9*n
B = F + 11*n
K = n + B
Q = max W (B + 9*K).
```
Here `Physical.warmup n = W`, `Physical.bound n = B`, and
`paddingThreshold n = Q`. The bound is singly exponential in the block length.

The aged left-diagonal interval theorem supplies a physical white witness
after a long white-center warmup. At the last black phase of a candidate
period, that witness produces a nearby black cell. The following white tail
carries it to column 1 and regenerates the same alternating prefix at the
next period start. Cone agreement controls the early phases and the black
tail controls the remaining phases. Column 1 is then periodic from `T+2*P`,
contradicting `Rule30Jen.not_adjacent` with the center's assumed period.

`EarlyCases`, `Physical`, and `Capture` contain the local stripe, physical
comparison, and capture arguments. The proof uses the literal single-seed
cells and a global free reference evolution; it assumes no finite-width
certificate, conditional capture property, or whole-state return. Periods
without a sufficiently long white gap remain outside this theorem.

Sources: `Rule30AgedLeftDiagonals` supplies the aged interval bound;
`Rule30BlackRuns` supplies black persistence, shielding, and cone agreement.
The nearest-cell capture arguments and black-tick white-witness strategy
adapt @AIOvernight's Lean-verified submissions `R30-20261026-8cca17` and its
successor `R30-20261026-4d375d`, whose fixed-distance capture step is here
parametric. The arbitrary-block age bound, physical composition, and symbolic
stripe regeneration extend those capture arguments.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ArbitraryWhitePadding

namespace EarlyCases

open Ruliology.CellularAutomata
open Rule30Jen Rule30BlackRuns

/-- A stationary row survives on the ordinary shrinking radius-one cone. -/
theorem stationary_cone (f : Int → Bool)
    (hf : ∀ p, rule (f (p - 1)) (f p) (f (p + 1)) = f p)
    (a : Nat) (L U : Int)
    (hrow : ∀ p, L ≤ p → p ≤ U → cell a p = f p) :
    ∀ s : Nat, ∀ p : Int, L + s ≤ p → p + s ≤ U → cell (a + s) p = f p
  | 0, p, hlo, hhi => by simpa using hrow p (by omega) (by omega)
  | s + 1, p, hlo, hhi => by
    show rule (cell (a + s) (p - 1)) (cell (a + s) p)
      (cell (a + s) (p + 1)) = f p
    rw [stationary_cone f hf a L U hrow s (p - 1) (by omega) (by omega),
      stationary_cone f hf a L U hrow s p (by omega) (by omega),
      stationary_cone f hf a L U hrow s (p + 1) (by omega) (by omega)]
    exact hf p

/-- Odd columns black and even columns white form a stationary Rule 30 row. -/
def stripe (p : Int) : Bool := decide (p % 2 = 1)

theorem stripe_stationary (p : Int) :
    rule (stripe (p - 1)) (stripe p) (stripe (p + 1)) = stripe p := by
  by_cases hp : p % 2 = 0
  · have hl : (p - 1) % 2 = 1 := by omega
    have hr : (p + 1) % 2 = 1 := by omega
    simp [stripe, hp, hl, hr, rule]
  · have hp1 : p % 2 = 1 := by omega
    have hl : (p - 1) % 2 = 0 := by omega
    have hr : (p + 1) % 2 = 0 := by omega
    simp [stripe, hp1, hl, hr, rule]

/-- The white boundary protects a shrinking initially white positive prefix. -/
theorem white_prefix (a K : Nat) (M : Int)
    (hc : ∀ r, r < K → cell (a + r) 0 = false)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ M → cell a p = false) :
    ∀ s : Nat, s ≤ K → ∀ p : Int, 1 ≤ p → p + s ≤ M →
      cell (a + s) p = false
  | 0, _, p, hlo, hhi => by simpa using hrow p hlo (by omega)
  | s + 1, hs, p, hlo, hhi => by
    show rule (cell (a + s) (p - 1)) (cell (a + s) p)
      (cell (a + s) (p + 1)) = false
    have hl : cell (a + s) (p - 1) = false := by
      by_cases hp : p = 1
      · rw [show p - 1 = 0 by omega]
        exact hc s (by omega)
      · exact white_prefix a K M hc hrow s (by omega) (p - 1) (by omega) (by omega)
    rw [hl, white_prefix a K M hc hrow s (by omega) p hlo (by omega),
      white_prefix a K M hc hrow s (by omega) (p + 1) (by omega) (by omega)]
    rfl

/-- A black column 1 followed by 9n white center ticks gives a protected white witness. -/
theorem early_white_witness_at (n a j : Nat) (_hn : 1 ≤ n) (hj : j < n)
    (hc : ∀ r, r < 9 * n → cell (a + r) 0 = false)
    (hb : cell a 1 = true) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ 2 * n + 1 ∧ cell (a + 9 * n + j) p = false := by
  have hblack : ∀ r, r ≤ 9 * n → cell (a + r) 1 = true :=
    black_stays a (9 * n) hc hb
  have hshield := black_shield 1 n a (fun r hr => hblack r (by omega))
  have hrow : ∀ p : Int, 1 ≤ p → p ≤ 2 * (n : Int) + 1 →
      cell (a + 9 * n) p = stripe p := by
    intro p hlo hhi
    have hcast : (p.toNat : Int) = p := by omega
    by_cases hp : p % 2 = 0
    · let i := p.toNat / 2
      have hi1 : 1 ≤ i := by dsimp [i]; omega
      have hin : i ≤ n := by dsimp [i]; omega
      have heq : (1 : Int) + 2 * (i : Int) - 1 = p := by dsimp [i]; omega
      have hs := (hshield i hi1 hin).1
      rw [heq] at hs
      simpa [stripe, hp] using hs
    · have hp1 : p % 2 = 1 := by omega
      by_cases hone : p = 1
      · subst p
        simpa [stripe] using hblack (9 * n) (Nat.le_refl _)
      · let i := p.toNat / 2
        have hi1 : 1 ≤ i := by dsimp [i]; omega
        have hin : i ≤ n := by dsimp [i]; omega
        have heq : (1 : Int) + 2 * (i : Int) = p := by dsimp [i]; omega
        have hs := (hshield i hi1 hin).2
        rw [heq] at hs
        simpa [stripe, hp1] using hs
  let p := n + n % 2
  have hp1 : 1 ≤ p := by dsimp [p]; omega
  have hp2 : p ≤ 2 * n + 1 := by dsimp [p]; omega
  have heven : (p : Int) % 2 = 0 := by dsimp [p]; omega
  refine ⟨p, hp1, hp2, ?_⟩
  have hs := stationary_cone stripe stripe_stationary (a + 9 * n) 1
    (2 * (n : Int) + 1) hrow j p (by dsimp [p]; omega) (by dsimp [p]; omega)
  simpa [stripe, heven] using hs

theorem early_white_witness (n N t j : Nat) (hn : 1 ≤ n) (hj : j < n)
    (hwhite : ∀ r, r < N + 9 * n → cell (t + r) 0 = false)
    (hblack : cell (t + N) 1 = true) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ 2 * n + 1 ∧ cell (t + (N + 9 * n) + j) p = false := by
  have hc : ∀ r, r < 9 * n → cell (t + N + r) 0 = false := by
    intro r hr
    have h := hwhite (N + r) (by omega)
    simpa [Nat.add_assoc] using h
  simpa [Nat.add_assoc] using early_white_witness_at n (t + N) j hn hj hc hblack

/-- A distant all-white prefix leaves p=n white after the warmup and j<n arbitrary ticks. -/
theorem distant_white_witness_at (n a j : Nat) (_hn : 1 ≤ n) (hj : j < n)
    (hc : ∀ r, r < 9 * n → cell (a + r) 0 = false)
    (hprefix : ∀ p : Int, 1 ≤ p → p < 11 * (n : Int) → cell a p = false) :
    cell (a + 9 * n + j) n = false := by
  have hrow : ∀ p : Int, 1 ≤ p → p ≤ 2 * (n : Int) - 1 →
      cell (a + 9 * n) p = false := by
    intro p hlo hhi
    exact white_prefix a (9 * n) (11 * (n : Int) - 1) hc
      (fun q hq1 hq2 => hprefix q hq1 (by omega)) (9 * n) (Nat.le_refl _) p hlo (by omega)
  exact stationary_cone (fun _ => false) (fun _ => rfl) (a + 9 * n)
    1 (2 * (n : Int) - 1) hrow j n (by omega) (by omega)

theorem distant_white_witness (n N t j : Nat) (hn : 1 ≤ n) (hj : j < n)
    (hwhite : ∀ r, r < 9 * n → cell (t + N + r) 0 = false)
    (hprefix : ∀ p : Int, 1 ≤ p → p < 11 * (n : Int) → cell (t + N) p = false) :
    cell (t + (N + 9 * n) + j) n = false := by
  simpa [Nat.add_assoc] using distant_white_witness_at n (t + N) j hn hj hwhite hprefix

end EarlyCases

namespace Physical
open Ruliology.CellularAutomata Rule30Jen Rule30Realization

def freeRow (t : Nat) (D p : Int) : Bool :=
  if p < D then false else cell t p

def freeEvol (t : Nat) (D : Int) (k : Nat) (p : Int) : Bool :=
  evol (freeRow t D) k p

theorem free_succ (t : Nat) (D : Int) (k : Nat) (p l c r : Int)
    (hl : l = p-1) (hc : c = p) (hr : r = p+1) :
    freeEvol t D (k+1) p =
      rule (freeEvol t D k l) (freeEvol t D k c) (freeEvol t D k r) := by
  subst l c r
  rfl

theorem free_support (t : Nat) (D : Int) :
    ∀ (k : Nat) (p : Int), p < D-(k:Int) → freeEvol t D k p = false
  | 0, p, hp => by simp [freeEvol, evol, freeRow, show p < D by omega]
  | k+1, p, hp => by
    change rule (freeEvol t D k (p-1)) (freeEvol t D k p)
      (freeEvol t D k (p+1)) = false
    rw [free_support t D k (p-1) (by omega),
      free_support t D k p (by omega), free_support t D k (p+1) (by omega)]
    rfl

def front (t : Nat) (D : Int) (i k : Nat) : Bool :=
  freeEvol t D k (D-(k:Int)+(i:Int))

theorem front_recurrence (t : Nat) (D : Int) :
    Rule30AgedLeftDiagonals.Recurrence (front t D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    change freeEvol t D (k+1) (D-((k+1:Nat):Int)+0) =
      freeEvol t D k (D-(k:Int)+0)
    rw [free_succ t D k _ (D-(k:Int)-2) (D-(k:Int)-1) (D-(k:Int))
      (by omega) (by omega) (by omega), free_support t D k (D-(k:Int)-2) (by omega),
      free_support t D k (D-(k:Int)-1) (by omega)]
    simp [rule]
  · intro k
    change freeEvol t D (k+1) (D-((k+1:Nat):Int)+1) = _
    rw [free_succ t D k _ (D-(k:Int)-1) (D-(k:Int)) (D-(k:Int)+1)
      (by omega) (by omega) (by omega), free_support t D k (D-(k:Int)-1) (by omega)]
    simp [front, rule]
  · intro i k
    change freeEvol t D (k+1) (D-((k+1:Nat):Int)+((i+2:Nat):Int)) = _
    rw [free_succ t D k _ (D-(k:Int)+(i:Int))
      (D-(k:Int)+((i+1:Nat):Int)) (D-(k:Int)+((i+2:Nat):Int))
      (by omega) (by omega) (by omega)]
    rfl

theorem free_initial_agrees (t : Nat) (D : Int)
    (hrow : ∀ p : Int, 0 < p → p < D → cell t p = false)
    (p : Int) (hp : 0 < p) : freeEvol t D 0 p = cell t p := by
  unfold freeEvol evol freeRow
  split
  · exact (hrow p hp ‹p < D›).symm
  · rfl

/-- Equality on the whole positive half-line, retaining the ORIGINAL age. -/
theorem before_arrival (t N : Nat) (D : Int) (hD : (N:Int) < D)
    (hrow : ∀ p : Int, 0 < p → p < D → cell t p = false)
    (hw : ∀ k, k < N → cell (t+k) 0 = false) :
    ∀ k, k ≤ N → ∀ p : Int, 0 < p → freeEvol t D k p = cell (t+k) p := by
  intro k
  induction k with
  | zero => intro hk p hp; simpa using free_initial_agrees t D hrow p hp
  | succ k ih =>
    intro hk p hp
    have hl : freeEvol t D k (p-1) = cell (t+k) (p-1) := by
      by_cases he : p=1
      · subst p
        rw [show (1:Int)-1=0 by omega, free_support t D k 0 (by omega), hw k (by omega)]
      · exact ih (by omega) (p-1) (by omega)
    rw [show t+(k+1)=t+k+1 by omega]
    change rule (freeEvol t D k (p-1)) (freeEvol t D k p)
      (freeEvol t D k (p+1)) =
      rule (cell (t+k) (p-1)) (cell (t+k) p) (cell (t+k) (p+1))
    rw [hl, ih (by omega) p hp, ih (by omega) (p+1) (by omega)]

/-- After coupling at age N, arbitrary center changes propagate at speed one. -/
theorem after_cone (t N : Nat) (D : Int)
    (hN : ∀ p : Int, 0 < p → freeEvol t D N p = cell (t+N) p) :
    ∀ (s : Nat) (p : Int), (s:Int) < p → freeEvol t D (N+s) p = cell (t+N+s) p := by
  intro s
  induction s with
  | zero => intro p hp; simpa using hN p hp
  | succ s ih =>
    intro p hp
    rw [show N+(s+1)=N+s+1 by omega, show t+N+(s+1)=t+N+s+1 by omega]
    change rule (freeEvol t D (N+s) (p-1)) (freeEvol t D (N+s) p)
      (freeEvol t D (N+s) (p+1)) =
      rule (cell (t+N+s) (p-1)) (cell (t+N+s) p) (cell (t+N+s) (p+1))
    rw [ih (p-1) (by omega), ih p (by omega), ih (p+1) (by omega)]

def lower (n : Nat) : Nat := 20*n
def upper (n : Nat) : Nat := lower n + 2^(lower n+1)
def age (n : Nat) : Nat := Rule30AgedLeftDiagonals.resetAge (lower n)
def warmup (n : Nat) : Nat := age n + 9*n
def bound (n : Nat) : Nat := upper n + 11*n

/-- A genuinely aged free front supplies a bounded physical white witness. -/
theorem late_witness (t n j : Nat) (hn : 1 ≤ n) (hj : j < n) (D : Int)
    (hDlo : (age n:Int)+2 ≤ D) (hDhi : D ≤ (age n:Int)+11*n-1)
    (hrow : ∀ p : Int, 0 < p → p < D → cell t p = false)
    (hw : ∀ k, k < age n → cell (t+k) 0 = false) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ bound n ∧ cell (t+warmup n+j) p = false := by
  let N := age n
  let s := 9*n+j
  have hN : ∀ p : Int, 0 < p → freeEvol t D N p = cell (t+N) p :=
    before_arrival t N D (by dsimp [N]; omega) hrow hw N (by omega)
  have hlo : 1 ≤ lower n := by dsimp [lower]; omega
  have hage : Rule30AgedLeftDiagonals.resetAge (lower n) ≤ N+s :=
    Nat.le_add_right (age n) s
  obtain ⟨i, hi1, hi2, hiw⟩ := Rule30AgedLeftDiagonals.white_witness_after_reset
    (front_recurrence t D) (lower n) (N+s) hlo hage
  have hi2' : i ≤ upper n := by simpa only [upper] using hi2
  let p : Int := D-(N:Int)-(s:Int)+(i:Int)
  have hps : (s:Int) < p := by dsimp [p, s, N, lower] at *; omega
  have hpb : p ≤ (bound n:Int) := by
    dsimp [p, s, N, bound] at *
    omega
  have hp0 : 0 ≤ p := by omega
  refine ⟨p.toNat, by omega, by omega, ?_⟩
  have hcouple := after_cone t N D hN s p hps
  have hpos : D-((N+s:Nat):Int)+(i:Int)=p := by dsimp [p]; omega
  change freeEvol t D (N+s) (D-((N+s:Nat):Int)+(i:Int)) = false at hiw
  rw [hpos, hcouple] at hiw
  have ht : t+N+s=t+warmup n+j := by dsimp [N,s,warmup]; omega
  rw [ht] at hiw
  simpa [Int.toNat_of_nonneg hp0] using hiw

theorem white_back_pair (t : Nat) (p : Int)
    (hl : cell t (p-1) = false) (hz : cell (t+1) p = false) :
    cell t p = false ∧ cell t (p+1) = false := by
  change rule (cell t (p-1)) (cell t p) (cell t (p+1)) = false at hz
  rw [hl] at hz
  cases hc : cell t p <;> cases hr : cell t (p+1) <;> simp_all [rule]

/-- A white row prefix expands by one when traced backwards past a white driver. -/
theorem white_back_step (t m : Nat) (hm : 1 ≤ m) (hc : cell t 0 = false)
    (hz : ∀ p : Nat, 1 ≤ p → p ≤ m → cell (t+1) p = false) :
    ∀ p : Nat, 1 ≤ p → p ≤ m+1 → cell t p = false := by
  have pair : ∀ k : Nat, k < m →
      cell t ((k+1:Nat):Int) = false ∧ cell t ((k+2:Nat):Int) = false := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa using white_back_pair t 1 (by simpa using hc) (hz 1 (by omega) (by omega))
    | succ k ih =>
      intro hk
      have hl := (ih (by omega)).1
      have h := white_back_pair t ((k+2:Nat):Int)
        (by simpa only [show ((k+2:Nat):Int)-1=((k+1:Nat):Int) by omega] using hl)
        (hz (k+2) (by omega) (by omega))
      simpa only [show ((k+2:Nat):Int)+1=((k+1+2:Nat):Int) by omega] using h
  intro p hp hpm
  by_cases he : p=1
  · subst p
    exact (pair 0 (by omega)).1
  · have h := (pair (p-2) (by omega)).2
    simpa only [show p-2+2=p by omega] using h

theorem white_backwards (t N : Nat)
    (hw : ∀ k, k < N → cell (t+k) 0 = false) :
    ∀ m : Nat, 1 ≤ m →
      (∀ p : Nat, 1 ≤ p → p ≤ m → cell (t+N) p = false) →
      ∀ p : Nat, 1 ≤ p → p ≤ m+N → cell t p = false := by
  induction N with
  | zero => intro m hm hz p hp hpm; simpa using hz p hp (by omega)
  | succ N ih =>
    intro m hm hz p hp hpm
    have hz' : ∀ p : Nat, 1 ≤ p → p ≤ m → cell (t+N+1) p = false := by
      simpa only [show t+(N+1)=t+N+1 by omega] using hz
    have prev := white_back_step (t+N) m hm (hw N (by omega)) hz'
    exact ih (fun k hk => hw k (by omega)) (m+1) (by omega) prev p hp (by omega)

theorem original_white_prefix (t N : Nat)
    (hw : ∀ k, k < N → cell (t+k) 0 = false) (h1 : cell (t+N) 1 = false) :
    ∀ p : Int, 0 < p → p < (N:Int)+2 → cell t p = false := by
  have hh := white_backwards t N hw 1 (by omega)
    (fun p hp hp1 => by simpa [show p=1 by omega] using h1)
  intro p hp hpN
  have hn := hh p.toNat (by omega) (by omega)
  simpa [Int.toNat_of_nonneg (show 0 ≤ p by omega)] using hn

/-- Every one of the next n ticks has a bounded white cell after the warmup. -/
theorem physical_white_witness (t n j : Nat) (hn : 1 ≤ n) (hj : j < n)
    (hw : ∀ k, k < warmup n → cell (t+k) 0 = false) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ bound n ∧ cell (t+warmup n+j) p = false := by
  cases h1 : cell (t+age n) 1 with
  | true =>
    obtain ⟨p,hp1,hpB,hpw⟩ := EarlyCases.early_white_witness
      n (age n) t j hn hj hw h1
    refine ⟨p,hp1,?_,hpw⟩
    unfold bound
    omega
  | false =>
    have hwN : ∀ k, k < age n → cell (t+k) 0 = false :=
      fun k hk => hw k (by dsimp [warmup]; omega)
    exact late_witness t n j hn hj ((age n:Int)+2) (by omega) (by omega)
      (original_white_prefix t (age n) hwN h1) hwN

def BlockBound (u : List Bool) : Prop :=
  ∀ t, (∀ k, k < warmup u.length → cell (t+k) 0 = false) →
    (∀ j, j < u.length → cell (t+warmup u.length+j) 0 = u.getD j false) →
    ∀ j, j < u.length → u.getD j false = true →
      ∃ p : Nat, 1 ≤ p ∧ p ≤ bound u.length ∧ cell (t+warmup u.length+j) p = false

theorem block_bound (u : List Bool) (hu : 1 ≤ u.length) : BlockBound u := by
  intro t hw _ j hj _
  exact physical_white_witness t u.length j hu hj hw

end Physical

namespace Capture

open Ruliology.CellularAutomata
open Rule30Jen Rule30BlackRuns

/- Generic nearest-cell/white-run arguments extracted from the hash-pinned
public source. The literal-width black_step is generalized to arbitrary B.
Only the official kit and the independently frozen EarlyCases are imported. -/

/-! ### B. The jump law on actual cells -/

theorem cell_succ (t : Nat) (p : Int) :
    cell (t + 1) p = rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) := rfl

/-- Some column among `1 … m` is black at time `t`. -/
def Near (t m : Nat) : Prop := ∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = true

theorem near_min {t : Nat} : ∀ m, Near t m →
    ∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = true ∧ ∀ q : Nat, 1 ≤ q → q < p → cell t q = false
  | 0, ⟨p, hp1, hp0, _⟩ => by omega
  | m + 1, ⟨p, hp1, hpm, hb⟩ => by
    rcases Classical.em (Near t m) with hn | hn
    · obtain ⟨p', h1, h2, h3, h4⟩ := near_min m hn
      exact ⟨p', h1, Nat.le_succ_of_le h2, h3, h4⟩
    · refine ⟨p, hp1, hpm, hb, fun q hq1 hq2 => ?_⟩
      cases hc : cell t q with
      | false => rfl
      | true => exact (hn ⟨q, hq1, by omega, hc⟩).elim

/-- White tick, first black cell at column `p ≥ 3`: it moves to column `p - 1`. -/
theorem white_step_far (t p : Nat) (_h0 : cell t 0 = false) (hp : 3 ≤ p)
    (hw : ∀ q : Nat, 1 ≤ q → q < p → cell t q = false) (hb : cell t p = true) :
    cell (t + 1) ((p - 1 : Nat) : Int) = true := by
  rw [cell_succ]
  have e1 : ((p - 1 : Nat) : Int) - 1 = ((p - 2 : Nat) : Int) := by omega
  have e2 : ((p - 1 : Nat) : Int) + 1 = (p : Int) := by omega
  rw [e1, e2, hw (p-2) (by omega) (by omega), hw (p-1) (by omega) (by omega), hb]
  rfl

/-- White tick with a black cell in columns `1, 2`: column `1` is black next. -/
theorem white_step_near (t : Nat) (h0 : cell t 0 = false) (h : cell t 1 = true ∨ cell t 2 = true) :
    cell (t + 1) 1 = true := by
  rw [cell_succ]
  have e : (1 : Int) - 1 = 0 := by omega
  rw [e, h0]
  rcases h with h | h
  · rw [h]; rfl
  · rw [show (1 : Int) + 1 = 2 by omega, h]; cases cell t 1 <;> rfl

theorem near_white_step {t m : Nat} (h0 : cell t 0 = false) (hm : 2 ≤ m) (h : Near t m) :
    Near (t + 1) (m - 1) := by
  obtain ⟨p, hp1, hpm, hb, hmin⟩ := near_min m h
  by_cases hp3 : 3 ≤ p
  · refine ⟨p - 1, by omega, by omega, ?_⟩
    exact white_step_far t p h0 hp3 hmin hb
  · refine ⟨1, Nat.le_refl 1, by omega, white_step_near t h0 ?_⟩
    have hp : p = 1 ∨ p = 2 := by omega
    rcases hp with rfl | rfl
    · exact Or.inl hb
    · exact Or.inr hb

theorem near_white_run {t m : Nat} :
    ∀ n, n + 1 ≤ m → (∀ s, s < n → cell (t + s) 0 = false) → Near t m → Near (t + n) (m - n) := by
  intro n
  induction n with
  | zero => intro _ _ h; simpa using h
  | succ n ih =>
    intro hn hw h
    have h1 := ih (by omega) (fun s hs => hw s (by omega)) h
    have h2 := near_white_step (m := m - n) (hw n (by omega)) (by omega) h1
    rw [show t + (n + 1) = t + n + 1 by omega, show m - (n + 1) = m - n - 1 by omega]
    exact h2

theorem white_min {t : Nat} : ∀ m, (∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = false) →
    ∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = false ∧ ∀ q : Nat, 1 ≤ q → q < p → cell t q = true
  | 0, ⟨p, hp1, hp0, _⟩ => by omega
  | m + 1, ⟨p, hp1, hpm, hb⟩ => by
    rcases Classical.em (∃ p : Nat, 1 ≤ p ∧ p ≤ m ∧ cell t p = false) with hn | hn
    · obtain ⟨p', h1, h2, h3, h4⟩ := white_min m hn
      exact ⟨p', h1, Nat.le_succ_of_le h2, h3, h4⟩
    · refine ⟨p, hp1, hpm, hb, fun q hq1 hq2 => ?_⟩
      cases hc : cell t q with
      | true => rfl
      | false => exact (hn ⟨q, hq1, by omega, hc⟩).elim

/-- Black tick, columns `1 … B` not all black: the next row has a black cell within `(B + 1)`. -/
theorem black_step (t B : Nat) (h0 : cell t 0 = true)
    (h : ∃ p : Nat, 1 ≤ p ∧ p ≤ B ∧ cell t p = false) : Near (t + 1) (B + 1) := by
  obtain ⟨p, hp1, hp14, hpw, hmin⟩ := white_min B h
  have hleft : cell t ((p : Int) - 1) = true := by
    by_cases hp1' : p = 1
    · subst hp1'; simpa using h0
    · have : ((p : Int) - 1) = ((p - 1 : Nat) : Int) := by omega
      rw [this]; exact hmin (p - 1) (by omega) (by omega)
  have hstep : cell (t + 1) p = !cell t ((p : Int) + 1) := by
    rw [cell_succ, hleft, hpw]; cases cell t ((p : Int) + 1) <;> rfl
  cases hc : cell t ((p : Int) + 1) with
  | false => exact ⟨p, hp1, by omega, by rw [hstep, hc]; rfl⟩
  | true =>
    refine ⟨p + 1, by omega, by omega, ?_⟩
    rw [cell_succ, show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega,
      show ((p + 1 : Nat) : Int) = (p : Int) + 1 by omega, hpw, hc]
    cases cell t ((p : Int) + 1 + 1) <;> rfl

/-- A nearby black cell after a black tick reaches column 1 and remains black
through the closed endpoint of the following white center run. -/
theorem capture_after_black (t B L : Nat) (h0 : cell t 0 = true)
    (hwitness : ∃ p : Nat, 1 ≤ p ∧ p ≤ B ∧ cell t p = false)
    (hw : ∀ s, s < L → cell (t + 1 + s) 0 = false) (hBL : B ≤ L) :
    ∀ s, B ≤ s → s ≤ L → cell (t + 1 + s) 1 = true := by
  have hnear := black_step t B h0 hwitness
  have harr := near_white_run (t := t + 1) (m := B + 1) B (by omega)
    (fun s hs => hw s (by omega)) hnear
  obtain ⟨p, hp1, hpB, hp⟩ := harr
  have heq : p = 1 := by omega
  subst p
  have hblack : cell (t + 1 + B) 1 = true := hp
  have htail := black_stays (t + 1 + B) (L - B) (fun r hr => by
    have h := hw (B + r) (by omega)
    simpa [Nat.add_assoc] using h) hblack
  intro s hs hsL
  have h := htail (s - B) (by omega)
  rwa [show t + 1 + B + (s - B) = t + 1 + s by omega] at h

/-- The shield plus its black column-1 endpoint is the complete fixed stripe. -/
theorem stripe_after_black_run (a K : Nat)
    (hb : ∀ r, r < 9 * K → cell (a + r) 1 = true)
    (hend : cell (a + 9 * K) 1 = true) :
    ∀ p : Int, 1 ≤ p → p ≤ 2 * (K : Int) + 1 →
      cell (a + 9 * K) p = EarlyCases.stripe p := by
  have hshield := black_shield 1 K a hb
  intro p hlo hhi
  have hcast : (p.toNat : Int) = p := by omega
  by_cases hp : p % 2 = 0
  · let i := p.toNat / 2
    have hi1 : 1 ≤ i := by dsimp [i]; omega
    have hin : i ≤ K := by dsimp [i]; omega
    have heq : (1 : Int) + 2 * (i : Int) - 1 = p := by dsimp [i]; omega
    have hs := (hshield i hi1 hin).1
    rw [heq] at hs
    simpa [EarlyCases.stripe, hp] using hs
  · have hp1 : p % 2 = 1 := by omega
    by_cases hone : p = 1
    · subst p
      simpa [EarlyCases.stripe] using hend
    · let i := p.toNat / 2
      have hi1 : 1 ≤ i := by dsimp [i]; omega
      have hin : i ≤ K := by dsimp [i]; omega
      have heq : (1 : Int) + 2 * (i : Int) = p := by dsimp [i]; omega
      have hs := (hshield i hi1 hin).2
      rw [heq] at hs
      simpa [EarlyCases.stripe, hp1] using hs

/-- A long enough white tail both captures a black column 1 and regenerates
the same complete alternating prefix at the endpoint. -/
theorem tail_and_stripe (t B K L : Nat) (h0 : cell t 0 = true)
    (hwitness : ∃ p : Nat, 1 ≤ p ∧ p ≤ B ∧ cell t p = false)
    (hw : ∀ s, s < L → cell (t + 1 + s) 0 = false)
    (hL : B + 9 * K ≤ L) :
    (∀ s, B ≤ s → s ≤ L → cell (t + 1 + s) 1 = true) ∧
    (∀ p : Int, 1 ≤ p → p ≤ 2 * (K : Int) + 1 →
      cell (t + 1 + L) p = EarlyCases.stripe p) := by
  have htail := capture_after_black t B L h0 hwitness hw (by omega)
  refine ⟨htail, ?_⟩
  have hstripe := stripe_after_black_run (t + 1 + (L - 9 * K)) K (fun r hr => by
    have h := htail (L - 9 * K + r) (by omega) (by omega)
    simpa [Nat.add_assoc] using h) (by
    rw [show t + 1 + (L - 9 * K) + 9 * K = t + 1 + L by omega]
    exact htail L (by omega) (Nat.le_refl _))
  rwa [show t + 1 + (L - 9 * K) + 9 * K = t + 1 + L by omega] at hstripe

end Capture

/-! ### Excluding every black-containing block with sufficient white padding -/
open Ruliology.CellularAutomata Rule30Jen Rule30BlackRuns
open Rule30StripCertificates Physical

def stripeWidth (n : Nat) : Nat := n + bound n
def paddingThreshold (n : Nat) : Nat :=
  max (warmup n) (bound n + 9*stripeWidth n)

theorem exists_last (u : List Bool) : ∀ m, m ≤ u.length →
    (∃ j, j < m ∧ u.getD j false = true) →
    ∃ j, j < m ∧ u.getD j false = true ∧
      ∀ j', j < j' → j' < m → u.getD j' false = false
  | 0, _, ⟨j,hj,_⟩ => by omega
  | m+1, hm, ⟨j,hj,hb⟩ => by
    cases hc : u.getD m false with
    | true => exact ⟨m,by omega,hc,fun j' h1 h2 => by omega⟩
    | false =>
      have hjm : j < m := by
        by_cases he : j=m
        · subst j; rw [hc] at hb; cases hb
        · omega
      obtain ⟨j0,h1,h2,h3⟩ := exists_last u m (by omega) ⟨j,hjm,hb⟩
      refine ⟨j0,by omega,h2,fun j' hj1 hj2 => ?_⟩
      by_cases hlt : j' < m
      · exact h3 j' hj1 hlt
      · have he : j'=m := by omega
        subst j'; exact hc

/-- Phasewise agreement from period number two gives the exact eventual onset T+2P. -/
theorem phase_periodic (f : Nat → Bool) (T P : Nat) (hP : 0 < P)
    (hphase : ∀ m, 2 ≤ m → ∀ s, s < P →
      f (T+(m+1)*P+s) = f (T+m*P+s)) :
    ∀ t, T+2*P ≤ t → f (t+P) = f t := by
  intro t ht
  let k := (t-(T+2*P))/P
  let s := (t-(T+2*P))%P
  have hs : s < P := Nat.mod_lt _ hP
  have hd : s+P*k=t-(T+2*P) := Nat.mod_add_div _ _
  have htime : t=T+(k+2)*P+s := by
    rw [Nat.add_mul]
    rw [Nat.mul_comm P k] at hd
    omega
  have hnext : t+P=T+((k+2)+1)*P+s := by
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  rw [hnext,htime]
  exact hphase (k+2) (Nat.le_add_left 2 k) s hs

/-- An arbitrary black-containing block is excluded with the explicit white padding bound. -/
theorem not_eventually_padded_word (u : List Bool) (q : Nat)
    (hblack : ∃ j, j < u.length ∧ u.getD j false = true)
    (hq : paddingThreshold u.length ≤ q) :
    ¬ EventuallyWord (u ++ List.replicate q false) := by
  intro hevent
  obtain ⟨T,hT⟩ := hevent
  let n := u.length
  let B := bound n
  let W := warmup n
  let K := n+B
  let P := n+q
  let w := u ++ List.replicate q false
  have hn : 1 ≤ n := by obtain ⟨j,hj,_⟩ := hblack; dsimp [n]; omega
  have hW : W ≤ q := Nat.le_trans (Nat.le_max_left _ _) hq
  have hqB : B+9*K ≤ q := Nat.le_trans (Nat.le_max_right _ _) hq
  have hP : 0 < P := by dsimp [P]; omega
  have hwlen : w.length=P := by simp [w,P,n]
  change ∀ t, T ≤ t → cell t 0 = w.getD ((t-T)%w.length) false at hT
  rw [hwlen] at hT
  have hper : ∀ t, T ≤ t → cell (t+P) 0 = cell t 0 := by
    intro t ht
    rw [hT (t+P) (by omega),hT t ht,
      show t+P-T=(t-T)+P by omega,Nat.add_mod_right]
  have hblock : ∀ m s, s < P → cell (T+m*P+s) 0 = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega),show T+m*P+s-T=s+m*P by omega,
      Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hs]
  have hgetu : ∀ j, j < n → w.getD j false = u.getD j false := by
    intro j hj
    simp only [w,List.getD_eq_getElem?_getD,List.getElem?_append_left hj]
  have hgetw : ∀ j, n ≤ j → j < P → w.getD j false = false := by
    intro j hj1 hj2
    rw [show w=u++List.replicate q false by rfl,List.getD_eq_getElem?_getD,
      List.getElem?_append_right hj1,List.getElem?_replicate,
      ite_eq_left (by dsimp [P,n] at *; omega)]
    rfl
  obtain ⟨ell,hell,hbell,hlast⟩ := exists_last u n (Nat.le_refl _) hblack
  have htailwhite : ∀ m s, ell < s → s < P → cell (T+m*P+s) 0 = false := by
    intro m s hs hsp
    rw [hblock m s hsp]
    by_cases hsn : s < n
    · rw [hgetu s hsn]
      exact hlast s hs hsn
    · exact hgetw s (by omega) hsp
  have hnext : ∀ m, T+(m+1)*P=T+m*P+P := by
    intro m
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  have hcapture : ∀ m, 1 ≤ m →
      (∀ s, K ≤ s → s ≤ P → cell (T+m*P+s) 1 = true) ∧
      (∀ p : Int, 1 ≤ p → p ≤ 2*(K:Int)+1 →
        cell (T+(m+1)*P) p = EarlyCases.stripe p) := by
    intro m hm
    have hprev : (m-1)*P+P=m*P := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    let t0 := T+(m-1)*P+(P-W)
    have hWP : W ≤ P := by dsimp [P]; omega
    have ht0 : t0+W=T+m*P := by dsimp [t0]; omega
    have hwhite : ∀ r, r < warmup n → cell (t0+r) 0 = false := by
      intro r hr
      have hphase : n ≤ P-W+r := by dsimp [P,W] at *; omega
      have hphaseP : P-W+r < P := by change r < W at hr; omega
      rw [show t0+r=T+(m-1)*P+(P-W+r) by dsimp [t0]; omega,
        hblock (m-1) (P-W+r) hphaseP,hgetw _ hphase hphaseP]
    obtain ⟨p,hp1,hpB,hpw⟩ := physical_white_witness t0 n ell hn hell hwhite
    have hwitness : ∃ p : Nat, 1 ≤ p ∧ p ≤ B ∧ cell (T+m*P+ell) p = false := by
      refine ⟨p,hp1,hpB,?_⟩
      change cell (t0+W+ell) p = false at hpw
      simpa only [ht0] using hpw
    have hblackell : cell (T+m*P+ell) 0 = true := by
      rw [hblock m ell (by dsimp [P]; omega),hgetu ell hell]
      exact hbell
    let L := P-ell-1
    have hL : B+9*K ≤ L := by dsimp [L,P,K] at *; omega
    have hwhiteL : ∀ s, s < L → cell (T+m*P+ell+1+s) 0 = false := by
      intro s hs
      have hsp : ell+1+s < P := by dsimp [L] at hs; omega
      have hh := htailwhite m (ell+1+s) (by omega) hsp
      simpa only [show T+m*P+(ell+1+s)=T+m*P+ell+1+s by omega] using hh
    obtain ⟨htail,hstripe⟩ := Capture.tail_and_stripe
      (T+m*P+ell) B K L hblackell hwitness hwhiteL hL
    constructor
    · intro s hs hsP
      have hBs : B ≤ s-ell-1 := by dsimp [K] at hs; omega
      have hsL : s-ell-1 ≤ L := by dsimp [L]; omega
      have hh := htail (s-ell-1) hBs hsL
      have he : T+m*P+ell+1+(s-ell-1)=T+m*P+s := by dsimp [K] at hs; omega
      simpa only [he] using hh
    · intro p hp1 hpK
      have he : T+m*P+ell+1+L=T+(m+1)*P := by
        rw [hnext]
        dsimp [L]
        dsimp [P] at *
        omega
      simpa only [he] using hstripe p hp1 hpK
  have hstripe : ∀ m, 2 ≤ m → ∀ p : Int, 1 ≤ p → p ≤ 2*(K:Int)+1 →
      cell (T+m*P) p = EarlyCases.stripe p := by
    intro m hm p hp1 hpK
    have hh := (hcapture (m-1) (by omega)).2 p hp1 hpK
    simpa only [show m-1+1=m by omega] using hh
  have hphase : ∀ m, 2 ≤ m → ∀ s, s < P →
      cell (T+(m+1)*P+s) 1 = cell (T+m*P+s) 1 := by
    intro m hm s hs
    by_cases hsK : s < K
    · have hdriver : ∀ r, cell (T+m*P+r) 0 = cell (T+(m+1)*P+r) 0 := by
        intro r
        have hh := hper (T+m*P+r) (by omega)
        rw [hnext]
        simpa only [show T+m*P+P+r=T+m*P+r+P by omega] using hh.symm
      have hrow : ∀ p : Int, 1 ≤ p → p ≤ (2*K+1:Nat) →
          cell (T+m*P) p = cell (T+(m+1)*P) p := by
        intro p hp1 hpK
        rw [hstripe m hm p hp1 (by omega),hstripe (m+1) (by omega) p hp1 (by omega)]
      exact (cone_agree (T+m*P) (T+(m+1)*P) (2*K+1) hdriver hrow
        s 1 (by omega) (by omega)).symm
    · rw [(hcapture m (by omega)).1 s (by omega) (by omega),
        (hcapture (m+1) (by omega)).1 s (by omega) (by omega)]
  have hcol := phase_periodic (fun t => cell t 1) T P hP hphase
  exact not_adjacent 0 ⟨T,P,hP,hper⟩ ⟨T+2*P,P,hP,hcol⟩


end Ruliology.CellularAutomata.Rule30ArbitraryWhitePadding
