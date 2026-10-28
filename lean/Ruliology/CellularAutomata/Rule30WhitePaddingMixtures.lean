module

public import Ruliology.CellularAutomata.Rule30ArbitraryWhitePadding
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# Finite mixtures of padded blocks with a pair of entry gaps

For any positive block-length bound `N` and any positive number `r` of blocks,
`not_eventually_word_seed_pair` excludes the official eventual repetition of
`word u q r`. This word concatenates the first `r` blocks `u i`, each followed
by `q i` white cells. Every block must contain a black cell and have length at
most `N`; their arrangement and the number of blocks are unrestricted.

Every gap must satisfy `q i >= 19*N+10`. Two designated cyclically adjacent
gaps provide entry around block zero. With
```
F(N) = 20*N + 2^(20*N+1)
W(N) = (2^(20*N) - 1) + 2*2^(20*N)*2^(20*N) + 9*N
B(N) = F(N) + 11*N,
```
the additional requirements are `q (r-1) >= W(N)` and
`q 0 >= B(N) + 9*(2*N+1)`. Here `W` and `B` are the imported physical
warmup and witness bounds. When `r=1`, both conditions apply to the same gap.
The final theorem has no initial stripe or custom repetition premise.

The incoming alternating stripe supplies a protected white witness during
each bounded block. Its last black phase then captures column 1, and linear
white padding regenerates the stripe at the segment endpoint. A finite cone
argument determines the column-1 response without assumptions on later
blocks. The two larger gaps derive initial stripe entry at `T+2*P`; segment
offsets and quotient/remainder then give every-time periodicity of columns
0 and 1, contradicting the pinned `Rule30Jen.not_adjacent` theorem.

`Maintenance` proves the conditional stripe invariant and response agreement.
`Schedule` derives stripe entry and excludes the exact repeated segment
schedule. The root `word` adapter uses the official
`Rule30StripCertificates.EventuallyWord`, with no replacement definition.
Linear gaps alone are not proved to supply entry, and periods outside these
block and gap hypotheses remain outside the theorem.

Sources: `Rule30ArbitraryWhitePadding` supplies the symbolic physical witness
and capture lemmas, and records the nearest-cell capture antecedents from
@AIOvernight's Lean-verified `R30-20261026-8cca17` and `R30-20261026-4d375d`.
This module adds linear stripe maintenance and the finite-mixture schedule
and word interfaces.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30WhitePaddingMixtures

namespace Maintenance
open Ruliology.CellularAutomata Rule30Jen

def horizon (N : Nat) : Nat := 2*N+1
def padding (N : Nat) : Nat := (N+1)+9*horizon N
def StripeAt (N t : Nat) : Prop :=
  ∀ p : Int, 1 ≤ p → p ≤ 2*(horizon N:Int)+1 →
    cell t p = Rule30ArbitraryWhitePadding.EarlyCases.stripe p

/-- The finite block followed by q white driver ticks. Nothing is assumed afterwards. -/
def Drives (t : Nat) (u : List Bool) (q : Nat) : Prop :=
  ∀ s, s < u.length+q → cell (t+s) 0 = u.getD s false

theorem padding_eq (N : Nat) : padding N = 19*N+10 := by
  unfold padding horizon
  omega

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

/-- The even middle cell of the incoming stripe survives any fewer than N ticks. -/
theorem short_white_witness (N t ell : Nat) (_hN : 1 ≤ N) (hell : ell < N)
    (hstripe : StripeAt N t) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ N+1 ∧ cell (t+ell) p = false := by
  let p := N+N%2
  have hp1 : 1 ≤ p := by dsimp [p]; omega
  have hpB : p ≤ N+1 := by dsimp [p]; omega
  have hpl : (1:Int)+ell ≤ (p:Int) := by dsimp [p]; omega
  have hpu : (p:Int)+ell ≤ 2*(horizon N:Int)+1 := by
    dsimp [p,horizon]
    omega
  have hh := Rule30ArbitraryWhitePadding.EarlyCases.stationary_cone Rule30ArbitraryWhitePadding.EarlyCases.stripe
    Rule30ArbitraryWhitePadding.EarlyCases.stripe_stationary t 1 (2*(horizon N:Int)+1)
    hstripe ell p hpl hpu
  have heven : (p:Int)%2=0 := by dsimp [p]; omega
  refine ⟨p,hp1,hpB,?_⟩
  simpa [Rule30ArbitraryWhitePadding.EarlyCases.stripe,heven] using hh

/-- A black-containing block of length at most N preserves the stripe after linear padding. -/
theorem maintain (N t : Nat) (u : List Bool) (q : Nat)
    (hN : 1 ≤ N) (hlen : u.length ≤ N)
    (hblack : ∃ ell, ell < u.length ∧ u.getD ell false = true)
    (hq : padding N ≤ q) (hstripe : StripeAt N t) (hdrive : Drives t u q) :
    (∀ s, horizon N ≤ s → s ≤ u.length+q → cell (t+s) 1 = true) ∧
    StripeAt N (t+u.length+q) := by
  obtain ⟨ell,hell,hbell,hlast⟩ := exists_last u u.length (Nat.le_refl _) hblack
  have hwitness := short_white_witness N t ell hN (by omega) hstripe
  have h0 : cell (t+ell) 0 = true := by
    rw [hdrive ell (by omega)]
    exact hbell
  let L := u.length+q-ell-1
  have hL : (N+1)+9*horizon N ≤ L := by
    change (N+1)+9*horizon N ≤ q at hq
    dsimp [L]
    omega
  have hw : ∀ s, s < L → cell (t+ell+1+s) 0 = false := by
    intro s hs
    have hsp : ell+1+s < u.length+q := by dsimp [L] at hs; omega
    rw [show t+ell+1+s=t+(ell+1+s) by omega,hdrive (ell+1+s) hsp]
    by_cases hu : ell+1+s < u.length
    · exact hlast (ell+1+s) (by omega) hu
    · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)]
      rfl
  obtain ⟨htail,hregen⟩ := Rule30ArbitraryWhitePadding.Capture.tail_and_stripe
    (t+ell) (N+1) (horizon N) L h0 hwitness hw hL
  constructor
  · intro s hs hsP
    have hB : N+1 ≤ s-ell-1 := by dsimp [horizon] at hs; omega
    have hsL : s-ell-1 ≤ L := by dsimp [L]; omega
    have hh := htail (s-ell-1) hB hsL
    have he : t+ell+1+(s-ell-1)=t+s := by dsimp [horizon] at hs; omega
    simpa only [he] using hh
  · intro p hp1 hpK
    have he : t+ell+1+L=t+u.length+q := by dsimp [L]; omega
    simpa only [he] using hregen p hp1 hpK

/-- Boundary agreement is needed only before the time horizon, not for the entire future. -/
theorem finite_cone_agree (t0 t1 M H : Nat)
    (hdrv : ∀ r, r < H → cell (t0+r) 0 = cell (t1+r) 0)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ M → cell t0 p = cell t1 p) :
    ∀ s : Nat, s ≤ H → ∀ p : Int, 1 ≤ p → p+s ≤ M →
      cell (t0+s) p = cell (t1+s) p
  | 0, _, p, h1, h2 => by simpa using hrow p h1 (by omega)
  | s+1, hs, p, h1, h2 => by
    show rule (cell (t0+s) (p-1)) (cell (t0+s) p) (cell (t0+s) (p+1)) =
      rule (cell (t1+s) (p-1)) (cell (t1+s) p) (cell (t1+s) (p+1))
    have hl : cell (t0+s) (p-1) = cell (t1+s) (p-1) := by
      by_cases hp : p=1
      · rw [show p-1=0 by omega]
        exact hdrv s (by omega)
      · exact finite_cone_agree t0 t1 M H hdrv hrow s (by omega)
          (p-1) (by omega) (by omega)
    rw [hl,finite_cone_agree t0 t1 M H hdrv hrow s (by omega) p h1 (by omega),
      finite_cone_agree t0 t1 M H hdrv hrow s (by omega) (p+1) (by omega) (by omega)]

/-- The complete response to the same block agrees, even with different admissible padding.
The equality includes the shorter segment's endpoint. Future blocks are unrestricted. -/
theorem response_agree (N t0 t1 : Nat) (u : List Bool) (q0 q1 : Nat)
    (hN : 1 ≤ N) (hlen : u.length ≤ N)
    (hblack : ∃ ell, ell < u.length ∧ u.getD ell false = true)
    (hq0 : padding N ≤ q0) (hq1 : padding N ≤ q1)
    (hs0 : StripeAt N t0) (hs1 : StripeAt N t1)
    (hd0 : Drives t0 u q0) (hd1 : Drives t1 u q1) :
    ∀ s, s ≤ u.length+q0 → s ≤ u.length+q1 →
      cell (t0+s) 1 = cell (t1+s) 1 := by
  have hb0 := (maintain N t0 u q0 hN hlen hblack hq0 hs0 hd0).1
  have hb1 := (maintain N t1 u q1 hN hlen hblack hq1 hs1 hd1).1
  intro s hsP0 hsP1
  by_cases hsK : s < horizon N
  · have hdrv : ∀ r, r < s → cell (t0+r) 0 = cell (t1+r) 0 := by
      intro r hr
      rw [hd0 r (by omega),hd1 r (by omega)]
    have hrow : ∀ p : Int, 1 ≤ p → p ≤ (2*horizon N+1:Nat) →
        cell t0 p = cell t1 p := by
      intro p hp1 hpK
      rw [hs0 p hp1 (by omega),hs1 p hp1 (by omega)]
    exact finite_cone_agree t0 t1 (2*horizon N+1) s hdrv hrow s (by omega)
      1 (by omega) (by omega)
  · rw [hb0 s (by omega) hsP0,hb1 s (by omega) hsP1]

end Maintenance

namespace Schedule
open Ruliology.CellularAutomata Rule30Jen Rule30StripCertificates
open Maintenance Rule30ArbitraryWhitePadding.Physical

def offset (u : Nat → List Bool) (q : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => offset u q i + (u i).length + q i

def RepeatsSegments (T r : Nat) (u : Nat → List Bool) (q : Nat → Nat) : Prop :=
  ∀ m i, i < r → Drives (T + m * offset u q r + offset u q i) (u i) (q i)

theorem offset_mono (u : Nat → List Bool) (q : Nat → Nat) :
    ∀ i j, i ≤ j → offset u q i ≤ offset u q j := by
  intro i j
  induction j generalizing i with
  | zero =>
    intro hij
    have hi : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    intro hij
    by_cases h : i ≤ j
    · have hm := ih i h
      simp only [offset]
      omega
    · have he : i = j + 1 := by omega
      subst i
      exact Nat.le_refl _

theorem offset_cover (u : Nat → List Bool) (q : Nat → Nat) :
    ∀ r s, s < offset u q r →
      ∃ i, i < r ∧ ∃ d, d < (u i).length + q i ∧ s = offset u q i + d := by
  intro r
  induction r with
  | zero => intro s hs; simp [offset] at hs
  | succ r ih =>
    intro s hs
    by_cases h : s < offset u q r
    · obtain ⟨i, hi, d, hd, he⟩ := ih s h
      exact ⟨i, by omega, d, hd, he⟩
    · refine ⟨r, by omega, s - offset u q r, ?_, ?_⟩
      · simp only [offset] at hs
        omega
      · omega

theorem walk_stripes (N T r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hstripe : StripeAt N T)
    (hdrive : ∀ i, i < r → Drives (T + offset u q i) (u i) (q i)) :
    ∀ i, i ≤ r → StripeAt N (T + offset u q i) := by
  intro i
  induction i with
  | zero => intro _; simpa [offset] using hstripe
  | succ i ih =>
    intro hi
    have hh := (maintain N (T + offset u q i) (u i) (q i) hN
      (hlen i (by omega)) (hblack i (by omega)) (hq i (by omega))
      (ih (by omega)) (hdrive i (by omega))).2
    simpa [offset, Nat.add_assoc] using hh

theorem cycle_stripes (N T r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hstripe : StripeAt N T) (hdrive : RepeatsSegments T r u q) :
    ∀ m i, i ≤ r → StripeAt N (T + m * offset u q r + offset u q i) := by
  have hstarts : ∀ m, StripeAt N (T + m * offset u q r) := by
    intro m
    induction m with
    | zero => simpa using hstripe
    | succ m ih =>
      have hh := walk_stripes N (T + m * offset u q r) r u q hN hlen hblack hq
        ih (hdrive m) r (Nat.le_refl _)
      simpa [Nat.succ_mul, Nat.add_assoc] using hh
  intro m
  exact walk_stripes N (T + m * offset u q r) r u q hN hlen hblack hq
    (hstarts m) (hdrive m)

theorem periodic_of_phases (f : Nat → Bool) (T P : Nat) (hP : 0 < P)
    (hphase : ∀ m s, s < P → f (T + (m + 1) * P + s) = f (T + m * P + s)) :
    ∀ t, T ≤ t → f (t + P) = f t := by
  intro t ht
  let k := (t - T) / P
  let s := (t - T) % P
  have hs : s < P := Nat.mod_lt _ hP
  have hd : s + P * k = t - T := Nat.mod_add_div _ _
  have htime : t = T + k * P + s := by
    rw [Nat.mul_comm P k] at hd
    omega
  have hnext : t + P = T + (k + 1) * P + s := by
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  rw [hnext, htime]
  exact hphase k s hs

/-- A repeated finite mixture with a certified initial stripe is impossible. -/
theorem not_repeats_from_stripe (N T r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hr : 1 ≤ r)
    (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hstripe : StripeAt N T) (hdrive : RepeatsSegments T r u q) : False := by
  let P := offset u q r
  have hP : 0 < P := by
    obtain ⟨j, hj, _⟩ := hblack 0 (by omega)
    have hm := offset_mono u q 1 r hr
    simp only [offset] at hm
    dsimp [P]
    omega
  have hstripes := cycle_stripes N T r u q hN hlen hblack hq hstripe hdrive
  have hphase1 : ∀ m s, s < P →
      cell (T + (m + 1) * P + s) 1 = cell (T + m * P + s) 1 := by
    intro m s hs
    obtain ⟨i, hi, d, hd, he⟩ := offset_cover u q r s hs
    have hh := response_agree N (T + (m + 1) * P + offset u q i)
      (T + m * P + offset u q i) (u i) (q i) (q i) hN (hlen i hi)
      (hblack i hi) (hq i hi) (hq i hi)
      (hstripes (m + 1) i (by omega)) (hstripes m i (by omega))
      (hdrive (m + 1) i hi) (hdrive m i hi) d (by omega) (by omega)
    simpa [he, Nat.add_assoc] using hh
  have hphase0 : ∀ m s, s < P →
      cell (T + (m + 1) * P + s) 0 = cell (T + m * P + s) 0 := by
    intro m s hs
    obtain ⟨i, hi, d, hd, he⟩ := offset_cover u q r s hs
    have h0 := hdrive (m + 1) i hi d hd
    have h1 := hdrive m i hi d hd
    have hh := h0.trans h1.symm
    simpa [he, Nat.add_assoc] using hh
  have hp0 : EventuallyPeriodic (fun t => cell t 0) :=
    ⟨T, P, hP, periodic_of_phases (fun t => cell t 0) T P hP hphase0⟩
  have hp1 : EventuallyPeriodic (fun t => cell t (0 + 1)) :=
    ⟨T, P, hP, periodic_of_phases (fun t => cell t 1) T P hP hphase1⟩
  exact not_adjacent 0 hp0 hp1

theorem repeats_shift (T r k : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hdrive : RepeatsSegments T r u q) :
    RepeatsSegments (T + k * offset u q r) r u q := by
  intro m i hi
  have hh := hdrive (k + m) i hi
  simpa [Nat.add_mul, Nat.add_assoc] using hh

/-- A pair of large gaps surrounding block zero provides entry; all other
gaps need only satisfy the linear maintenance bound. -/
theorem not_repeats_seed_pair (N T r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hr : 1 ≤ r)
    (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hbefore : warmup N ≤ q (r - 1))
    (hafter : bound N + 9 * horizon N ≤ q 0)
    (hdrive : RepeatsSegments T r u q) : False := by
  let P := offset u q r
  let W := warmup N
  let A := T + P - W
  have hri : r - 1 < r := by omega
  have hPend : P = offset u q (r - 1) + (u (r - 1)).length + q (r - 1) := by
    dsimp [P]
    exact (congrArg (offset u q) (show r = (r - 1) + 1 by omega)).trans rfl
  have hWP : W ≤ P := by dsimp [W]; omega
  have hwhite : ∀ s, s < W → cell (A + s) 0 = false := by
    intro s hs
    let d := (u (r - 1)).length + q (r - 1) - W + s
    have hd : d < (u (r - 1)).length + q (r - 1) := by dsimp [d, W] at *; omega
    have hdn : (u (r - 1)).length ≤ d := by dsimp [d, W] at *; omega
    have htime : A + s = T + 0 * offset u q r + offset u q (r - 1) + d := by
      dsimp [A, d]
      omega
    rw [htime, hdrive 0 (r - 1) hri d hd,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none hdn]
    rfl
  obtain ⟨ell, hell, hbell, hlast⟩ := exists_last (u 0) (u 0).length
    (Nat.le_refl _) (hblack 0 (by omega))
  have hellN : ell < N := by have hh := hlen 0 (by omega); omega
  have hwitness := physical_white_witness A N ell hN hellN hwhite
  have htime : A + warmup N + ell = T + P + ell := by dsimp [A, W] at *; omega
  rw [htime] at hwitness
  have hd0 : Drives (T + P) (u 0) (q 0) := by
    simpa [P, offset] using hdrive 1 0 (by omega)
  have h0 : cell (T + P + ell) 0 = true := by
    rw [hd0 ell (by omega)]
    exact hbell
  let L := (u 0).length + q 0 - ell - 1
  have hL : bound N + 9 * horizon N ≤ L := by dsimp [L]; omega
  have htailwhite : ∀ s, s < L → cell (T + P + ell + 1 + s) 0 = false := by
    intro s hs
    have hsp : ell + 1 + s < (u 0).length + q 0 := by dsimp [L] at hs; omega
    rw [show T + P + ell + 1 + s = T + P + (ell + 1 + s) by omega,
      hd0 (ell + 1 + s) hsp]
    by_cases hu : ell + 1 + s < (u 0).length
    · exact hlast _ (by omega) hu
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  have hseed0 := (Rule30ArbitraryWhitePadding.Capture.tail_and_stripe (T + P + ell) (bound N)
    (horizon N) L h0 hwitness htailwhite hL).2
  have hseed : StripeAt N (T + P + offset u q 1) := by
    have he : T + P + ell + 1 + L = T + P + offset u q 1 := by
      dsimp [L, offset]
      omega
    simpa only [StripeAt, he] using hseed0
  have hsuffix : ∀ i, 1 ≤ i → i ≤ r → StripeAt N (T + P + offset u q i) := by
    intro i
    induction i with
    | zero => intro hi; omega
    | succ i ih =>
      intro hi hir
      by_cases hi0 : i = 0
      · subst i
        exact hseed
      · have hh := (maintain N (T + P + offset u q i) (u i) (q i) hN
          (hlen i (by omega)) (hblack i (by omega)) (hq i (by omega))
          (ih (by omega) (by omega)) (by simpa [P] using hdrive 1 i (by omega))).2
        simpa [offset, Nat.add_assoc] using hh
  have hstart : StripeAt N (T + 2 * offset u q r) := by
    have hh := hsuffix r hr (Nat.le_refl _)
    simpa [P, Nat.two_mul, Nat.add_assoc] using hh
  exact not_repeats_from_stripe N (T + 2 * offset u q r) r u q hN hr hlen hblack hq
    hstart (repeats_shift T r 2 u q hdrive)

end Schedule

/-! ### The official finite-word interface -/
open Ruliology.CellularAutomata Rule30StripCertificates
open Maintenance Rule30ArbitraryWhitePadding.Physical Schedule

/-- Concatenate the first r blocks, each followed by its prescribed white gap. -/
def word (u : Nat → List Bool) (q : Nat → Nat) : Nat → List Bool
  | 0 => []
  | r+1 => word u q r ++ u r ++ List.replicate (q r) false

theorem word_length (u : Nat → List Bool) (q : Nat → Nat) :
    ∀ r, (word u q r).length = offset u q r
  | 0 => rfl
  | r+1 => by simp only [word,List.length_append,List.length_replicate,word_length u q r,offset]

theorem getD_append_left (a b : List Bool) (s : Nat) (hs : s < a.length) :
    (a++b).getD s false = a.getD s false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hs]

theorem getD_append_offset (a b : List Bool) (s : Nat) :
    (a++b).getD (a.length+s) false = b.getD s false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : a.length ≤ a.length+s)]
  rw [show a.length+s-a.length=s by omega]

theorem padded_getD (u : List Bool) (q s : Nat) :
    (u++List.replicate q false).getD s false = u.getD s false := by
  by_cases hs : s < u.length
  · exact getD_append_left u (List.replicate q false) s hs
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : u.length ≤ s),
      List.getElem?_eq_none (by omega : u.length ≤ s),List.getElem?_replicate]
    split <;> rfl

/-- Every segment has the expected local letters at its exact offset. -/
theorem segment_getD (u : Nat → List Bool) (q : Nat → Nat) :
    ∀ r i s, i < r → s < (u i).length+q i →
      (word u q r).getD (offset u q i+s) false = (u i).getD s false := by
  intro r
  induction r with
  | zero => intro i s hi; omega
  | succ r ih =>
    intro i s hi hs
    by_cases hir : i < r
    · have hend := offset_mono u q (i+1) r (by omega)
      have hindex : offset u q i+s < offset u q r := by
        rw [offset] at hend
        omega
      rw [word,List.append_assoc,getD_append_left (word u q r)
        (u r++List.replicate (q r) false) (offset u q i+s) (by rw [word_length]; exact hindex)]
      exact ih i s hir hs
    · have he : i=r := by omega
      subst i
      rw [word,List.append_assoc,
        show offset u q r+s=(word u q r).length+s by rw [word_length],getD_append_offset]
      exact padded_getD (u r) (q r) s

/-- Official eventual repetition of the concatenation implies the exact segment schedule. -/
theorem eventuallyWord_repeats (r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hevent : EventuallyWord (word u q r)) : ∃ T, RepeatsSegments T r u q := by
  obtain ⟨T,hT⟩ := hevent
  refine ⟨T,?_⟩
  intro m i hi s hs
  have hend := offset_mono u q (i+1) r (by omega)
  have hphase : offset u q i+s < offset u q r := by
    rw [offset] at hend
    omega
  rw [hT _ (by omega),word_length,
    show T+m*offset u q r+offset u q i+s-T=offset u q i+s+m*offset u q r by omega,
    Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hphase]
  exact segment_getD u q r i s hi hs

/-- An official finite repeated word with a certified adjacent large-gap pair is excluded.
All other gaps need only the linear maintenance padding. No initial stripe is assumed. -/
theorem not_eventually_word_seed_pair (N r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hr : 1 ≤ r)
    (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hbefore : warmup N ≤ q (r-1))
    (hafter : bound N+9*horizon N ≤ q 0) :
    ¬ EventuallyWord (word u q r) := by
  intro hevent
  obtain ⟨T,hdrive⟩ := eventuallyWord_repeats r u q hevent
  exact Schedule.not_repeats_seed_pair N T r u q hN hr hlen hblack hq
    hbefore hafter hdrive


end Ruliology.CellularAutomata.Rule30WhitePaddingMixtures
