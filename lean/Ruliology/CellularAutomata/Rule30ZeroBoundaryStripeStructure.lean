module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFourComplete

/-!
# Structural Laws for Zero-Boundary Stripe Front Windows

This module explains the exceptional front windows on the ray of `13` (`13, 223, 3553, …`, of
every tail length `4 + 4j`): the seven-cell window `97` is not on that ray, and a rule that
gives the primitive roots off the ray is the question that remains.

1. **Even-Step Orbit Invariance (`cycle_of_orb_even`, `cycle_orb_even_iff`)**:
   Because `fS K` is a periodic permutation on `Fin (2^K) × Fin 2` (`universal_front_period`) and
   `sig` depends only on the step parity (`sig_congr`), the predicate `Cycle K S W p lam` is
   invariant under any even number of front-window steps `t` (`t % 2 = 0`).
2. **The Unmasked 2-Step Clone Map `F_shift` and its `110₂` Top-Bit Signature
   (`orb_two_eq_F_shift`, `F_shift_top_bits`, `cycle_F_shift`, `cycle_F_shiftIter`)**:
   Two unmasked front steps map any `k`-bit window `W` (`2^(k-1) ≤ W < 2^k`) to a `(k + 4)`-bit
   window `F_shift W < 2^(k + 4)` of the same parity whose top three bits at `(k + 3, k + 2, k + 1)`
   are universally `(true, true, false)` (`110₂`), and which satisfies
   `orb K 2 (W, 0) = (F_shift W, 0)` for every width `K ≥ k + 4`. Consequently,
   `Cycle K S W 0 lam → Cycle K S (F_shiftIter j W) 0 lam` transfers any cycle certificate along
   the infinite ray `W → F_shift W → F_shift² W → ⋯` of `(k + 4j)`-bit windows without new
   certificate tables.
3. **Unbounded Width Lifting and Infinite Clone-Ray Mortality (`cycle_lift_width`,
   `cycle_F_shiftIter_unbounded`, `rowTail_F_shiftIter_sound`, `rowTail_ray13_all_odd`)**:
   Combining `orbit_low`, `universal_front_period`, and `cycle_F_shiftIter` lifts any certified odd
   root `W < 2^k` to `Cycle (K + 4 * j + 1) S (F_shiftIter j W) 0 (2 ^ (K + 4 * j + 1))` for
   *every* `j : Nat` (unbounded tail length `k + 4 * j`). In particular, `rowTail_ray13_all_odd`
   certifies horizon-45 mortality for the entire infinite two-parameter family `(j, m)` of odd
   stripe prefixes followed by the `(4 + 4 * j)`-bit exceptional tails `F_shiftIter j 13`
   (`13, 223, 3553, 56907, ...`).
4. **The Backward `00 ↔ 1^∞` Avalanche Dichotomy (`backward_or_recurrence`,
   `backward_zero_tail_dichotomy`)**:
   Whenever `fstep K W fp < 2^m` (`m ≥ 2`), the preimage `W` satisfies the monotone OR recurrence
   `W.testBit i = (W.testBit (i - 1) || W.testBit (i - 2))` for all `m ≤ i < K`. This forces an
   exact dichotomy: either `W.testBit (m - 1) = false ∧ W.testBit (m - 2) = false` (in which case
   `W < 2^(m - 2)` shrinks by 2 bits), or `W.testBit (m - 1) = true ∨ W.testBit (m - 2) = true`
   (in which case `W.testBit i = true` for every `m ≤ i < K`, triggering a `1^∞` avalanche).
5. **Inverse Pullback Characterization of Exceptional Windows (`orb_inv`,
   `not_cycle_iff_survivor_pullback`)**:
   Using the exact inverse orbit `orb_inv K r`, a front window `(w, 0)` fails to close at width
   `K + 1` and horizon `S` if and only if `(w, 0) = orb_inv K r (x, 1)` for some odd step `r` and
   some horizon-`S` zero-boundary survivor `x` (`sig (S + 1) 1 x = false`). Observation (not
   proved in this module): the primitive exceptional roots—`13` at four bits, `97` at seven bits,
   and twelve at eight bits—are the minimal odd windows on each survivor's pullback cycle where
   the backward step starts the `1^∞` avalanche; a rule that gives the primitive roots off the
   ray of `13` is the question that remains.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripeStructure

open Rule30ZeroBoundary Rule30ZeroBoundarySmall Rule30ZeroBoundaryStripeFront
open Rule30ZeroBoundaryStripeFrontLift Rule30ZeroBoundaryStripeFourComplete

/-! ## 1. Phase and Even-Step Orbit Invariance of `Cycle` -/

/-- The phase along `orb K t (W, p)` alternates at each step: for `p < 2`,
`(orb K t (W, p)).2 = (p + t) % 2`. -/
theorem orb_phase (K W p t : Nat) (hp : p < 2) :
    (orb K t (W, p)).2 = (p + t) % 2 := by
  induction t with
  | zero =>
    change p = (p + 0) % 2
    omega
  | succ t ih =>
    change 1 - (orb K t (W, p)).2 = (p + (t + 1)) % 2
    rw [ih]
    omega

/-- After an even number of steps `t`, `orb K t (W, p)` returns to the same phase `p`. -/
theorem orb_even_phase (K W p t : Nat) (hp : p < 2) (ht : t % 2 = 0) :
    (orb K t (W, p)).2 = p := by
  rw [orb_phase K W p t hp]
  omega

/-- Shifting the starting state of a periodic orbit by any `t` steps preserves the period `lam`. -/
theorem orb_period_shift {K lam t : Nat} {s : Nat × Nat} (hper : orb K lam s = s) :
    orb K lam (orb K t s) = orb K t s := by
  rw [← orb_add, Nat.add_comm, orb_add, hper]

/-- `sig` depends only on the parity of the time argument `r`. -/
theorem sig_parity_eq (fuel r₁ r₂ x : Nat) (hpar : r₁ % 2 = r₂ % 2) :
    sig fuel r₁ x = sig fuel r₂ x :=
  sig_congr hpar (fun _ _ => rfl)

/-- **Even-step orbit invariance of `Cycle`.** If `(W, p)` has a checked cycle of period `lam`,
then every state `(W', p) = orb K t (W, p)` at an even step `t` along the orbit also has a checked
cycle with the exact same width `K`, horizon `S`, and period `lam`. -/
theorem cycle_of_orb_even {K S W p lam t : Nat} (hp : p < 2) (ht : t % 2 = 0)
    (hcyc : Cycle K S W p lam) :
    Cycle K S (orb K t (W, p)).1 p lam := by
  obtain ⟨hlam2, hlam0, hper, hsig⟩ := hcyc
  have hpt : orb K t (W, p) = ((orb K t (W, p)).1, p) :=
    Prod.ext rfl (orb_even_phase K W p t hp ht)
  refine ⟨hlam2, hlam0, ?_, ?_⟩
  · rw [← hpt]
    exact orb_period_shift hper
  · intro j hj hpar
    rw [← hpt, ← orb_add, orb_mod K lam (W, p) hper (t + j)]
    have hmod_par : (t + j) % lam % 2 = (0 + j) % 2 := by
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hlam2)]
      omega
    have h1 := hsig ((t + j) % lam) (Nat.mod_lt _ hlam0) (by rw [Nat.zero_add]; omega)
    rw [Nat.zero_add] at h1 ⊢
    rw [sig_parity_eq (S + 1) j ((t + j) % lam) _ (by omega)]
    exact h1

/-- Conversely, if `(orb K t (W, p)).1` has a checked cycle at an even step `t`, so does `W`. -/
theorem cycle_orb_even_iff {K S W p lam t : Nat} (hp : p < 2) (ht : t % 2 = 0)
    (hper_base : orb K lam (W, p) = (W, p)) :
    Cycle K S W p lam ↔ Cycle K S (orb K t (W, p)).1 p lam := by
  constructor
  · exact cycle_of_orb_even hp ht
  · intro hcyc'
    have hlam2 : lam % 2 = 0 := hcyc'.1
    have hlam0 : 0 < lam := hcyc'.2.1
    let t' := lam - t % lam
    have hlt : t % lam < lam := Nat.mod_lt t hlam0
    have ht' : t' % 2 = 0 := by
      have h1 : (t % lam) % 2 = 0 := by
        rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hlam2), ht]
      dsimp [t']
      omega
    have hpt : ((orb K t (W, p)).1, p) = orb K t (W, p) :=
      Prod.ext rfl (orb_even_phase K W p t hp ht).symm
    have hback : (orb K t' ((orb K t (W, p)).1, p)).1 = W := by
      rw [hpt, orb_mod K lam (W, p) hper_base t, ← orb_add]
      have hsum : t % lam + t' = lam := by dsimp [t']; omega
      rw [hsum, hper_base]
    have hc := cycle_of_orb_even hp ht' hcyc'
    rwa [hback] at hc

/-! ## 2. The Universal Unmasked 2-Step Clone Map `F_shift` -/

/-- Unmasked even-phase front step on `Nat`. -/
def fstep0_unmasked (W : Nat) : Nat :=
  W ^^^ (((W <<< 1) ||| 1) ||| ((W <<< 2) ||| (1 <<< 1)))

/-- Unmasked odd-phase front step on `Nat`. -/
def fstep1_unmasked (W : Nat) : Nat :=
  W ^^^ ((W <<< 1) ||| ((W <<< 2) ||| 1))

/-- The unmasked 2-step front-window map `F_shift`: sends any `k`-bit odd window `w` to its
`(k + 4)`-bit 2-step forward clone on the same front orbit. -/
def F_shift (W : Nat) : Nat :=
  fstep1_unmasked (fstep0_unmasked W)

/-- Iteration of `F_shift`. -/
def F_shiftIter : Nat → Nat → Nat
  | 0, W => W
  | j + 1, W => F_shift (F_shiftIter j W)

theorem testBit_one_ge_one {j : Nat} (hj : 1 ≤ j) : (1 : Nat).testBit j = false :=
  Rule30ZeroBoundarySmall.testBit_ge_of_lt (show 1 < 2 ^ 1 by decide) hj

theorem testBit_fstep0_unmasked (W i : Nat) :
    (fstep0_unmasked W).testBit i = xor (W.testBit i)
      ((if i = 0 then true else W.testBit (i - 1)) ||
        (if i = 0 then false else if i = 1 then true else W.testBit (i - 2))) := by
  unfold fstep0_unmasked
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  rcases i with _ | _ | i
  · rfl
  · rw [testBit_one_ge_one (by omega)]
    simp
  · rw [testBit_one_ge_one (by omega), testBit_one_ge_one (by omega)]
    simp

theorem testBit_fstep1_unmasked (W i : Nat) :
    (fstep1_unmasked W).testBit i = xor (W.testBit i)
      ((if i = 0 then false else W.testBit (i - 1)) ||
        (if i = 0 then true else if i = 1 then false else W.testBit (i - 2))) := by
  unfold fstep1_unmasked
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  rcases i with _ | _ | i
  · rfl
  · rw [testBit_one_ge_one (by omega)]
    simp
  · rw [testBit_one_ge_one (by omega)]
    simp

theorem fstep0_unmasked_lt {k W : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k) :
    fstep0_unmasked W < 2 ^ (k + 2) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_fstep0_unmasked]
  have h0 : W.testBit i = false := Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  have h1 : W.testBit (i - 1) = false := Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  have h2 : W.testBit (i - 2) = false := Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  rw [h0, h1, h2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rfl

theorem fstep1_unmasked_lt {k W : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k) :
    fstep1_unmasked W < 2 ^ (k + 2) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_fstep1_unmasked]
  have h0 : W.testBit i = false := Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  have h1 : W.testBit (i - 1) = false := Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  have h2 : W.testBit (i - 2) = false := Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  rw [h0, h1, h2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rfl

/-- If `W < 2^k` (`k ≥ 1`), then `F_shift W < 2^(k + 4)`. -/
theorem F_shift_lt {k W : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k) :
    F_shift W < 2 ^ (k + 4) := by
  unfold F_shift
  have h1 := fstep0_unmasked_lt hk hW
  have h2 := fstep1_unmasked_lt (by omega : 1 ≤ k + 2) h1
  rwa [show k + 2 + 2 = k + 4 by omega] at h2

/-- Iterating `F_shift` `j` times increases the bit-length bound by `4 * j`. -/
theorem F_shiftIter_lt {k W : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k) (j : Nat) :
    F_shiftIter j W < 2 ^ (k + 4 * j) := by
  induction j with
  | zero => simpa [F_shiftIter] using hW
  | succ j ih =>
    unfold F_shiftIter
    have h := F_shift_lt (by omega : 1 ≤ k + 4 * j) ih
    rwa [show k + 4 * j + 4 = k + 4 * (j + 1) by omega] at h

/-- `F_shift` preserves bit 0 (and hence odd/even parity). -/
theorem testBit_zero_F_shift (W : Nat) :
    (F_shift W).testBit 0 = W.testBit 0 := by
  unfold F_shift
  rw [testBit_fstep1_unmasked, testBit_fstep0_unmasked]
  cases W.testBit 0 <;> rfl

/-- `F_shiftIter j` preserves bit 0 for every `j`. -/
theorem testBit_zero_F_shiftIter (j W : Nat) :
    (F_shiftIter j W).testBit 0 = W.testBit 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    unfold F_shiftIter
    rw [testBit_zero_F_shift, ih]

/-- **Universal `110₂` Top-Bit Signature of `F_shift`.**
For any `k`-bit window `W` (`k ≥ 1`) with leading bit `W.testBit (k - 1) = true` and `W < 2^k`,
the top three bits of `F_shift W` at `(k + 3, k + 2, k + 1)` are `(true, true, false)` (`110₂`). -/
theorem F_shift_top_bits {k W : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k)
    (htop : W.testBit (k - 1) = true) :
    (F_shift W).testBit (k + 3) = true ∧
      (F_shift W).testBit (k + 2) = true ∧
      (F_shift W).testBit (k + 1) = false := by
  have hw_k : W.testBit k = false :=
    Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  have hw_k1 : W.testBit (k + 1) = false :=
    Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  have hf0_k : (fstep0_unmasked W).testBit k = true := by
    rw [testBit_fstep0_unmasked, hw_k, htop, ite_eq_right (by omega)]
    simp
  have hf0_k1 : (fstep0_unmasked W).testBit (k + 1) = true := by
    rw [testBit_fstep0_unmasked, hw_k1, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega),
      show k + 1 - 1 = k by omega, show k + 1 - 2 = k - 1 by omega, hw_k, htop]
    simp
  have h1 := fstep0_unmasked_lt hk hW
  have hf0_k2 : (fstep0_unmasked W).testBit (k + 2) = false :=
    Rule30ZeroBoundarySmall.testBit_ge_of_lt h1 (by omega)
  have hf0_k3 : (fstep0_unmasked W).testBit (k + 3) = false :=
    Rule30ZeroBoundarySmall.testBit_ge_of_lt h1 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold F_shift
    rw [testBit_fstep1_unmasked, hf0_k3, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega),
      show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, hf0_k2, hf0_k1]
    rfl
  · unfold F_shift
    rw [testBit_fstep1_unmasked, hf0_k2, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega),
      show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, hf0_k1, hf0_k]
    rfl
  · unfold F_shift
    rw [testBit_fstep1_unmasked, hf0_k1, ite_eq_right (by omega),
      show k + 1 - 1 = k by omega, hf0_k]
    simp

/-- When `fstep0_unmasked W < 2^K`, `fstep K W 0` equals `fstep0_unmasked W` without truncation. -/
theorem fstep_zero_eq_unmasked {K W : Nat} (hbound : fstep0_unmasked W < 2 ^ K) :
    fstep K W 0 = fstep0_unmasked W := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [testBit_fstep K W 0 i (by decide), testBit_fstep0_unmasked]
    simp [hi]
  · rw [testBit_fstep K W 0 i (by decide), decide_eq_false hi, Bool.false_and,
      Rule30ZeroBoundarySmall.testBit_ge_of_lt hbound (by omega)]

/-- When `fstep1_unmasked W < 2^K`, `fstep K W 1` equals `fstep1_unmasked W` without truncation. -/
theorem fstep_one_eq_unmasked {K W : Nat} (hbound : fstep1_unmasked W < 2 ^ K) :
    fstep K W 1 = fstep1_unmasked W := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [testBit_fstep K W 1 i (by decide), testBit_fstep1_unmasked]
    simp [hi]
  · rw [testBit_fstep K W 1 i (by decide), decide_eq_false hi, Bool.false_and,
      Rule30ZeroBoundarySmall.testBit_ge_of_lt hbound (by omega)]

/-- **Fundamental 2-step clone identity.** For any `k`-bit window `W < 2^k` (`k ≥ 1`) and any
width `K ≥ k + 4`, two steps of `orb K` from `(W, 0)` land at `(F_shift W, 0)`. -/
theorem orb_two_eq_F_shift {k K W : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k) (hK : k + 4 ≤ K) :
    orb K 2 (W, 0) = (F_shift W, 0) := by
  have h1 : fstep0_unmasked W < 2 ^ K :=
    Nat.lt_of_lt_of_le (fstep0_unmasked_lt hk hW) (Nat.pow_le_pow_right (by decide) (by omega))
  have h2 : fstep1_unmasked (fstep0_unmasked W) < 2 ^ K :=
    Nat.lt_of_lt_of_le (F_shift_lt hk hW) (Nat.pow_le_pow_right (by decide) hK)
  show (fstep K (fstep K W 0) 1, 0) = (F_shift W, 0)
  rw [fstep_zero_eq_unmasked h1, fstep_one_eq_unmasked h2]
  rfl

/-- Iterated 2-step clone identity: `2 * j` steps of `orb K` from `(W, 0)` land at
`(F_shiftIter j W, 0)` whenever `k + 4 * j ≤ K`. -/
theorem orb_mul_two_eq_F_shiftIter {k K W : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k)
    (j : Nat) (hK : k + 4 * j ≤ K) :
    orb K (2 * j) (W, 0) = (F_shiftIter j W, 0) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Nat.mul_succ, orb_add, ih (by omega)]
    change orb K 2 (F_shiftIter j W, 0) = (F_shift (F_shiftIter j W), 0)
    exact orb_two_eq_F_shift (by omega : 1 ≤ k + 4 * j) (F_shiftIter_lt hk hW j) (by omega)

/-- **Universal Clone-Ray Transfer Theorem.** If `(W, 0)` (`W < 2^k`) has a checked cycle at width
`K ≥ k + 4`, then its `(k + 4)`-bit clone `(F_shift W, 0)` has a checked cycle with the exact same
parameters `(K, S, lam)`. -/
theorem cycle_F_shift {k K S W lam : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k) (hK : k + 4 ≤ K)
    (hcyc : Cycle K S W 0 lam) :
    Cycle K S (F_shift W) 0 lam := by
  have h := cycle_of_orb_even (t := 2) (by decide) (by decide) hcyc
  rwa [orb_two_eq_F_shift hk hW hK] at h

/-- **Iterated Clone-Ray Transfer Theorem.** A single cycle certificate `Cycle K S W 0 lam`
automatically certifies every window `F_shiftIter j W` along the clone ray up to width `K`. -/
theorem cycle_F_shiftIter {k K S W lam j : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k)
    (hK : k + 4 * j ≤ K) (hcyc : Cycle K S W 0 lam) :
    Cycle K S (F_shiftIter j W) 0 lam := by
  have h := cycle_of_orb_even (t := 2 * j) (by decide) (by omega) hcyc
  rwa [orb_mul_two_eq_F_shiftIter hk hW j hK] at h

/-! ## 3. Instant Certificates and Unbounded Clone-Ray Mortality -/

/-- The 8-bit exceptional window `223` (`0b11011111`) is the 2-step clone `F_shift 13`. -/
theorem F_shift_13_eq_223 : F_shift 13 = 223 := by decide

/-- The 12-bit exceptional window `3553` is `F_shift (F_shift 13)`. -/
theorem F_shiftIter_2_13_eq : F_shiftIter 2 13 = 3553 := by decide

/-- The 11-bit exceptional window `1659` is the 2-step clone `F_shift 97`. -/
theorem F_shift_97_eq : F_shift 97 = 1659 := by decide

/-- **Zero-table completion of the 8-bit exceptional window `(223, 0)`** directly from
`cycle13_complete` via `cycle_F_shift`. -/
theorem cycle223_complete : Cycle 46 45 223 0 2097152 := by
  rw [← F_shift_13_eq_223]
  exact cycle_F_shift (k := 4) (by decide) (by decide) (by decide) cycle13_complete

/-- **Zero-table completion of the 12-bit exceptional window `(3553, 0)`** directly from
`cycle13_complete` via `cycle_F_shiftIter`. -/
theorem cycle3553_complete : Cycle 46 45 3553 0 2097152 := by
  rw [← F_shiftIter_2_13_eq]
  exact cycle_F_shiftIter (k := 4) (j := 2) (by decide) (by decide) (by decide) cycle13_complete

/-- Every window `F_shiftIter j 13` (`j ≤ 10`, up to 44-bit tails) is certified at width 46 and
horizon 45 directly from `cycle13_complete`. -/
theorem cycle_ray13_complete (j : Nat) (hj : j ≤ 10) :
    Cycle 46 45 (F_shiftIter j 13) 0 2097152 :=
  cycle_F_shiftIter (k := 4) (j := j) (by decide) (by decide) (by omega) cycle13_complete

/-- Any closed cycle `Cycle K S W p L` (`S + 1 ≤ K`) lifts to any larger width `K + d + 1` with the
universal period `2 ^ (K + d + 1)`. -/
theorem cycle_lift_width {K d S W p L : Nat} (hSK : S + 1 ≤ K) (hW : W < 2 ^ (K + d + 1))
    (hp : p < 2) (hcyc : Cycle K S W p L) :
    Cycle (K + d + 1) S W p (2 ^ (K + d + 1)) := by
  obtain ⟨hL2, hL0, hper, hsig⟩ := hcyc
  refine ⟨by rw [Nat.pow_succ]; omega, Nat.two_pow_pos (K + d + 1),
    universal_front_period (K + d) W p hW hp, ?_⟩
  intro r _ hpar
  have hlow : LowEq (S + 1) (orb (K + d + 1) r (W, p)).1 (orb K r (W, p)).1 :=
    fun i hi => (orbit_low (n := K) (K₁ := K + d + 1) (K₂ := K)
      (by omega) (Nat.le_refl K) (fun _ _ => rfl) hp r).2.2 i (by omega)
  have hmod : (0 + r) % 2 = (0 + r % L) % 2 := by
    rw [Nat.zero_add, Nat.zero_add, Nat.mod_mod_of_dvd r (Nat.dvd_of_mod_eq_zero hL2)]
  rw [sig_congr hmod hlow, orb_mod K L (W, p) hper r]
  exact hsig (r % L) (Nat.mod_lt r hL0) (by omega)

/-- **Unbounded Clone-Ray Transfer Theorem (`∀ j : Nat`).**
For *every* `j : Nat` (arbitrarily large tail lengths `k + 4 * j`), a single cycle certificate
`Cycle K S W 0 L` (`W < 2^k`, `k ≤ K`, `S + 1 ≤ K`) induces a valid horizon-`S` cycle certificate
at width `K + 4 * j + 1` for `F_shiftIter j W`. -/
theorem cycle_F_shiftIter_unbounded {k K S W L : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k)
    (hK : k ≤ K) (hSK : S + 1 ≤ K) (hcyc : Cycle K S W 0 L) (j : Nat) :
    Cycle (K + 4 * j + 1) S (F_shiftIter j W) 0 (2 ^ (K + 4 * j + 1)) := by
  have hW_hi : W < 2 ^ (K + 4 * j + 1) :=
    Nat.lt_of_lt_of_le hW (Nat.pow_le_pow_right (by decide) (by omega))
  have hlift := cycle_lift_width (d := 4 * j) hSK hW_hi (by decide) hcyc
  exact cycle_F_shiftIter hk hW (by omega) hlift

/-- **Unbounded `(13, 0)` Clone-Ray Certificate (`∀ j : Nat`).**
Every window `F_shiftIter j 13` (`j : Nat`, of bit-length `4 + 4 * j`) has a verified horizon-45
cycle at width `46 + 4 * j + 1`. -/
theorem cycle_ray13_unbounded (j : Nat) :
    Cycle (46 + 4 * j + 1) 45 (F_shiftIter j 13) 0 (2 ^ (46 + 4 * j + 1)) :=
  cycle_F_shiftIter_unbounded (k := 4) (by decide) (by decide) (by decide) (by decide)
    cycle13_complete j

/-- The stripe prefix `S[1..m]` followed by the bits of any natural-number tail `w : Nat`. -/
def rowTail (m w : Nat) (k : Nat) : Bool :=
  if k ≤ m then stripe k else w.testBit (k - m - 1)

theorem pk_rowTail (m w K : Nat) (hw : w < 2 ^ K) :
    pk (fun i => rowTail m w (m + 1 + i)) K = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pk]
  by_cases hi : i < K
  · simp only [hi, decide_true, Bool.true_and, rowTail]
    rw [ite_eq_right (by omega), show m + 1 + i - m - 1 = i by omega]
  · simp only [hi, decide_false, Bool.false_and]
    exact (Rule30ZeroBoundarySmall.testBit_ge_of_lt hw (by omega)).symm

/-- **Unbounded Clone-Ray Mortality Theorem (`∀ j m : Nat`).**
If `W < 2^k` is an odd window (`W.testBit 0 = true`) with a cycle certificate `Cycle K S W 0 L`
(`k ≤ K`, `S + 1 ≤ K`), then for *every* clone index `j : Nat` (tail length `k + 4 * j`) and
*every* odd stripe length `m` (`m % 2 = 1`), the configuration `rowTail m (F_shiftIter j W)`
agrees with the stripe on `1..m`, deviates at `m + 1`, and turns depth `1` white at an even time
`t ≤ m + S`. -/
theorem rowTail_F_shiftIter_sound {k K S W L : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k)
    (hodd : W.testBit 0 = true) (hK : k ≤ K) (hSK : S + 1 ≤ K)
    (hcyc : Cycle K S W 0 L) (j m : Nat) (hm : m % 2 = 1) :
    (∀ c, 1 ≤ c → c < m + 1 → rowTail m (F_shiftIter j W) c = stripe c) ∧
      rowTail m (F_shiftIter j W) (m + 1) ≠ stripe (m + 1) ∧
      ∃ t, t ≤ m + S ∧ t % 2 = 0 ∧ zrow (rowTail m (F_shiftIter j W)) t 1 = false := by
  have hag : ∀ c, 1 ≤ c → c < m + 1 → rowTail m (F_shiftIter j W) c = stripe c := by
    intro c _ hc
    unfold rowTail
    rw [ite_eq_left (by omega)]
  have hdev : rowTail m (F_shiftIter j W) (m + 1) ≠ stripe (m + 1) := by
    unfold rowTail
    rw [ite_eq_right (by omega), show m + 1 - m - 1 = 0 by omega,
      testBit_zero_F_shiftIter j W, hodd, stripe_add_mod m 1 1 hm]
    decide
  have hlt : F_shiftIter j W < 2 ^ (K + 4 * j + 1) :=
    Nat.lt_of_lt_of_le (F_shiftIter_lt hk hW j) (Nat.pow_le_pow_right (by decide) (by omega))
  have hwin : pk (fun i => rowTail m (F_shiftIter j W) (m + 1 + i)) (K + 4 * j + 1) =
      F_shiftIter j W :=
    pk_rowTail m (F_shiftIter j W) (K + 4 * j + 1) hlt
  have hc : Cycle (K + 4 * j + 1) S
      (pk (fun i => rowTail m (F_shiftIter j W) (m + 1 + i)) (K + 4 * j + 1))
      ((m + 1) % 2) (2 ^ (K + 4 * j + 1)) := by
    rw [hwin, show (m + 1) % 2 = 0 by omega]
    exact cycle_F_shiftIter_unbounded hk hW hK hSK hcyc j
  obtain ⟨s, hs, he, hz⟩ := front_sound (rowTail m (F_shiftIter j W)) (m + 1)
    (K + 4 * j + 1) S (2 ^ (K + 4 * j + 1)) (by omega) hag (by omega) hc
  exact ⟨hag, hdev, m + s, by omega, by simpa using he, by simpa using hz⟩

/-- **Unbounded Tail-13 Clone-Ray Mortality (`∀ j m : Nat`).**
For every `j : Nat` (arbitrarily large `(4 + 4 * j)`-bit exceptional tails `13, 223, 3553, ...`)
and every odd `m`, `rowTail m (F_shiftIter j 13)` turns depth `1` white at an even time `t ≤ m + 45`. -/
theorem rowTail_ray13_all_odd (j m : Nat) (hm : m % 2 = 1) :
    (∀ c, 1 ≤ c → c < m + 1 → rowTail m (F_shiftIter j 13) c = stripe c) ∧
      rowTail m (F_shiftIter j 13) (m + 1) ≠ stripe (m + 1) ∧
      ∃ t, t ≤ m + 45 ∧ t % 2 = 0 ∧ zrow (rowTail m (F_shiftIter j 13)) t 1 = false :=
  rowTail_F_shiftIter_sound (k := 4) (K := 46) (S := 45) (W := 13) (L := 2097152)
    (by decide) (by decide) (by decide) (by decide) (by decide) cycle13_complete j m hm

/-! ## 4. The Backward `00 ↔ 1^∞` Avalanche Dichotomy -/

/-- Whenever `fstep K W fp < 2^m` (`m ≥ 2`), every bit `i` of the preimage `W` in `[m, K)` satisfies
the monotone OR recurrence `W.testBit i = (W.testBit (i - 1) || W.testBit (i - 2))`. -/
theorem backward_or_recurrence {K m W fp i : Nat} (hm : 2 ≤ m) (hfp : fp < 2)
    (hstep : fstep K W fp < 2 ^ m) (hmi : m ≤ i) (hiK : i < K) :
    W.testBit i = (W.testBit (i - 1) || W.testBit (i - 2)) := by
  have hzero : (fstep K W fp).testBit i = false :=
    Rule30ZeroBoundarySmall.testBit_ge_of_lt hstep hmi
  rw [testBit_fstep K W fp i hfp, decide_eq_true hiK, Bool.true_and,
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at hzero
  cases hA : W.testBit i <;> cases hB : (W.testBit (i - 1) || W.testBit (i - 2)) <;> simp_all

/-- **Case 1 of the Backward Dichotomy (`00 → 0^∞`):** If `fstep K W fp < 2^m` and
`W.testBit (m - 1) = false ∧ W.testBit (m - 2) = false`, then `W.testBit i = false` for all
`m - 2 ≤ i < K`. -/
theorem backward_zero_propagation {K m W fp : Nat} (hm : 2 ≤ m) (hfp : fp < 2)
    (hstep : fstep K W fp < 2 ^ m)
    (hz1 : W.testBit (m - 1) = false) (hz2 : W.testBit (m - 2) = false) :
    ∀ d, m - 2 + d < K → W.testBit (m - 2 + d) = false := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro hdK
    rcases (show d = 0 ∨ d = 1 ∨ 2 ≤ d by omega) with rfl | rfl | hd2
    · simpa using hz2
    · rw [show m - 2 + 1 = m - 1 by omega]; exact hz1
    · rw [backward_or_recurrence hm hfp hstep (by omega) hdK,
        show m - 2 + d - 1 = m - 2 + (d - 1) by omega,
        show m - 2 + d - 2 = m - 2 + (d - 2) by omega,
        ih (d - 1) (by omega) (by omega), ih (d - 2) (by omega) (by omega)]
      rfl

/-- **Case 2 of the Backward Dichotomy (`¬ 00 → 1^∞` Avalanche):** If `fstep K W fp < 2^m` and
`W.testBit (m - 1) = true ∨ W.testBit (m - 2) = true`, then `W.testBit i = true` for every
`m ≤ i < K`. -/
theorem backward_one_avalanche {K m W fp : Nat} (hm : 2 ≤ m) (hfp : fp < 2)
    (hstep : fstep K W fp < 2 ^ m)
    (hone : W.testBit (m - 1) = true ∨ W.testBit (m - 2) = true) :
    ∀ d, m + d < K → W.testBit (m + d) = true := by
  intro d
  induction d with
  | zero =>
    intro hmK
    rw [Nat.add_zero] at hmK ⊢
    rw [backward_or_recurrence hm hfp hstep (by omega) hmK]
    rcases hone with h1 | h2
    · simp [h1]
    · simp [h2]
  | succ d ih =>
    intro hdK
    rw [backward_or_recurrence hm hfp hstep (by omega) hdK,
      show m + (d + 1) - 1 = m + d by omega, ih (by omega)]
    simp

/-- **The Backward `00 ↔ 1^∞` Avalanche Dichotomy.**
For any preimage `W < 2^K` of an `m`-bit window `fstep K W fp < 2^m` (`2 ≤ m ≤ K`), either
`W < 2^(m - 2)` (shrinks by 2 bits) or `W.testBit i = true` across the entire upper tail
`m ≤ i < K` (`1^∞` avalanche). -/
theorem backward_zero_tail_dichotomy {K m W fp : Nat} (hm : 2 ≤ m) (hW : W < 2 ^ K)
    (hfp : fp < 2) (hstep : fstep K W fp < 2 ^ m) :
    W < 2 ^ (m - 2) ∨ (∀ i, m ≤ i → i < K → W.testBit i = true) := by
  by_cases h1 : W.testBit (m - 1) = false ∧ W.testBit (m - 2) = false
  · left
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases hiK : i < K
    · have h := backward_zero_propagation hm hfp hstep h1.1 h1.2 (i - (m - 2)) (by omega)
      rwa [show m - 2 + (i - (m - 2)) = i by omega] at h
    · exact Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)
  · right
    have hone : W.testBit (m - 1) = true ∨ W.testBit (m - 2) = true := by
      cases h_m1 : W.testBit (m - 1) <;> cases h_m2 : W.testBit (m - 2)
      · exact absurd ⟨h_m1, h_m2⟩ h1
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    intro i hmi hiK
    have h := backward_one_avalanche hm hfp hstep hone (i - m) (by omega)
    rwa [show m + (i - m) = i by omega] at h

/-! ## 5. Exact Inverse Orbit `orb_inv` and the Survivor Pullback Rule -/

/-- The inverse of `orb (K + 1) r` on `Fin (2^(K + 1)) × Fin 2`, defined via the universal period
`2^(K + 1)`. -/
def orb_inv (K r : Nat) (s : Nat × Nat) : Nat × Nat :=
  orb (K + 1) (2 ^ (K + 1) - r % 2 ^ (K + 1)) s

theorem orb_inv_cancel_left (K r w p : Nat)
    (hw : w < 2 ^ (K + 1)) (hp : p < 2) :
    orb_inv K r (orb (K + 1) r (w, p)) = (w, p) := by
  unfold orb_inv
  have hper := universal_front_period K w p hw hp
  rw [orb_mod (K + 1) (2 ^ (K + 1)) (w, p) hper r, ← orb_add]
  have hpos : 0 < 2 ^ (K + 1) := Nat.two_pow_pos (K + 1)
  have hlt : r % 2 ^ (K + 1) < 2 ^ (K + 1) := Nat.mod_lt r hpos
  have hsum : r % 2 ^ (K + 1) + (2 ^ (K + 1) - r % 2 ^ (K + 1)) = 2 ^ (K + 1) := by omega
  rw [hsum, hper]

theorem orb_inv_cancel_right (K r w p : Nat)
    (hw : w < 2 ^ (K + 1)) (hp : p < 2) :
    orb (K + 1) r (orb_inv K r (w, p)) = (w, p) := by
  unfold orb_inv
  have hper := universal_front_period K w p hw hp
  have hpos : 0 < 2 ^ (K + 1) := Nat.two_pow_pos (K + 1)
  have hlt : r % 2 ^ (K + 1) < 2 ^ (K + 1) := Nat.mod_lt r hpos
  have hper' : orb (K + 1) (2 ^ (K + 1)) (orb (K + 1) (2 ^ (K + 1) - r % 2 ^ (K + 1)) (w, p)) =
      orb (K + 1) (2 ^ (K + 1) - r % 2 ^ (K + 1)) (w, p) :=
    orb_period_shift hper
  rw [orb_mod (K + 1) (2 ^ (K + 1)) _ hper' r, ← orb_add]
  have hsum : 2 ^ (K + 1) - r % 2 ^ (K + 1) + r % 2 ^ (K + 1) = 2 ^ (K + 1) := by omega
  rw [hsum, hper]

/-- An odd-arrival state `x` is a horizon-`S` zero-boundary survivor if `sig (S + 1) 1 x = false`. -/
def IsOddSurvivor (S x : Nat) : Prop :=
  sig (S + 1) 1 x = false

/-- **Survivor Pullback Characterization of Exceptional Front Windows.**
At width `K + 1`, a front window `(w, 0)` (`w < 2^(K + 1)`) fails to form a valid horizon-`S` cycle
of universal period `2^(K + 1)` if and only if `(w, 0)` is the backward pullback `orb_inv K r (x, 1)`
of some horizon-`S` zero-boundary survivor `x < 2^(K + 1)` at an odd step `r < 2^(K + 1)`. -/
theorem not_cycle_iff_survivor_pullback (K S w : Nat) (hw : w < 2 ^ (K + 1)) :
    ¬ Cycle (K + 1) S w 0 (2 ^ (K + 1)) ↔
      ∃ r, r < 2 ^ (K + 1) ∧ r % 2 = 1 ∧
        ∃ x, x < 2 ^ (K + 1) ∧ IsOddSurvivor S x ∧ orb_inv K r (x, 1) = (w, 0) := by
  have hlam2 : 2 ^ (K + 1) % 2 = 0 := by
    rw [Nat.pow_succ]
    omega
  have hlam0 : 0 < 2 ^ (K + 1) := Nat.two_pow_pos (K + 1)
  have hper : orb (K + 1) (2 ^ (K + 1)) (w, 0) = (w, 0) :=
    universal_front_period K w 0 hw (by decide)
  constructor
  · intro hnc
    have hnot : ¬ ∀ j, j < 2 ^ (K + 1) → (0 + j) % 2 = 1 - 0 →
        sig (S + 1) (0 + j) (orb (K + 1) j (w, 0)).1 = true := by
      intro hall
      exact hnc ⟨hlam2, hlam0, hper, hall⟩
    rw [Classical.not_forall] at hnot
    obtain ⟨r, hr⟩ := hnot
    rw [Classical.not_imp, Classical.not_imp] at hr
    obtain ⟨hr_lt, hr_par, hsig_false⟩ := hr
    simp only [Nat.zero_add, Nat.sub_zero, Bool.not_eq_true] at hr_par hsig_false
    refine ⟨r, hr_lt, hr_par, (orb (K + 1) r (w, 0)).1, orbit_bound hw r, ?_, ?_⟩
    · unfold IsOddSurvivor
      rw [sig_parity_eq (S + 1) 1 r _ (by omega)]
      exact hsig_false
    · have hphase : (orb (K + 1) r (w, 0)).2 = 1 := by
        rw [orb_phase (K + 1) w 0 r (by decide)]
        omega
      have hpair : ((orb (K + 1) r (w, 0)).1, 1) = orb (K + 1) r (w, 0) :=
        Prod.ext rfl hphase.symm
      rw [hpair]
      exact orb_inv_cancel_left K r w 0 hw (by decide)
  · rintro ⟨r, hr_lt, hr_par, x, hx, hsurv, hpull⟩ ⟨_, _, _, hsig⟩
    have hfwd : orb (K + 1) r (w, 0) = (x, 1) := by
      rw [← hpull]
      exact orb_inv_cancel_right K r x 1 hx (by decide)
    have hok := hsig r hr_lt (by omega)
    simp only [Nat.zero_add, hfwd] at hok
    rw [sig_parity_eq (S + 1) r 1 x (by omega)] at hok
    unfold IsOddSurvivor at hsurv
    rw [hsurv] at hok
    exact Bool.false_ne_true hok

end Rule30ZeroBoundaryStripeStructure
end Ruliology.CellularAutomata
