module

public import Rule30Equivalents.TFunctionCycles
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Infinitely many least-return sections of Rule 30

For the existing integer map `TFunction.Phi`, this file proves exact growth of the highest
nonzero bit and uses it to distinguish sections at genuine minimal positive prefix returns.

* `log2_Phi`, `log2_iterate_Phi`: every nonzero finite input gains exactly two top-bit positions
  per tick. The top-bit argument refines the existing `TFunctionCycles.lt_Phi` proof.
* `log2_tail_iterate`: after an n-bit prefix, the tail section of `Phi^p` raises the top degree
  of every positive finite tail by exactly `2*p`, independently of the prefix.
* `period_is_least`, `section_reconstruction`: `period n v` is the actual least positive return
  modulo `2^n`, and its tail map reconstructs the full image under that return.
* `finite_tail_distinguishes`: different exponents give different maps on the same tail `1`,
  distinguished at some finite level. This is functional distinction, not syntactic distinction
  between descriptions of states.
* `orbitSignalizer_infinite`: the set of least-return section maps on finite Nat tails is
  infinite, using the existing `TFunctionCycles.per_unbounded` theorem for the seed `1`.

The representation is `Nat -> Nat` on finite-support tails, with an explicit finite-tree witness.
It does not assert surjectivity on Nat. The proof uses only the forward congruence
`TFunctionCycles.iterate_mod_eq`, the cycle theorem `Phi_cycle`, and the pre-existing unboundedness
of finite-prefix cycle lengths. `AutomatonGroup` already records the relation to group 2369;
its group identification and known noncontraction are not new claims of this file.

Infinitude of these exact section maps does not rule out a finite quotient preserving a chosen
property. No property-preserving reader quotient, arbitrary return theorem, or solution of
Prize Problem 1 follows here. The physical center reads the moving bit `t` of `Phi^t(1)`.

-/

@[expose] public section

namespace Rule30Equivalents.OrbitSignalizer

open Rule30Equivalents.TFunction (Phi low testBit_Phi)
open Rule30Equivalents.TFunctionCycles (lt_Phi)

/-- The top bit of every nonzero finite input moves up exactly two places. -/
theorem log2_Phi {x : Nat} (hx : x ≠ 0) : (Phi x).log2 = x.log2 + 2 := by
  have h1 : x < 2 ^ (x.log2 + 1) := Nat.lt_log2_self
  have hz : x.testBit (x.log2 + 2) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hb : (Phi x).testBit (x.log2 + 2) = true := by
    rw [testBit_Phi, hz]
    have hl : low x (x.log2 + 2) = true := by
      unfold low
      rw [show x.log2 + 2 - 2 = x.log2 by omega, Nat.testBit_log2 hx,
        decide_eq_true (show 2 ≤ x.log2 + 2 by omega)]
      simp
    rw [hl]
    rfl
  have hlow := Nat.ge_two_pow_of_testBit hb
  have hp : 2 ^ (x.log2 + 2 + 1) = 4 * 2 ^ (x.log2 + 1) := by
    rw [show x.log2 + 2 + 1 = (x.log2 + 1) + 2 by omega, Nat.pow_add]
    omega
  have hu : Phi x < 2 ^ (x.log2 + 2 + 1) := by
    unfold Phi
    apply Nat.xor_lt_two_pow
    · rw [hp]; omega
    · apply Nat.or_lt_two_pow <;> rw [hp] <;> omega
  exact (Nat.log2_eq_iff (by have := lt_Phi hx; omega)).2 ⟨hlow, hu⟩

/-- Iterating the genuine Rule 30 map adds twice the elapsed time to top degree. -/
theorem log2_iterate_Phi {x : Nat} (hx : x ≠ 0) (p : Nat) :
    (Phi^[p] x).log2 = x.log2 + 2 * p := by
  have hnonzero : ∀ p, Phi^[p] x ≠ 0 := by
    intro p
    induction p with
    | zero => simpa using hx
    | succ p ih =>
      rw [Function.iterate_succ_apply']
      have := lt_Phi ih
      omega
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', log2_Phi (hnonzero p), ih]
    omega

/-- A finite prefix below bit `n` does not change the top degree of a nonzero tail. -/
theorem log2_prefix_tail (n v x : Nat) (hv : v < 2 ^ n) (hx : 0 < x) :
    (v + 2 ^ n * x).log2 = n + x.log2 := by
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  have hbounds := (Nat.log2_eq_iff (show x ≠ 0 by omega)).1 rfl
  have hl : 2 ^ (n + x.log2) ≤ v + 2 ^ n * x := by
    rw [Nat.pow_add]
    nlinarith [Nat.mul_le_mul_left (2 ^ n) hbounds.1]
  have hu : v + 2 ^ n * x < 2 ^ (n + x.log2 + 1) := by
    rw [show n + x.log2 + 1 = n + (x.log2 + 1) by omega, Nat.pow_add]
    nlinarith [Nat.mul_le_mul_left (2 ^ n) (show x + 1 ≤ 2 ^ (x.log2 + 1) by omega)]
  exact (Nat.log2_eq_iff (by nlinarith)).2 ⟨hl, hu⟩

/-- Every exact tail section of `Phi^p` has degree shift `2p`, independently of the prefix. -/
theorem log2_tail_iterate (n v p x : Nat) (hv : v < 2 ^ n) (hx : 0 < x) :
    ((Phi^[p] (v + 2 ^ n * x)) / 2 ^ n).log2 = x.log2 + 2 * p := by
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  have hy : v + 2 ^ n * x ≠ 0 := by nlinarith
  have hz : Phi^[p] (v + 2 ^ n * x) ≠ 0 := by
    cases p with
    | zero => simpa using hy
    | succ p =>
      have := Rule30Equivalents.TFunctionCycles.lt_iterate_Phi hy (p + 1) (by omega)
      omega
  have he := log2_iterate_Phi hy p
  rw [log2_prefix_tail n v x hv hx] at he
  have hb := (Nat.log2_eq_iff hz).1 he
  have hl : 2 ^ (x.log2 + 2 * p) ≤ (Phi^[p] (v + 2 ^ n * x)) / 2 ^ n := by
    apply (Nat.le_div_iff_mul_le hp).2
    have e : 2 ^ (n + x.log2 + 2 * p) = 2 ^ (x.log2 + 2 * p) * 2 ^ n := by
      rw [show n + x.log2 + 2 * p = (x.log2 + 2 * p) + n by omega, Nat.pow_add]
    simpa only [e] using hb.1
  have hu : (Phi^[p] (v + 2 ^ n * x)) / 2 ^ n < 2 ^ (x.log2 + 2 * p + 1) := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    have e : 2 ^ (n + x.log2 + 2 * p + 1) = 2 ^ (x.log2 + 2 * p + 1) * 2 ^ n := by
      rw [show n + x.log2 + 2 * p + 1 = (x.log2 + 2 * p + 1) + n by omega, Nat.pow_add]
    simpa only [e] using hb.2
  exact (Nat.log2_eq_iff (by have := Nat.two_pow_pos (x.log2 + 2 * p); omega)).2 ⟨hl, hu⟩


open Rule30Equivalents.TFunction (Phi)
open Rule30Equivalents.TFunctionCycles

/-- The action on the tail after reading the n-bit vertex v. -/
def tailSection (n v p x : Nat) : Nat := Phi^[p] (v + 2 ^ n * x) / 2 ^ n

/-- The actual minimal positive orbit length of vertex v modulo 2^n. -/
def period (n v : Nat) : Nat := per Phi ψΦ v n

theorem period_pos (n v : Nat) : 0 < period n v := by
  obtain ⟨k, _, hk⟩ := per_eq_two_pow Phi ψΦ v n
  change 0 < per Phi ψΦ v n
  rw [hk]
  exact Nat.two_pow_pos k

/-- The chosen exponent is an actual return and is minimal among positive returns. -/
theorem period_is_least (n v : Nat) (hv : v < 2 ^ n) :
    Phi^[period n v] v % 2 ^ n = v ∧
    ∀ m, 0 < m → Phi^[m] v % 2 ^ n = v → period n v ≤ m := by
  constructor
  · have hh := (Phi_cycle v n (period n v)).2 (dvd_refl _)
    simpa [Nat.mod_eq_of_lt hv] using hh
  · intro m hm hret
    have hd : period n v ∣ m := (Phi_cycle v n m).1 (by
      simpa [Nat.mod_eq_of_lt hv] using hret)
    exact Nat.le_of_dvd hm hd

/-- Exact section reconstruction under a genuine prefix return. The argument
uses only the forward T-function congruence, never surjectivity on Nat. -/
theorem section_reconstruction (n v p : Nat) (_hv : v < 2 ^ n)
    (hret : Phi^[p] v % 2 ^ n = v) (x : Nat) :
    Phi^[p] (v + 2 ^ n * x) = v + 2 ^ n * tailSection n v p x := by
  have hin : (v + 2 ^ n * x) % 2 ^ n = v % 2 ^ n := by
    simp only [Nat.add_mul_mod_self_left]
  have hcon := iterate_mod_eq Phi_bit hin p
  have hmod : Phi^[p] (v + 2 ^ n * x) % 2 ^ n = v := hcon.trans hret
  have hh := Nat.mod_add_div (Phi^[p] (v + 2 ^ n * x)) (2 ^ n)
  rw [hmod] at hh
  exact hh.symm

/-- Restrictions to finite-support Nat tails of the ordinary orbit-signalizer
elements: one section at each vertex, at its MINIMAL positive orbit length. -/
def orbitSignalizer : Set (Nat → Nat) :=
  {f | ∃ n v, v < 2 ^ n ∧ f = tailSection n v (period n v)}

theorem member_reconstruction {f : Nat → Nat} (hf : f ∈ orbitSignalizer) :
    ∃ n v p, v < 2 ^ n ∧ 0 < p ∧
      (∀ m, 0 < m → Phi^[m] v % 2 ^ n = v → p ≤ m) ∧
      (∀ x, Phi^[p] (v + 2 ^ n * x) = v + 2 ^ n * f x) := by
  obtain ⟨n, v, hv, rfl⟩ := hf
  refine ⟨n, v, period n v, hv, period_pos n v, (period_is_least n v hv).2, ?_⟩
  exact section_reconstruction n v (period n v) hv (period_is_least n v hv).1

/-- Distinct return times give distinct section FUNCTIONS, witnessed on tail 1. -/
theorem section_ne_of_period_ne (n v p n' v' p' : Nat)
    (hv : v < 2 ^ n) (hv' : v' < 2 ^ n') (hp : p ≠ p') :
    tailSection n v p ≠ tailSection n' v' p' := by
  intro heq
  have he := congrArg (fun f : Nat → Nat => (f 1).log2) heq
  have h0 := log2_tail_iterate n v p 1 hv (by omega)
  have h1 := log2_tail_iterate n' v' p' 1 hv' (by omega)
  change (tailSection n v p 1).log2 = Nat.log2 1 + 2 * p at h0
  change (tailSection n' v' p' 1).log2 = Nat.log2 1 + 2 * p' at h1
  rw [h0, h1] at he
  exact hp (by omega)

/-- Both sections differ on the SAME finite, zero-padded tail 1. Taking a
level above both output top bits makes this a genuine finite-tree witness. -/
theorem finite_tail_distinguishes (n v p n' v' p' : Nat)
    (hv : v < 2 ^ n) (hv' : v' < 2 ^ n') (hp : p ≠ p') :
    ∃ k, 1 < 2 ^ k ∧
      tailSection n v p 1 % 2 ^ k ≠ tailSection n' v' p' 1 % 2 ^ k := by
  have h0 : (tailSection n v p 1).log2 = 2 * p := by
    simpa [tailSection] using log2_tail_iterate n v p 1 hv (by omega)
  have h1 : (tailSection n' v' p' 1).log2 = 2 * p' := by
    simpa [tailSection] using log2_tail_iterate n' v' p' 1 hv' (by omega)
  let k := 2 * max p p' + 1
  have hl0 : tailSection n v p 1 < 2 ^ k := by
    have hh : tailSection n v p 1 < 2 ^ ((tailSection n v p 1).log2 + 1) := Nat.lt_log2_self
    rw [h0] at hh
    exact Nat.lt_of_lt_of_le hh (Nat.pow_le_pow_right (by omega) (by
      have hm := Nat.le_max_left p p'; dsimp [k]; omega))
  have hl1 : tailSection n' v' p' 1 < 2 ^ k := by
    have hh : tailSection n' v' p' 1 < 2 ^ ((tailSection n' v' p' 1).log2 + 1) := Nat.lt_log2_self
    rw [h1] at hh
    exact Nat.lt_of_lt_of_le hh (Nat.pow_le_pow_right (by omega) (by
      have hm := Nat.le_max_right p p'; dsimp [k]; omega))
  refine ⟨k, ?_, ?_⟩
  · have hh : 2 ^ 0 < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by dsimp [k]; omega)
    exact hh
  · rw [Nat.mod_eq_of_lt hl0, Nat.mod_eq_of_lt hl1]
    intro he
    have hh := congrArg Nat.log2 he
    rw [h0, h1] at hh
    exact hp (by omega)

/-- The exact orbit-signalizer of the white-boundary Rule 30 automorphism is
infinite. Distinctness is of maps on tails, not of syntactic state words. -/
theorem orbitSignalizer_infinite : orbitSignalizer.Infinite := by
  classical
  intro hfinite
  let M := hfinite.toFinset.sup (fun f : Nat → Nat => (f 1).log2)
  obtain ⟨n, hn⟩ := per_unbounded (a := 1) (by omega) (M + 1)
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    simp [per] at hn
  have hv : 1 < 2 ^ n := by
    have hh : 2 ^ 0 < 2 ^ n := Nat.pow_lt_pow_right (by omega) hnpos
    simpa using hh
  let f := tailSection n 1 (period n 1)
  have hf : f ∈ orbitSignalizer := ⟨n, 1, hv, rfl⟩
  have hbound : (f 1).log2 ≤ M :=
    Finset.le_sup (f := fun g : Nat → Nat => (g 1).log2) (hfinite.mem_toFinset.2 hf)
  have hdeg := log2_tail_iterate n 1 (period n 1) 1 hv (by omega)
  change (f 1).log2 = Nat.log2 1 + 2 * period n 1 at hdeg
  change M + 1 < period n 1 at hn
  omega

end Rule30Equivalents.OrbitSignalizer
