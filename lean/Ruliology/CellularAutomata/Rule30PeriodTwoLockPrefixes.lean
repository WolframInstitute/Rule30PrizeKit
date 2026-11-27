module

public import Ruliology.CellularAutomata.Rule30LockPrefixCertificates

/-!
# Finite prefix certificates for the period-two lock

Fix the alternating boundary, black at tick zero. Sample `j` is tick `1 + 2*j`.
For any length `m` and prefix code `c`, every infinite completion eventually
enters one of the two phases of the 19-cell lock iff a finite branching
certificate passes. The time and phase can both depend on the completion.
`accepts_hit` identifies them on the branch selected by its actual initial
bits. `deadline_iff` also gives the equivalence at any prescribed deadline.

At sample `j`, the window depends only on the first `20 + 2*j` input bits.
After a split on all still-unknown bits of this cone, every leaf can be
verified by exact evolution. Compactness gives a common deadline from
pointwise entry, since both phases stay in the lock at every later sample.
Partial cones can often be checked earlier by the kit's ternary calculation.

Examples of prefixes forcing entry are the low 23 bits of seed 31 and the
low 20 bits of seed 495. Certificates with largest leaf samples 12 and 6,
respectively, cover these prefixes. For both, the odd-tick gate reads
0101… from sample zero. The sharp lengths for that trace and its shorter
counterexamples are in [R30-20261127-4129d8](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261127-4129d8).
For example, the 20-bit prefix of 495 has this seven-leaf certificate:

    let a := Certificate.hit 6 1
    let b := Certificate.hit 3 0
    let t := Certificate.split (.split a a) (.split (.split a b) b)
    accepts (.split (.split (.hit 1 0) t) (.hit 2 1)) 20 495

The equivalence concerns membership in the lock, in either phase.

onebluecloud with OpenAI Codex (GPT-6). The lock and its closure are from
`Rule30SidewaysLocks` (Quint and Gemini). The proof follows the seven-phase
prefix certificates of `Rule30LockPrefixCertificates` and reuses their
compactness argument and ternary window checker.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodTwoLockPrefixes

open Rule30SidewaysLocks
open Rule30LockPrefixCertificates (HasPrefix prefix_mod uniform_window_iff
  checkWindowClass checkWindowClass_sound)

/-- Entry at this sample, with the phase chosen by the actual 19-cell window. -/
def Locked (R : Nat → Bool) (j : Nat) : Prop :=
  ∃ k : Fin 2, winW 19 R (1+2*j) ∈ cls 19 lock2Codes k.val

theorem locked_later {R : Nat → Bool} {j J : Nat} (le : j ≤ J) (hit : Locked R j) :
    Locked R J := by
  obtain ⟨k, hk⟩ := hit
  have h := lock_forever lock2_ok (by decide) R (t0 := 1+2*j) (by omega) k.isLt hk (J-j)
  exact ⟨⟨(k.val+(J-j))%2, by omega⟩,
    by simpa only [show 1+2*j+2*(J-j) = 1+2*J by omega] using h⟩

inductive Certificate where
  | hit (sample : Nat) (phase : Fin 2)
  | split (zero one : Certificate)
  deriving Repr

def Certificate.deadline : Certificate → Nat
  | .hit j _ => j
  | .split l r => max l.deadline r.deadline

/-- Read only the completion bits queried on this path. -/
def Certificate.follow : Certificate → Nat → (Nat → Bool) → Nat × Fin 2
  | .hit j k, _, _ => (j, k)
  | .split l r, m, R =>
    if R (m+1) then r.follow (m+1) R else l.follow (m+1) R

/-- Verify a tree starting from an already normalized prefix code. -/
def verify : Certificate → Nat → Nat → Bool
  | .hit j k, m, c => checkWindowClass 19 (1+2*j) m c (cls 19 lock2Codes k.val)
  | .split l r, m, c => verify l (m+1) c && verify r (m+1) (2^m+c)

/-- Cell 1 is bit zero. Bits of the prefix code above its length are ignored. -/
def accepts (tree : Certificate) (m c : Nat) : Bool := verify tree m (c % 2^m)

private theorem verify_hit (tree : Certificate) {m c : Nat} (size : c < 2^m)
    (pass : verify tree m c = true) : ∀ R, HasPrefix m c R →
    ∃ j k, tree.follow m R = (j,k) ∧ j ≤ tree.deadline ∧
      winW 19 R (1+2*j) ∈ cls 19 lock2Codes k.val := by
  induction tree generalizing m c with
  | hit j k =>
    exact fun _ h => ⟨j,k,rfl,Nat.le_refl _,checkWindowClass_sound pass h⟩
  | split l r il ir =>
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp pass
    refine Rule30LockPrefixCertificates.Rule30LockCube.split_forces
      (P := fun R => ∃ j k, (l.split r).follow m R = (j,k) ∧ j ≤ (l.split r).deadline ∧
        winW 19 R (1+2*j) ∈ cls 19 lock2Codes k.val) size ?_ ?_
    · intro R h
      have bit := (h m (by omega)).trans (Nat.testBit_lt_two_pow size)
      obtain ⟨j,k,mark,bound,hit⟩ := il (by rw [Nat.pow_succ]; omega) left R h
      exact ⟨j,k,by simpa [Certificate.follow,bit] using mark,
        Nat.le_trans bound (Nat.le_max_left _ _),hit⟩
    · intro R h
      have bit : R (m+1) = true := by
        simpa [Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow size] using h m (by omega)
      obtain ⟨j,k,mark,bound,hit⟩ := ir (by rw [Nat.pow_succ]; omega) right R h
      exact ⟨j,k,by simpa [Certificate.follow,bit] using mark,
        Nat.le_trans bound (Nat.le_max_right _ _),hit⟩

/-- Each completion reaches the very time and phase on the leaf it selects. -/
theorem accepts_hit {tree : Certificate} {m c : Nat} (pass : accepts tree m c = true)
    {R : Nat → Bool} (pref : HasPrefix m c R) :
    ∃ j k, tree.follow m R = (j,k) ∧ j ≤ tree.deadline ∧
      winW 19 R (1+2*j) ∈ cls 19 lock2Codes k.val :=
  verify_hit tree (c := c % 2^m) (Nat.mod_lt _ (Nat.two_pow_pos _)) pass R
    ((prefix_mod R m c).mpr pref)

private theorem complete_at (j n m c : Nat) (enough : 19+(1+2*j) ≤ m+n)
    (all : ∀ R, HasPrefix m c R → Locked R j) :
    ∃ tree, verify tree m c = true ∧ tree.deadline = j := by
  induction n generalizing m c with
  | zero =>
    have full : 19+(1+2*j) ≤ m := by omega
    obtain ⟨k, hit⟩ := all (rh c) (rh_prefix c m)
    rw [winW_prefix (c := c) (rh_prefix c (19+(1+2*j)))] at hit
    exact ⟨.hit j k, by simpa [verify,checkWindowClass,full] using hit, rfl⟩
  | succ n ih =>
    obtain ⟨l,pl,dl⟩ := ih (m+1) c (by omega) (fun R h => all R (fun i hi => h i (by omega)))
    obtain ⟨r,pr,dr⟩ := ih (m+1) (2^m+c) (by omega) (fun R h => all R (fun i hi => by
      simpa only [Nat.testBit_two_pow_add_gt hi] using h i (by omega)))
    exact ⟨.split l r, by simp [verify,pl,pr], by simp [Certificate.deadline,dl,dr]⟩

/-- Exact for every fixed sample, including when the phases of the completions differ. -/
theorem deadline_iff (m c J : Nat) :
    (∀ R, HasPrefix m c R → Locked R J) ↔
    ∃ tree, accepts tree m c = true ∧ tree.deadline ≤ J := by
  constructor
  · intro all
    obtain ⟨tree,pass,eq⟩ := complete_at J (20+2*J-m) m (c % 2^m) (by omega)
      (fun R h => all R ((prefix_mod R m c).mp h))
    exact ⟨tree,pass,by omega⟩
  · rintro ⟨tree,pass,bound⟩ R pref
    obtain ⟨j,k,_,le,hit⟩ := accepts_hit pass pref
    exact locked_later (Nat.le_trans le bound) ⟨k,hit⟩

/-- Every completion eventually enters the period-two lock iff a finite tree passes. -/
theorem eventual_iff (m c : Nat) :
    (∀ R, HasPrefix m c R → ∃ j, Locked R j) ↔ ∃ tree, accepts tree m c = true := by
  have uniform := uniform_window_iff 19 (fun w => ∃ k : Fin 2, w ∈ cls 19 lock2Codes k.val)
    (fun le hit => locked_later le hit) m c
  constructor
  · intro each
    obtain ⟨J,all⟩ := uniform.mp each
    obtain ⟨tree,pass,_⟩ := (deadline_iff m c J).mp all
    exact ⟨tree,pass⟩
  · rintro ⟨tree,pass⟩ R h
    obtain ⟨j,k,_,_,hit⟩ := accepts_hit pass h
    exact ⟨j,k,hit⟩

end Ruliology.CellularAutomata.Rule30PeriodTwoLockPrefixes
