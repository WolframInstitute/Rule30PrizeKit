module

public import Ruliology.CellularAutomata.Rule30Problem3
public import Ruliology.CellularAutomata.Rule30BlackRuns
public import Ruliology.CellularAutomata.Rule30CenterRuns
public import Ruliology.CellularAutomata.Rule30LeftUnbounded
public import Ruliology.CellularAutomata.Rule30FactorWindow

/-!
# Prize Problem 3: head-cone locality, dyadic ray collapse, and unconditional step lower bounds

Structural properties and unconditional lower bounds for deterministic one-tape Turing machines
(`Rule30Problem3.Machine`) computing the Rule 30 center column `center` from the binary digits of
`n` (least significant bit first).

- **Head-cone and prefix locality (`run_eq_of_init_eq_lt`).** Starting at `head = 0`, in `t` steps
  a one-tape machine only inspects tape cells `i < t`; since negative cells of `M.init n` are
  always blank, `M.run n t` depends only on the cells `0 ≤ i < t` of `M.init n`.
- **2-adic tape congruence and transient elimination (`init_tape_eq_of_mod_two_pow_eq`,
  `computes_eq_of_mod_two_pow_of_run_le`, `computes_const_on_dyadic_ray`).** For any `k ≥ 1`, all
  inputs `n ≥ 2^(k-1)` in the same residue class modulo `2^k` share the exact same non-blank tape
  prefix on cells `i < k`. Consequently, if a machine computing `f` halts in at most `k` steps on
  even a single (arbitrarily large) input `n ≥ 2^(k-1)`, then `f` is constant across the entire
  residue ray `{m ≥ 2^(k-1) | m ≡ n (mod 2^k)}` all the way down to `2^(k-1)`—eliminating any
  transient beyond `2^(k-1)`.
- **Residue-flip, fixed-transient periodicity, and unbounded step lower bounds (`time_gt_of_mod_two_pow_ne`,
  `log2_succ_succ_le_time_of_ray_flip`, `period_of_eventually_time_le`, `time_unbounded_le_thirteen`,
  `evPer_two_pow_of_eventually_time_le`, `time_unbounded_of_problem1`, `diagonal_time_unbounded`,
  `period_of_canon_window_time_le`, `diagonal_canon_window_time_ge`).**
  Any single pair `r, m ≥ 2^(k-1)` with `r ≡ m (mod 2^k)` and `f r ≠ f m` forces `k + 1 ≤ T n` for
  every `n ≥ 2^(k-1)` in that residue class, and flipping above the MSB forces
  `Nat.log2 n + 2 ≤ T n` (`log2_succ_succ_le_time_of_ray_flip`). Moreover, if `T n ≤ k` from some
  `N` on, every residue class mod `2^k` has a witness `m + N * 2^k ≥ N`, so `f` has period `2^k`
  from the fixed threshold `2^(k-1)` independent of `N` (`period_of_eventually_time_le`). Combining
  this with `Rule30FactorWindow.transient_add_period_ge` (`T₀ + P ≥ 16359`) proves unconditionally
  (without `Problem1`) that for every `k ≤ 13`, every machine computing `center` takes at least
  `k + 1` steps infinitely often (`time_unbounded_le_thirteen`, up to `14` steps), while
  `Rule30LeftUnbounded.D_period_unbounded` yields left diagonals requiring `≥ k + 1` steps
  infinitely often for every `k` (`diagonal_time_unbounded`). In fact, `T r ≤ k` merely on the
  canonical window `r ∈ [2^(k-1), 2^(k-1) + 2^k)` of `2^k` inputs already makes `f` `2^k`-periodic
  from `2^(k-1)` on (`period_of_canon_window_time_le`), so for every `k` some left diagonal `D j`
  (`j ≤ 2^(2*2^k)`) forces `k + 1 ≤ T r` on the canonical window `[2^(k-1), 2^(k-1) + 2^k)` itself
  (`diagonal_canon_window_time_ge`).
- **Fast cone evaluation and unconditional uniform step bounds (`center_eq_fastCenter`,
  `one_le_time`, `two_le_time`, `three_le_time`, `four_le_time`, `five_le_time`,
  `log2_succ_succ_le_time_lt_16`).** Using `Rule30BlackRuns.stepRow` on `rowAt 0 (-t) (2t + 1)`,
  we evaluate the explicit minimal residue-flip witnesses for `k = 1, 2, 3, 4` (`t ≤ 99`) and prove
  unconditionally that every machine `M` computing `center` satisfies `k + 1 ≤ T n` for all
  `n ≥ 2^(k-1)` (`1 ≤ k ≤ 4`), and `Nat.log2 n + 2 ≤ T n` for all `1 ≤ n < 16`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Problem3Bounds

open Rule30Jen Rule30Prize Rule30Diagonals Rule30BlackRuns
open Rule30CenterRuns Rule30LeftReset Rule30LeftUnbounded Rule30Problem3

/-! ### 1. Head-cone and prefix locality of `Machine.run` -/

/-- A single head move increases the head position by at most `1`. -/
theorem move_apply_le_succ (d : Move) (h : Int) : d.apply h ≤ h + 1 := by
  cases d <;> simp [Move.apply] <;> omega

/-- If two configurations have the same state, the same head position, and the same tape symbol at
the head, then one step either halts with the same answer on both or produces configurations with
the same state, the same head position, and tapes that agree wherever the original tapes agreed. -/
theorem step_congr_below {M : Machine} {c₁ c₂ : Cfg M} {B : Int}
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head) (hhead : c₁.head < B)
    (ht : ∀ i : Int, i < B → c₁.tape i = c₂.tape i) :
    (∃ b, c₁.step = .inl b ∧ c₂.step = .inl b) ∨
      ∃ c₁' c₂', c₁.step = .inr c₁' ∧ c₂.step = .inr c₂' ∧
        c₁'.state = c₂'.state ∧ c₁'.head = c₂'.head ∧ c₁'.head ≤ c₁.head + 1 ∧
        (∀ i : Int, i < B → c₁'.tape i = c₂'.tape i) := by
  have hread : c₁.tape c₁.head = c₂.tape c₂.head := by
    rw [← hh]
    exact ht c₁.head hhead
  unfold Cfg.step
  rw [hs, hread]
  cases hδ : M.δ c₂.state (c₂.tape c₂.head) with
  | inl b => exact Or.inl ⟨b, rfl, rfl⟩
  | inr val =>
    obtain ⟨p, a, d⟩ := val
    refine Or.inr ⟨_, _, rfl, rfl, rfl, by rw [hh], move_apply_le_succ d c₁.head, fun i hi => ?_⟩
    dsimp only
    rw [hh]
    by_cases hih : i = c₂.head
    · simp [hih]
    · simp [hih, ht i hi]

/-- General horizon invariance for `t` steps: if `M.run m s` and `M.run n s` are in configurations
that agree on state, head, and all tape cells below `head + k`, then after `k` more steps they
either both halt with the same answer or remain in configurations agreeing on state and head. -/
theorem run_add_congr_below {M : Machine} (m n : Nat) :
    ∀ (k s : Nat) {c₁ c₂ : Cfg M},
      M.run m s = .inr c₁ → M.run n s = .inr c₂ →
      c₁.state = c₂.state → c₁.head = c₂.head →
      (∀ i : Int, i < c₁.head + (k : Int) → c₁.tape i = c₂.tape i) →
      (∃ b, M.run m (s + k) = .inl b ∧ M.run n (s + k) = .inl b) ∨
        ∃ c₁' c₂', M.run m (s + k) = .inr c₁' ∧ M.run n (s + k) = .inr c₂' ∧
          c₁'.state = c₂'.state ∧ c₁'.head = c₂'.head
  | 0, s, c₁, c₂, hm, hn, hs, hh, _ => Or.inr ⟨c₁, c₂, hm, hn, hs, hh⟩
  | k + 1, s, c₁, c₂, hm, hn, hs, hh, ht => by
    have hstep := step_congr_below (B := c₁.head + ((k + 1 : Nat) : Int)) hs hh (by omega) ht
    rcases hstep with ⟨b, hb₁, hb₂⟩ | ⟨c₁', c₂', hc₁', hc₂', hs', hh', hle, ht'⟩
    · left
      have hm1 : M.run m (s + 1) = .inl b := by simp [Machine.run, hm, hb₁]
      have hn1 : M.run n (s + 1) = .inl b := by simp [Machine.run, hn, hb₂]
      refine ⟨b, ?_, ?_⟩
      · have := Machine.run_add hm1 k
        rwa [show s + 1 + k = s + (k + 1) by omega] at this
      · have := Machine.run_add hn1 k
        rwa [show s + 1 + k = s + (k + 1) by omega] at this
    · have hm1 : M.run m (s + 1) = .inr c₁' := by simp [Machine.run, hm, hc₁']
      have hn1 : M.run n (s + 1) = .inr c₂' := by simp [Machine.run, hn, hc₂']
      have ih := run_add_congr_below m n k (s + 1) hm1 hn1 hs' hh' (fun i hi => ht' i (by omega))
      rwa [show s + 1 + k = s + (k + 1) by omega] at ih

/-- Negative tape cells of `M.init n` are always blank (`0`), independent of `n`. -/
theorem init_tape_neg (M : Machine) (n : Nat) {i : Int} (hi : i < 0) :
    (M.init n).tape i = ⟨0, by omega⟩ := by
  simp only [Machine.init]
  rw [ite_eq_right (fun h => by omega)]

/-- **Head-cone prefix locality.** If `M.init m` and `M.init n` agree on all tape cells
`0 ≤ i < t`, then `M.run m t` halts with `.inl b` if and only if `M.run n t` halts with `.inl b`. -/
theorem run_eq_of_init_eq_lt {M : Machine} {m n t : Nat}
    (htape : ∀ i : Int, 0 ≤ i → i < (t : Int) → (M.init m).tape i = (M.init n).tape i)
    (b : Bool) : M.run m t = .inl b ↔ M.run n t = .inl b := by
  have hcongr := run_add_congr_below (M := M) m n t 0 (c₁ := M.init m) (c₂ := M.init n)
    rfl rfl rfl rfl (fun i hi => by
      have h0 : (M.init m).head = 0 := rfl
      rw [h0, Int.zero_add] at hi
      by_cases hneg : i < 0
      · rw [init_tape_neg M m hneg, init_tape_neg M n hneg]
      · exact htape i (by omega) hi)
  rw [Nat.zero_add] at hcongr
  rcases hcongr with ⟨b', hb₁, hb₂⟩ | ⟨c₁', c₂', hc₁', hc₂', _, _⟩
  · rw [hb₁, hb₂]
  · rw [hc₁', hc₂']
    simp

/-! ### 2. 2-adic tape congruence and transient elimination -/

/-- If `m % 2^k = n % 2^k`, then `m` and `n` share all binary digits `testBit j` for `j < k`. -/
theorem testBit_eq_of_mod_two_pow_eq {m n k j : Nat} (hj : j < k)
    (hmod : m % 2 ^ k = n % 2 ^ k) : m.testBit j = n.testBit j := by
  have h1 := Nat.testBit_mod_two_pow m k j
  have h2 := Nat.testBit_mod_two_pow n k j
  rw [hmod] at h1
  rw [decide_eq_true hj, Bool.true_and] at h1 h2
  exact h1.symm.trans h2

/-- **2-adic initial-tape congruence.** For any `k : Nat` and any `m, n ≥ 2^(k-1)` with
`m % 2^k = n % 2^k`, the initial tapes `M.init m` and `M.init n` are identical on all cells
`0 ≤ i < k`. -/
theorem init_tape_eq_of_mod_two_pow_eq (M : Machine) {m n k : Nat}
    (hm : 2 ^ (k - 1) ≤ m) (hn : 2 ^ (k - 1) ≤ n) (hmod : m % 2 ^ k = n % 2 ^ k) :
    ∀ i : Int, 0 ≤ i → i < (k : Int) → (M.init m).tape i = (M.init n).tape i := by
  intro i hi0 hik
  have hlt : i.toNat < k := by omega
  have hle : i.toNat ≤ k - 1 := by omega
  have hpow : 2 ^ i.toNat ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by decide) hle
  have hm_cond : 0 ≤ i ∧ 2 ^ i.toNat ≤ m := ⟨hi0, Nat.le_trans hpow hm⟩
  have hn_cond : 0 ≤ i ∧ 2 ^ i.toNat ≤ n := ⟨hi0, Nat.le_trans hpow hn⟩
  simp only [Machine.init]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hm_cond), ite_eq_left_of_eq_true _ _ (eq_true hn_cond),
    testBit_eq_of_mod_two_pow_eq hlt hmod]

/-- If `M.run n t = .inl b₁` and `M.run n s = .inl b₂`, then `b₁ = b₂`. -/
theorem run_inl_unique {M : Machine} {n t s : Nat} {b₁ b₂ : Bool}
    (h₁ : M.run n t = .inl b₁) (h₂ : M.run n s = .inl b₂) : b₁ = b₂ := by
  have e₁ := Machine.run_add h₁ s
  have e₂ := Machine.run_add h₂ t
  rw [Nat.add_comm] at e₂
  have := e₁.symm.trans e₂
  injection this

/-- **Transient elimination / residue collapse.** If `M` computes `f` within time `T` and halts on
an input `n ≥ 2^(k-1)` within `k` steps (`T n ≤ k`), then for every `m ≥ 2^(k-1)` with
`m % 2^k = n % 2^k`, `M.run m k = .inl (f n)` and `f m = f n`. -/
theorem computes_eq_of_mod_two_pow_of_run_le {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {m n k : Nat} (hm : 2 ^ (k - 1) ≤ m) (hn : 2 ^ (k - 1) ≤ n)
    (hmod : m % 2 ^ k = n % 2 ^ k) (hT : T n ≤ k) :
    M.run m k = .inl (f n) ∧ f m = f n := by
  have hrun_n : M.run n k = .inl (f n) := by
    have := Machine.run_add (hM n) (k - T n)
    rwa [Nat.add_sub_cancel' hT] at this
  have hrun_m : M.run m k = .inl (f n) :=
    (run_eq_of_init_eq_lt (init_tape_eq_of_mod_two_pow_eq M hm hn hmod) (f n)).mpr hrun_n
  exact ⟨hrun_m, (run_inl_unique hrun_m (hM m)).symm⟩

/-- **Dyadic ray collapse.** If `M` computes `f` within time `T`, `2^(k-1) ≤ n`, and `T n ≤ k`,
then the entire arithmetic progression `u ↦ f (n + u * 2^k)` (`u : Nat`) is constant. -/
theorem computes_const_on_dyadic_ray {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {n k : Nat} (hn : 2 ^ (k - 1) ≤ n) (hT : T n ≤ k) (u : Nat) :
    f (n + u * 2 ^ k) = f n := by
  have hm : 2 ^ (k - 1) ≤ n + u * 2 ^ k := by omega
  have hmod : (n + u * 2 ^ k) % 2 ^ k = n % 2 ^ k := by
    rw [Nat.add_mul_mod_self_right]
  exact (computes_eq_of_mod_two_pow_of_run_le hM hm hn hmod hT).2

/-! ### 3. General residue-flip, blank-reach, and diagonal lower bounds -/

/-- **Residue-pair step lower bound.** If `r, m ≥ 2^(k-1)` lie in the same residue class modulo
`2^k` and `f r ≠ f m`, then every input `n ≥ 2^(k-1)` in that residue class requires at least
`k + 1` steps on any machine computing `f`. -/
theorem time_gt_of_mod_two_pow_ne {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {r m n k : Nat}
    (hr : 2 ^ (k - 1) ≤ r) (hm : 2 ^ (k - 1) ≤ m) (hn : 2 ^ (k - 1) ≤ n)
    (hrm : r % 2 ^ k = m % 2 ^ k) (hrn : r % 2 ^ k = n % 2 ^ k) (hne : f r ≠ f m) :
    k + 1 ≤ T n := by
  by_cases hle : T n ≤ k
  · exfalso
    have e₁ := (computes_eq_of_mod_two_pow_of_run_le hM hr hn hrn hle).2
    have e₂ := (computes_eq_of_mod_two_pow_of_run_le hM hm hn (hrm.symm.trans hrn) hle).2
    exact hne (e₁.trans e₂.symm)
  · omega

/-- **Logarithmic blank-reach lower bound.** For any input `n ≥ 1`, let `L = Nat.log2 n + 1` be the
binary digit length of `n`. If there exists `u : Nat` such that `f (n + u * 2^L) ≠ f n`, then any
machine computing `f` must take at least `Nat.log2 n + 2` steps on `n` (scanning all `L` binary
digits plus the first blank cell). -/
theorem log2_succ_succ_le_time_of_ray_flip {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {n u : Nat} (hn : 1 ≤ n)
    (hflip : f (n + u * 2 ^ (Nat.log2 n + 1)) ≠ f n) :
    Nat.log2 n + 2 ≤ T n := by
  have hpow : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le (by omega)
  have hle : ¬ T n ≤ Nat.log2 n + 1 := fun hT =>
    hflip (computes_const_on_dyadic_ray hM (k := Nat.log2 n + 1) hpow hT u)
  omega

/-- If `M` computes `f` and takes at most `k` steps from `N` on, then `f` has period `2 ^ k` from
`2 ^ (k - 1)` on, whatever `N` is. -/
theorem period_of_eventually_time_le {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k N : Nat} (hT : ∀ n, N ≤ n → T n ≤ k) :
    ∀ m, 2 ^ (k - 1) ≤ m → f (m + 2 ^ k) = f m := by
  intro m hm
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hNle : N ≤ N * 2 ^ k := Nat.le_mul_of_pos_right N hpos
  have hn : 2 ^ (k - 1) ≤ m + N * 2 ^ k := by omega
  have hTn : T (m + N * 2 ^ k) ≤ k := hT _ (by omega)
  have hmod₁ : m % 2 ^ k = (m + N * 2 ^ k) % 2 ^ k := by
    rw [Nat.add_mul_mod_self_right]
  have hmod₂ : (m + 2 ^ k) % 2 ^ k = (m + N * 2 ^ k) % 2 ^ k := by
    rw [Nat.add_mod_right, Nat.add_mul_mod_self_right]
  have e₁ := (computes_eq_of_mod_two_pow_of_run_le hM hm hn hmod₁ hTn).2
  have e₂ := (computes_eq_of_mod_two_pow_of_run_le hM (by omega) hn hmod₂ hTn).2
  exact e₂.trans e₁.symm

/-- For every `k ≤ 13`, every machine computing `center` takes more than `k` steps on infinitely
many inputs, without `Problem1`. -/
theorem time_unbounded_le_thirteen {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {k : Nat} (hk : k ≤ 13) (N : Nat) : ∃ n, N ≤ n ∧ k + 1 ≤ T n := by
  refine Classical.byContradiction fun hno => ?_
  have hT : ∀ n, N ≤ n → T n ≤ k := fun n hn =>
    Nat.le_of_not_lt fun hlt => hno ⟨n, hn, hlt⟩
  have hper := period_of_eventually_time_le hM hT
  have hwin : 16359 ≤ 2 ^ (k - 1) + 2 ^ k :=
    Rule30FactorWindow.transient_add_period_ge (2 ^ (k - 1)) (2 ^ k) (Nat.two_pow_pos k)
      fun t ht => hper t ht
  have h1 : 2 ^ (k - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ k ≤ 2 ^ 13 := Nat.pow_le_pow_right (by decide) hk
  have e12 : (2 : Nat) ^ 12 = 4096 := rfl
  have e13 : (2 : Nat) ^ 13 = 8192 := rfl
  omega

/-- **Eventual time `≤ k` implies eventual period `2^k`.** If `M` computes `f` within time `T` and
`T n ≤ k` for all `n ≥ N`, then `f` is eventually `2^k`-periodic (`EvPer f (2^k)`). -/
theorem evPer_two_pow_of_eventually_time_le {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k N : Nat} (hT : ∀ n, N ≤ n → T n ≤ k) :
    EvPer f (2 ^ k) := by
  refine ⟨max N (2 ^ (k - 1)), fun n hn => ?_⟩
  have h := computes_const_on_dyadic_ray hM (n := n) (k := k) (by omega) (hT n (by omega)) 1
  rwa [Nat.one_mul] at h

/-- **`Problem1` implies unbounded Turing step counts for `center`.** Under `Problem1`, for every
machine `M` computing `center` in time `T`, every step budget `k : Nat`, and every threshold `N`,
there is an input `n ≥ N` on which `M` requires at least `k + 1` steps. -/
theorem time_unbounded_of_problem1 (hP1 : Problem1) {M : Machine} {T : Nat → Nat}
    (hM : Computes M center T) (k N : Nat) : ∃ n, N ≤ n ∧ k + 1 ≤ T n := by
  by_cases hex : ∃ n, N ≤ n ∧ k + 1 ≤ T n
  · exact hex
  · exfalso
    have hev : EvPer center (2 ^ k) :=
      evPer_two_pow_of_eventually_time_le hM (k := k) (N := N) (fun n hn => by
        by_cases hle : T n ≤ k
        · exact hle
        · exact absurd ⟨n, hn, by omega⟩ hex)
    obtain ⟨T0, hT0⟩ := hev
    exact hP1 ⟨T0, 2 ^ k, Nat.two_pow_pos k, hT0⟩

/-- **Every doubling window `[b, 2b]` (`b ≥ 1`) contains both a white and a black center cell.** -/
theorem exists_both_colors_in_window (b : Nat) (hb : 1 ≤ b) :
    (∃ t₁, b ≤ t₁ ∧ t₁ ≤ 2 * b ∧ center t₁ = false) ∧
    (∃ t₂, b ≤ t₂ ∧ t₂ < 2 * b ∧ center t₂ = true) :=
  ⟨exists_white b hb, exists_black' b hb⟩

/-- **Unbounded Turing step complexity across left diagonals `D j`.** By
`Rule30LeftUnbounded.D_period_unbounded`, for every step budget `k : Nat` there is a left diagonal
`D j` with `j ≤ 2 ^ (2 * 2 ^ k)` such that for every machine `M` and time function `T` computing
`D j` and every threshold `N : Nat`, some input `n ≥ N` requires at least `k + 1` steps. -/
theorem diagonal_time_unbounded (k : Nat) :
    ∃ j ≤ 2 ^ (2 * 2 ^ k), ∀ {M : Machine} {T : Nat → Nat},
      Computes M (D j) T → ∀ N, ∃ n, N ≤ n ∧ k + 1 ≤ T n := by
  obtain ⟨j, hj, hnot⟩ := D_period_unbounded (2 ^ k) (Nat.two_pow_pos k)
  refine ⟨j, hj, fun {M} {T} hM N => ?_⟩
  by_cases hex : ∃ n, N ≤ n ∧ k + 1 ≤ T n
  · exact hex
  · exfalso
    apply hnot
    refine evPer_two_pow_of_eventually_time_le hM (N := N) (fun n hn => ?_)
    by_cases hle : T n ≤ k
    · exact hle
    · exact absurd ⟨n, hn, by omega⟩ hex

/-! ### 4. Fast cone evaluation and unconditional uniform step lower bounds for `center` -/

/-- Element `i < n` of `rowAt t p n` is `cell t (p + i)`. -/
theorem getD_rowAt (t : Nat) : ∀ (n i : Nat) (p : Int), i < n →
    (rowAt t p n).getD i false = cell t (p + i)
  | 0, i, _, hi => by omega
  | n + 1, 0, p, _ => by simp [rowAt]
  | n + 1, i + 1, p, hi => by
    simp only [rowAt, List.getD_cons_succ]
    rw [getD_rowAt t n i (p + 1) (by omega)]
    congr 1
    omega

/-- Iterating `stepRow false` `k` times on a finite row list. -/
def runZero : Nat → List Bool → List Bool
  | 0, L => L
  | k + 1, L => runZero k (stepRow false L)

/-- Because every cell strictly left of `-N` is white up to time `N`, one step of `stepRow false`
on `rowAt t (-N) (n + 1)` gives `rowAt (t + 1) (-N) n`. -/
theorem stepRow_false_rowAt {t N n : Nat} (ht : t ≤ N) :
    stepRow false (rowAt t (-(N : Int)) (n + 1)) = rowAt (t + 1) (-(N : Int)) n := by
  have h0 : cell t (-(N : Int) - 1) = false := cell_eq_false_of_lt t _ (by omega)
  rw [← h0]
  exact stepRow_rowAt t n (-(N : Int))

/-- Iterating `runZero k` from time `t` with `t + k ≤ N` advances `rowAt` to time `t + k`. -/
theorem runZero_rowAt {N : Nat} : ∀ (k t n : Nat), t + k ≤ N →
    runZero k (rowAt t (-(N : Int)) (n + k)) = rowAt (t + k) (-(N : Int)) n
  | 0, t, n, _ => by simp [runZero]
  | k + 1, t, n, htk => by
    simp only [runZero]
    rw [show n + (k + 1) = (n + k) + 1 by omega, stepRow_false_rowAt (by omega),
      runZero_rowAt k (t + 1) n (by omega), show t + 1 + k = t + (k + 1) by omega]

/-- The initial light-cone row `[-(t : Int), t]` at time `0`: a single black cell at index `t`. -/
def initCone (t : Nat) : List Bool :=
  List.replicate t false ++ (true :: List.replicate t false)

/-- `rowAt 0 p n` is all `false` whenever `p + n ≤ 0`. -/
theorem rowAt_zero_neg : ∀ (n : Nat) (p : Int), p + (n : Int) ≤ 0 →
    rowAt 0 p n = List.replicate n false
  | 0, _, _ => rfl
  | n + 1, p, hp => by
    have h0 : cell 0 p = false := decide_eq_false (by omega)
    simp only [rowAt, h0, List.replicate_succ]
    rw [rowAt_zero_neg n (p + 1) (by omega)]

/-- `rowAt 0 p n` is all `false` whenever `1 ≤ p`. -/
theorem rowAt_zero_pos : ∀ (n : Nat) (p : Int), 1 ≤ p →
    rowAt 0 p n = List.replicate n false
  | 0, _, _ => rfl
  | n + 1, p, hp => by
    have h0 : cell 0 p = false := decide_eq_false (by omega)
    simp only [rowAt, h0, List.replicate_succ]
    rw [rowAt_zero_pos n (p + 1) (by omega)]

/-- Splitting `rowAt t p (a + b)` into two adjacent blocks. -/
theorem rowAt_add (t : Nat) : ∀ (a b : Nat) (p : Int),
    rowAt t p (a + b) = rowAt t p a ++ rowAt t (p + a) b
  | 0, b, p => by simp [rowAt]
  | a + 1, b, p => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [rowAt, List.cons_append]
    rw [rowAt_add t a b (p + 1), show p + 1 + (a : Int) = p + ((a + 1 : Nat) : Int) by omega]

/-- `initCone t` equals `rowAt 0 (-(t : Int)) (2 * t + 1)`. -/
theorem initCone_eq_rowAt (t : Nat) :
    initCone t = rowAt 0 (-(t : Int)) (2 * t + 1) := by
  unfold initCone
  rw [show 2 * t + 1 = t + (t + 1) by omega, rowAt_add 0 t (t + 1) (-(t : Int)),
    rowAt_zero_neg t (-(t : Int)) (by omega), show -(t : Int) + (t : Int) = 0 by omega]
  simp only [rowAt, show cell 0 0 = true from rfl, show (0 : Int) + 1 = 1 from rfl]
  rw [rowAt_zero_pos t 1 (by omega)]

/-- Fast quadratic evaluator for `center t`: evolve `initCone t` for `t` steps and read index `t`. -/
def fastCenter (t : Nat) : Bool := (runZero t (initCone t)).getD t false

/-- **`center t` equals `fastCenter t`.** -/
theorem center_eq_fastCenter (t : Nat) : center t = fastCenter t := by
  unfold fastCenter
  rw [initCone_eq_rowAt t, show 2 * t + 1 = (t + 1) + t by omega,
    runZero_rowAt (N := t) t 0 (t + 1) (by omega), Nat.zero_add,
    getD_rowAt t (t + 1) t (-(t : Int)) (by omega), show -(t : Int) + (t : Int) = 0 by omega]
  rfl

/-- Explicit witness multiplier `u ≥ 1` flipping `center (r + u * 2^k)` for `k = 1, 2, 3, 4`. -/
def flipWitness (k r : Nat) : Nat :=
  match k, r with
  | 1, 1 => 3 | 2, 2 => 5 | 2, 4 => 2 | 2, 5 => 3 | 3, 5 => 2 | 3, 6 => 2 | 3, 8 => 3 | 3, 10 => 2 | 4, 8 => 2 | 4, 11 => 4 | 4, 13 => 2 | 4, 19 => 5 | 4, 20 => 4 | 4, 23 => 3
  | _, _ => 1

/-- Kernel check of the minimal residue-flip pairs `(r, r + flipWitness k r * 2^k)` for `k = 1, 2, 3, 4` (`t ≤ 99`). -/
theorem dyadic_residues_flip_up_to_four :
    ((List.range' 1 2).all (fun r => fastCenter r != fastCenter (r + flipWitness 1 r * 2)) &&
     (List.range' 2 4).all (fun r => fastCenter r != fastCenter (r + flipWitness 2 r * 4)) &&
     (List.range' 4 8).all (fun r => fastCenter r != fastCenter (r + flipWitness 3 r * 8)) &&
     (List.range' 8 16).all (fun r => fastCenter r != fastCenter (r + flipWitness 4 r * 16))) = true := by
  decide +kernel

/-- Canonical representative of `n` in `[2^(k-1), 2^(k-1) + 2^k)` sharing `n % 2^k`. -/
def canonRep (k n : Nat) : Nat := 2 ^ (k - 1) + (n - 2 ^ (k - 1)) % 2 ^ k

/-- `canonRep k n` lies in `List.range' (2^(k-1)) (2^k)` and agrees with `n` modulo `2^k`. -/
theorem canonRep_spec {k n : Nat} (hn : 2 ^ (k - 1) ≤ n) :
    canonRep k n ∈ List.range' (2 ^ (k - 1)) (2 ^ k) ∧
    2 ^ (k - 1) ≤ canonRep k n ∧
    canonRep k n % 2 ^ k = n % 2 ^ k := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlt : (n - 2 ^ (k - 1)) % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpos
  refine ⟨List.mem_range'.mpr ⟨(n - 2 ^ (k - 1)) % 2 ^ k, hlt, by unfold canonRep; omega⟩,
    by unfold canonRep; omega, ?_⟩
  unfold canonRep
  have hd : n = 2 ^ (k - 1) + ((n - 2 ^ (k - 1)) % 2 ^ k + 2 ^ k * ((n - 2 ^ (k - 1)) / 2 ^ k)) := by
    have := Nat.mod_add_div (n - 2 ^ (k - 1)) (2 ^ k)
    omega
  conv => rhs; rw [hd]
  rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]

/-- `canonRep k n` lies strictly below `2^(k-1) + 2^k`. -/
theorem canonRep_lt {k n : Nat} : canonRep k n < 2 ^ (k - 1) + 2 ^ k := by
  unfold canonRep
  have : (n - 2 ^ (k - 1)) % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  omega

/-- **Finite canonical-window periodicity.** If `M` computes `f` in time `T` and `T r ≤ k` for
every input `r` in the canonical window `[2^(k-1), 2^(k-1) + 2^k)` of `2^k` inputs, then `f` has
period `2^k` for all `m ≥ 2^(k-1)`. -/
theorem period_of_canon_window_time_le {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k : Nat}
    (hwin : ∀ r, 2 ^ (k - 1) ≤ r → r < 2 ^ (k - 1) + 2 ^ k → T r ≤ k) :
    ∀ m, 2 ^ (k - 1) ≤ m → f (m + 2 ^ k) = f m := by
  intro m hm
  let r := canonRep k m
  obtain ⟨_, hr1, hmod⟩ := canonRep_spec hm
  have hr2 : r < 2 ^ (k - 1) + 2 ^ k := canonRep_lt
  have hTr : T r ≤ k := hwin r hr1 hr2
  have hmod1 : m % 2 ^ k = r % 2 ^ k := hmod.symm
  have hmod2 : (m + 2 ^ k) % 2 ^ k = r % 2 ^ k := by
    rw [Nat.add_mod_right, hmod1]
  have e1 := (computes_eq_of_mod_two_pow_of_run_le hM hm hr1 hmod1 hTr).2
  have e2 := (computes_eq_of_mod_two_pow_of_run_le hM (by omega) hr1 hmod2 hTr).2
  exact e2.trans e1.symm

/-- **Unconditional canonical-window step lower bound on left diagonals.** For every `k : Nat`,
there exists a left diagonal `D j` (`j ≤ 2 ^ (2 * 2 ^ k)`) such that every machine `M` computing
`D j` in time `T` takes at least `k + 1` steps on some input `r` in the canonical window
`[2^(k-1), 2^(k-1) + 2^k)`. -/
theorem diagonal_canon_window_time_ge (k : Nat) :
    ∃ j ≤ 2 ^ (2 * 2 ^ k), ∀ (M : Machine) (T : Nat → Nat), Computes M (D j) T →
      ∃ r, 2 ^ (k - 1) ≤ r ∧ r < 2 ^ (k - 1) + 2 ^ k ∧ k + 1 ≤ T r := by
  obtain ⟨j, hj, hnot⟩ := D_period_unbounded (2 ^ k) (Nat.two_pow_pos k)
  refine ⟨j, hj, fun M T hM => Classical.byContradiction fun hno => ?_⟩
  have hwin : ∀ r, 2 ^ (k - 1) ≤ r → r < 2 ^ (k - 1) + 2 ^ k → T r ≤ k := fun r hr1 hr2 =>
    Nat.le_of_not_lt fun hlt => hno ⟨r, hr1, hr2, hlt⟩
  have hper := period_of_canon_window_time_le hM hwin
  exact hnot ⟨2 ^ (k - 1), fun m hm => by simpa [Nat.add_comm] using hper m hm⟩

/-- Generic converter from a verified `List.all` residue-flip check to a uniform step bound
`k + 1 ≤ T n` for all `n ≥ 2^(k-1)`. -/
theorem time_gt_of_all_flip {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {k : Nat} (hall : (List.range' (2 ^ (k - 1)) (2 ^ k)).all
      (fun r => fastCenter r != fastCenter (r + flipWitness k r * 2 ^ k)) = true)
    {n : Nat} (hn : 2 ^ (k - 1) ≤ n) : k + 1 ≤ T n := by
  obtain ⟨hmem, hr, hmod⟩ := canonRep_spec hn
  have hu := List.all_eq_true.mp hall (canonRep k n) hmem
  have hne : center (canonRep k n) ≠ center (canonRep k n + flipWitness k (canonRep k n) * 2 ^ k) := by
    rw [center_eq_fastCenter, center_eq_fastCenter]
    intro heq
    rw [heq, bne_self_eq_false] at hu
    exact Bool.noConfusion hu
  exact time_gt_of_mod_two_pow_ne hM hr (by omega) hn
    (by rw [Nat.add_mul_mod_self_right]) hmod hne

/-- **No machine halts in `0` steps:** `1 ≤ T n` for every input `n`. -/
theorem one_le_time {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) (n : Nat) : 1 ≤ T n := by
  rcases Nat.eq_zero_or_pos (T n) with h0 | hpos
  · have h := hM n
    rw [h0] at h
    cases h
  · exact hpos

/-- **Unconditional `2`-step lower bound:** every machine computing `center` takes at least `2`
steps on every input `n ≥ 1`. -/
theorem two_le_time {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn : 1 ≤ n) : 2 ≤ T n := by
  have h := dyadic_residues_flip_up_to_four
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact time_gt_of_all_flip hM (k := 1) h.1.1.1 hn

/-- **Unconditional `3`-step lower bound:** every machine computing `center` takes at least `3`
steps on every input `n ≥ 2`. -/
theorem three_le_time {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn : 2 ≤ n) : 3 ≤ T n := by
  have h := dyadic_residues_flip_up_to_four
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact time_gt_of_all_flip hM (k := 2) h.1.1.2 hn

/-- **Unconditional `4`-step lower bound:** every machine computing `center` takes at least `4`
steps on every input `n ≥ 4`. -/
theorem four_le_time {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn : 4 ≤ n) : 4 ≤ T n := by
  have h := dyadic_residues_flip_up_to_four
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact time_gt_of_all_flip hM (k := 3) h.1.2 hn

/-- **Unconditional `5`-step lower bound:** every machine computing `center` takes at least `5`
steps on every input `n ≥ 8`. -/
theorem five_le_time {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn : 8 ≤ n) : 5 ≤ T n := by
  have h := dyadic_residues_flip_up_to_four
  rw [Bool.and_eq_true] at h
  exact time_gt_of_all_flip hM (k := 4) h.2 hn

/-- **Full-input scan bound up to `n < 16`:** on every input `1 ≤ n < 16`, every machine computing
`center` takes at least `Nat.log2 n + 2` steps (scanning all binary digits of `n` plus the first
blank cell). -/
theorem log2_succ_succ_le_time_lt_16 {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn1 : 1 ≤ n) (hn16 : n < 16) : Nat.log2 n + 2 ≤ T n := by
  by_cases h2 : n < 2
  · have hn : n = 1 := by omega
    have hlog : Nat.log2 n = 0 := by rw [hn]; rfl
    rw [hlog]
    exact two_le_time hM hn1
  · by_cases h4 : n < 4
    · have hlog : Nat.log2 n = 1 := by
        rcases (show n = 2 ∨ n = 3 by omega) with rfl | rfl <;> rfl
      rw [hlog]; exact three_le_time hM (by omega)
    · by_cases h8 : n < 8
      · have hlog : Nat.log2 n = 2 := by
          rcases (show n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 by omega) with rfl | rfl | rfl | rfl <;> rfl
        rw [hlog]; exact four_le_time hM (by omega)
      · have hlog : Nat.log2 n = 3 := by
          have hge : 2 ^ 3 ≤ n := by omega
          have hlt : n < 2 ^ 4 := by omega
          exact Nat.le_antisymm (Nat.le_of_lt_succ ((Nat.log2_lt (by omega)).mpr hlt))
            ((Nat.le_log2 (by omega)).mpr hge)
        rw [hlog]; exact five_le_time hM (by omega)


/-! ### Right-head horizon (`ScansBelow`), `RightSpan`, time-space collapse, and spatial excursion bounds -/

/-- After `s` steps from `head = 0`, any active configuration `c` satisfies `c.head ≤ s`. -/
theorem run_head_le_steps {M : Machine} {n : Nat} :
    ∀ {s : Nat} {c : Cfg M}, M.run n s = .inr c → c.head ≤ (s : Int)
  | 0, c, hc => by
    injection hc with h
    subst h
    simp [Machine.init]
  | s + 1, c, hc => by
    simp only [Machine.run] at hc
    cases hr : M.run n s with
    | inl b => rw [hr] at hc; cases hc
    | inr c₀ =>
      rw [hr] at hc
      dsimp only at hc
      have ih := run_head_le_steps hr
      unfold Cfg.step at hc
      cases hδ : M.δ c₀.state (c₀.tape c₀.head) with
      | inl b => rw [hδ] at hc; cases hc
      | inr val =>
        rcases val with ⟨p, a, d⟩
        rw [hδ] at hc
        injection hc with h
        subst h
        have hm := move_apply_le_succ d c₀.head
        dsimp only
        omega

/-- During the first `t` steps on input `n`, `M`'s head remains strictly to the left of cell `B`
(even if `M` runs for arbitrarily many steps `t` and uses the negative half-tape `i < 0` as
unbounded workspace). -/
def ScansBelow (M : Machine) (n t : Nat) (B : Int) : Prop :=
  ∀ s, s < t → ∀ c, M.run n s = .inr c → c.head < B

/-- Monotonicity of `ScansBelow` in the step horizon `t`. -/
theorem ScansBelow.mono {M : Machine} {n t₁ t₂ : Nat} {B : Int}
    (h : ScansBelow M n t₂ B) (ht : t₁ ≤ t₂) : ScansBelow M n t₁ B :=
  fun s hs c hc => h s (Nat.lt_of_lt_of_le hs ht) c hc

/-- Monotonicity of `ScansBelow` in the spatial barrier `B`. -/
theorem ScansBelow.mono_bound {M : Machine} {n t : Nat} {B₁ B₂ : Int}
    (h : ScansBelow M n t B₁) (hB : B₁ ≤ B₂) : ScansBelow M n t B₂ :=
  fun s hs c hc => Int.lt_of_lt_of_le (h s hs c hc) hB

/-- Any run of length `t ≤ k` from `head = 0` automatically satisfies `ScansBelow M n t k`. -/
theorem scansBelow_of_le {M : Machine} {n t k : Nat} (ht : t ≤ k) :
    ScansBelow M n t (k : Int) := by
  intro s hs c hc
  have hle := run_head_le_steps hc
  omega

/-- The right-hand input span `RightSpan M n t`: the smallest `B : Nat` such that `M`'s head stays
strictly below cell `B` during the first `t` steps on input `n` (measuring how many non-negative
cells `0, …, B - 1` the head reaches). -/
def RightSpan (M : Machine) (n : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 =>
    match M.run n t with
    | .inl _ => RightSpan M n t
    | .inr c => max (RightSpan M n t) (c.head + 1).toNat

/-- **Exact equivalence between `ScansBelow` and `RightSpan`.** For every `B : Nat`, the head
stays strictly below cell `B` during the first `t` steps iff `RightSpan M n t ≤ B`. -/
theorem scansBelow_iff_rightSpan_le {M : Machine} {n t B : Nat} :
    ScansBelow M n t (B : Int) ↔ RightSpan M n t ≤ B := by
  induction t with
  | zero =>
    simp [ScansBelow, RightSpan]
  | succ t ih =>
    simp only [RightSpan]
    cases hr : M.run n t with
    | inl b =>
      dsimp only
      rw [← ih]
      refine ⟨fun h s hs c hc => h s (by omega) c hc, fun h s hs c hc => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with hlt | rfl
      · exact h s hlt c hc
      · rw [hr] at hc; cases hc
    | inr c₀ =>
      dsimp only
      rw [Nat.max_le, ← ih]
      refine ⟨fun h => ⟨fun s hs c hc => h s (by omega) c hc, ?_⟩, fun ⟨h1, h2⟩ s hs c hc => ?_⟩
      · have hlt : c₀.head < (B : Int) := h t (Nat.lt_succ_self t) c₀ hr
        omega
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with hlt | rfl
        · exact h1 s hlt c hc
        · rw [hr] at hc
          injection hc with h
          subst h
          omega

/-- In `t` steps from `head = 0`, `RightSpan M n t ≤ t`. -/
theorem rightSpan_le_steps (M : Machine) (n t : Nat) : RightSpan M n t ≤ t := by
  exact scansBelow_iff_rightSpan_le.mp (scansBelow_of_le (Nat.le_refl t))

/-- **Unbounded-time step congruence below a spatial barrier `B`.** If `M.init m` and `M.init n`
agree on all cells `0 ≤ i < B` (and hence on all `i < B`, since negative cells are blank) and
`ScansBelow M n t B` holds, then `M.run m t = M.run n t`, and if both are still running at step `t`
their configurations have the same state, the same head position, and identical tapes below `B`. -/
theorem run_congr_of_scansBelow {M : Machine} {m n : Nat} {B : Nat}
    (hinit : ∀ i : Int, 0 ≤ i → i < B → (M.init m).tape i = (M.init n).tape i) :
    ∀ t, ScansBelow M n t (B : Int) →
      match M.run m t, M.run n t with
      | .inl b₁, .inl b₂ => b₁ = b₂
      | .inr c₁, .inr c₂ =>
          c₁.state = c₂.state ∧ c₁.head = c₂.head ∧ ∀ i : Int, i < B → c₁.tape i = c₂.tape i
      | _, _ => False
  | 0, _ => by
    refine ⟨rfl, rfl, fun i hi => ?_⟩
    by_cases h0 : 0 ≤ i
    · exact hinit i h0 hi
    · simp [Machine.init, h0]
  | t + 1, hscan => by
    have ih := run_congr_of_scansBelow hinit t (hscan.mono (Nat.le_succ t))
    simp only [Machine.run]
    cases hm : M.run m t with
    | inl b₁ =>
      cases hn : M.run n t with
      | inl b₂ => rw [hm, hn] at ih; exact ih
      | inr c₂ => rw [hm, hn] at ih; exact False.elim ih
    | inr c₁ =>
      cases hn : M.run n t with
      | inl b₂ => rw [hm, hn] at ih; exact False.elim ih
      | inr c₂ =>
        rw [hm, hn] at ih
        obtain ⟨hst, hhd, htp⟩ := ih
        have hlt : c₁.head < (B : Int) := by
          rw [hhd]
          exact hscan t (Nat.lt_succ_self t) c₂ hn
        rcases step_congr_below hst hhd hlt htp with ⟨b, h1, h2⟩ | ⟨c₁', c₂', h1, h2, hst', hhd', _, htp'⟩
        · dsimp only; rw [h1, h2]
        · dsimp only; rw [h1, h2]; exact ⟨hst', hhd', htp'⟩

/-- **Unbounded-time run invariance under `ScansBelow`.** If `M.init m` and `M.init n` agree on
all input cells `0 ≤ i < B` and `M`'s head on input `n` stays strictly below cell `B` during `t`
steps (`ScansBelow M n t B`), then `M.run m t = M.run n t`—regardless of how large `t` is or how
many negative worktape cells `i < 0` are visited. -/
theorem run_eq_of_init_eq_of_scansBelow {M : Machine} {m n t B : Nat}
    (hinit : ∀ i : Int, 0 ≤ i → i < B → (M.init m).tape i = (M.init n).tape i)
    (hscan : ScansBelow M n t (B : Int)) :
    (∀ b, M.run m t = .inl b ↔ M.run n t = .inl b) ∧ ScansBelow M m t (B : Int) := by
  refine ⟨fun b => ?_, fun s hs c₁ hc₁ => ?_⟩
  · have h := run_congr_of_scansBelow hinit t hscan
    cases hm : M.run m t <;> cases hn : M.run n t <;> rw [hm, hn] at h
    · simp [h]
    · exact False.elim h
    · exact False.elim h
    · simp
  · have h := run_congr_of_scansBelow hinit s (hscan.mono (Nat.le_of_lt hs))
    cases hn : M.run n s with
    | inl b₂ => rw [hc₁, hn] at h; exact False.elim h
    | inr c₂ =>
      rw [hc₁, hn] at h
      rw [h.2.1]
      exact hscan s hs c₂ hn

/-- **2-adic ray collapse under bounded right-head excursion (`ScansBelow`).** If `M` computes `f`
in time `T`, `m, n ≥ 2^(k-1)` (`k ≥ 1`) satisfy `m % 2^k = n % 2^k`, and on input `n` the head of
`M` never visits cell `k` or higher (`ScansBelow M n (T n) k`), then `M` halts on `m` within `T n`
steps with `M.run m (T n) = .inl (f n)`, `f m = f n`, and `ScansBelow M m (T n) k`. -/
theorem computes_eq_of_mod_two_pow_of_scansBelow {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k m n : Nat} (hm : 2 ^ (k - 1) ≤ m) (hn : 2 ^ (k - 1) ≤ n)
    (hmod : m % 2 ^ k = n % 2 ^ k) (hscan : ScansBelow M n (T n) (k : Int)) :
    M.run m (T n) = .inl (f n) ∧ f m = f n ∧ ScansBelow M m (T n) (k : Int) := by
  rcases k with _ | k'
  · exfalso
    have h0 : M.run n 0 = .inr (M.init n) := rfl
    rcases Nat.eq_zero_or_pos (T n) with hT0 | hTpos
    · have h := hM n; rw [hT0] at h; cases h
    · have hlt := hscan 0 hTpos (M.init n) h0
      simp [Machine.init] at hlt
  · have hinit : ∀ i : Int, 0 ≤ i → i < (k' + 1 : Nat) → (M.init m).tape i = (M.init n).tape i :=
      fun i hi0 hik => init_tape_eq_of_mod_two_pow_eq M hm hn hmod i hi0 hik
    obtain ⟨hiff, hscan_m⟩ := run_eq_of_init_eq_of_scansBelow hinit hscan
    have hrun_m : M.run m (T n) = .inl (f n) := (hiff (f n)).mpr (hM n)
    have h1 := Machine.run_add hrun_m (T m)
    have h2 := Machine.run_add (hM m) (T n)
    rw [Nat.add_comm] at h2
    have hsum : (.inl (f n) : Bool ⊕ Cfg M) = .inl (f m) := h1.symm.trans h2
    injection hsum with hfeq
    exact ⟨hrun_m, hfeq.symm, hscan_m⟩

/-- **Dyadic ray constancy and halting collapse under `ScansBelow`.** If `M` computes `f` in time `T`
and keeps its head below cell `k` (`ScansBelow M n (T n) k`) on a single input `n ≥ 2^(k-1)`, then
for every `u ≥ 1`, on the ray element `m = n % 2^k + u * 2^k` the machine halts within `T n` steps
(`M.run m (T n) = .inl (f n)`) and `f m = f n`. -/
theorem computes_const_on_dyadic_ray_of_scansBelow {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k n : Nat} (hn : 2 ^ (k - 1) ≤ n)
    (hscan : ScansBelow M n (T n) (k : Int)) (u : Nat) (hu : 1 ≤ u) :
    M.run (n % 2 ^ k + u * 2 ^ k) (T n) = .inl (f n) ∧
      f (n % 2 ^ k + u * 2 ^ k) = f n := by
  have hm : 2 ^ (k - 1) ≤ n % 2 ^ k + u * 2 ^ k := by
    have h1 : 2 ^ (k - 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (Nat.sub_le k 1)
    have h2 : 1 * 2 ^ k ≤ u * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) hu
    omega
  have hmod : (n % 2 ^ k + u * 2 ^ k) % 2 ^ k = n % 2 ^ k := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
  obtain ⟨hrun, hfeq, _⟩ := computes_eq_of_mod_two_pow_of_scansBelow hM hm hn hmod hscan
  exact ⟨hrun, hfeq⟩

/-- **Residue-flip right-head lower bound (arbitrary halting time `T`).** If `M` computes `f` in
time `T` and two inputs `r, m ≥ 2^(k-1)` in the same residue class modulo `2^k` satisfy `f r ≠ f m`,
then on *every* input `n ≥ 2^(k-1)` in that residue class, `M`'s head must reach cell `k` or higher
before halting—no matter how many steps `T n` or negative worktape cells `i < 0` it uses. -/
theorem exists_head_ge_of_mod_two_pow_ne {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k r m n : Nat}
    (hr : 2 ^ (k - 1) ≤ r) (hm : 2 ^ (k - 1) ≤ m) (hn : 2 ^ (k - 1) ≤ n)
    (hrm : r % 2 ^ k = m % 2 ^ k) (hneq : f r ≠ f m) (hrn : r % 2 ^ k = n % 2 ^ k) :
    ∃ s < T n, ∃ c, M.run n s = .inr c ∧ (k : Int) ≤ c.head := by
  refine Classical.byContradiction fun hno => ?_
  have hscan : ScansBelow M n (T n) (k : Int) := fun s hs c hc =>
    Int.lt_of_not_ge fun hge => hno ⟨s, hs, c, hc, hge⟩
  have e1 := (computes_eq_of_mod_two_pow_of_scansBelow hM hr hn hrn hscan).2.1
  have e2 := (computes_eq_of_mod_two_pow_of_scansBelow hM hm hn (hrm.symm.trans hrn) hscan).2.1
  exact hneq (e1.trans e2.symm)

/-- **Residue-flip lower bound on `RightSpan`.** Under the hypotheses of
`exists_head_ge_of_mod_two_pow_ne`, `k + 1 ≤ RightSpan M n (T n)`. -/
theorem k_lt_rightSpan_of_mod_two_pow_ne {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k r m n : Nat}
    (hr : 2 ^ (k - 1) ≤ r) (hm : 2 ^ (k - 1) ≤ m) (hn : 2 ^ (k - 1) ≤ n)
    (hrm : r % 2 ^ k = m % 2 ^ k) (hneq : f r ≠ f m) (hrn : r % 2 ^ k = n % 2 ^ k) :
    k + 1 ≤ RightSpan M n (T n) := by
  refine Classical.byContradiction fun hlt => ?_
  have hle : RightSpan M n (T n) ≤ k := by omega
  have hscan : ScansBelow M n (T n) (k : Int) := scansBelow_iff_rightSpan_le.mpr hle
  obtain ⟨s, hs, c, hc, hge⟩ := exists_head_ge_of_mod_two_pow_ne hM hr hm hn hrm hneq hrn
  have := hscan s hs c hc
  omega

/-- **Blank-reach right-head lower bound (arbitrary halting time `T`).** For any `n ≥ 1`, let
`L = Nat.log2 n + 1` be the binary length of `n`. If `f (n + u * 2^L) ≠ f n` for some `u`, then
every machine `M` computing `f` in time `T` must move its head onto the blank cell `L` beyond the
most significant bit of `n` (`∃ s < T n, ∃ c, M.run n s = .inr c ∧ (Nat.log2 n + 1 : Int) ≤ c.head`). -/
theorem exists_head_gt_log2_of_ray_flip {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {n u : Nat} (hn : 1 ≤ n)
    (hflip : f (n + u * 2 ^ (Nat.log2 n + 1)) ≠ f n) :
    ∃ s < T n, ∃ c, M.run n s = .inr c ∧ (Nat.log2 n + 1 : Int) ≤ c.head := by
  let L := Nat.log2 n + 1
  have hpow : 2 ^ (L - 1) ≤ n := Nat.log2_self_le (by omega)
  have hpow2 : 2 ^ (L - 1) ≤ n + u * 2 ^ L := Nat.le_trans hpow (Nat.le_add_right n (u * 2 ^ L))
  have hmod : (n + u * 2 ^ L) % 2 ^ L = n % 2 ^ L := Nat.add_mul_mod_self_right n u (2 ^ L)
  exact exists_head_ge_of_mod_two_pow_ne hM hpow2 hpow hpow hmod hflip (hmod.trans rfl)

/-- **Blank-reach `RightSpan` lower bound.** If `n ≥ 1` and `f (n + u * 2^(Nat.log2 n + 1)) ≠ f n`,
then `Nat.log2 n + 2 ≤ RightSpan M n (T n)` for every machine `M` computing `f` in time `T`. -/
theorem log2_succ_lt_rightSpan_of_ray_flip {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {n u : Nat} (hn : 1 ≤ n)
    (hflip : f (n + u * 2 ^ (Nat.log2 n + 1)) ≠ f n) :
    Nat.log2 n + 2 ≤ RightSpan M n (T n) := by
  let L := Nat.log2 n + 1
  have hpow : 2 ^ (L - 1) ≤ n := Nat.log2_self_le (by omega)
  have hpow2 : 2 ^ (L - 1) ≤ n + u * 2 ^ L := Nat.le_trans hpow (Nat.le_add_right n (u * 2 ^ L))
  have hmod : (n + u * 2 ^ L) % 2 ^ L = n % 2 ^ L := Nat.add_mul_mod_self_right n u (2 ^ L)
  exact k_lt_rightSpan_of_mod_two_pow_ne hM hpow2 hpow hpow hmod hflip (hmod.trans rfl)

/-- **Canonical-window right-head periodicity and halting-time collapse.** If `M` computes `f` in
time `T` and its head stays below cell `k` (`ScansBelow M r (T r) k`) on the canonical window
`r ∈ [2^(k-1), 2^(k-1) + 2^k)`, then `f` has global period `2^k` from `2^(k-1)` onward *and* on
every input `m ≥ 2^(k-1)` the machine halts within `T (canonRep k m)` steps. -/
theorem period_and_halt_of_canon_window_scansBelow {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k : Nat}
    (hwin : ∀ r, 2 ^ (k - 1) ≤ r → r < 2 ^ (k - 1) + 2 ^ k → ScansBelow M r (T r) (k : Int)) :
    (∀ m, 2 ^ (k - 1) ≤ m → f (m + 2 ^ k) = f m) ∧
      (∀ m, 2 ^ (k - 1) ≤ m → M.run m (T (canonRep k m)) = .inl (f m)) := by
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · let r := canonRep k m
    obtain ⟨_, hr1, hmod⟩ := canonRep_spec hm
    have hr2 : r < 2 ^ (k - 1) + 2 ^ k := canonRep_lt
    have hscan : ScansBelow M r (T r) (k : Int) := hwin r hr1 hr2
    have hmod1 : m % 2 ^ k = r % 2 ^ k := hmod.symm
    have hmod2 : (m + 2 ^ k) % 2 ^ k = r % 2 ^ k := by rw [Nat.add_mod_right, hmod1]
    have e1 := (computes_eq_of_mod_two_pow_of_scansBelow hM hm hr1 hmod1 hscan).2.1
    have e2 := (computes_eq_of_mod_two_pow_of_scansBelow hM (by omega) hr1 hmod2 hscan).2.1
    exact e2.trans e1.symm
  · let r := canonRep k m
    obtain ⟨_, hr1, hmod⟩ := canonRep_spec hm
    have hr2 : r < 2 ^ (k - 1) + 2 ^ k := canonRep_lt
    have hscan : ScansBelow M r (T r) (k : Int) := hwin r hr1 hr2
    obtain ⟨hrun, hfeq, _⟩ := computes_eq_of_mod_two_pow_of_scansBelow hM hm hr1 hmod.symm hscan
    rwa [← hfeq] at hrun

/-- **Full step-by-step configuration and negative-worktape collapse to the canonical root.** If
`ScansBelow M r (T r) k` holds on the canonical window `r ∈ [2^(k-1), 2^(k-1) + 2^k)`, then for
every input `m ≥ 2^(k-1)` (`k ≥ 1`) and every step `s ≤ T (canonRep k m)`, the run on `m` matches
the run on `r = canonRep k m` in state, head position, and tape contents across all cells `i < k`
(including the entire negative half-tape `i < 0`). -/
theorem run_congr_canonRep_of_canon_window_scansBelow {M : Machine} {T : Nat → Nat} {k : Nat}
    (hwin : ∀ r, 2 ^ (k - 1) ≤ r → r < 2 ^ (k - 1) + 2 ^ k → ScansBelow M r (T r) (k : Int))
    {m s : Nat} (hm : 2 ^ (k - 1) ≤ m) (hs : s ≤ T (canonRep k m)) :
    match M.run m s, M.run (canonRep k m) s with
    | .inl b₁, .inl b₂ => b₁ = b₂
    | .inr c₁, .inr c₂ =>
        c₁.state = c₂.state ∧ c₁.head = c₂.head ∧ ∀ i : Int, i < k → c₁.tape i = c₂.tape i
    | _, _ => False := by
  let r := canonRep k m
  obtain ⟨_, hr1, hmod⟩ := canonRep_spec hm
  have hr2 : r < 2 ^ (k - 1) + 2 ^ k := canonRep_lt
  have hscan : ScansBelow M r s (k : Int) := (hwin r hr1 hr2).mono hs
  have hinit : ∀ i : Int, 0 ≤ i → i < k → (M.init m).tape i = (M.init r).tape i :=
    fun i hi0 hik => init_tape_eq_of_mod_two_pow_eq M hm hr1 hmod.symm i hi0 hik
  exact run_congr_of_scansBelow hinit s hscan

/-- **Eventual right-head bound forces fixed-transient periodicity `2^k`.** If `M` computes `f` in
time `T` and `ScansBelow M n (T n) k` holds for all `n ≥ N`, then `f` has period `2^k` from the
fixed threshold `2^(k-1)` onward. -/
theorem period_of_eventually_scansBelow {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {k N : Nat}
    (hscan : ∀ n, N ≤ n → ScansBelow M n (T n) (k : Int)) :
    ∀ m, 2 ^ (k - 1) ≤ m → f (m + 2 ^ k) = f m := by
  refine (period_and_halt_of_canon_window_scansBelow hM fun r hr1 _ => ?_).1
  by_cases hk : k = 0
  · subst hk
    exfalso
    have hN := hscan N (Nat.le_refl N)
    have h0 : M.run N 0 = .inr (M.init N) := rfl
    rcases Nat.eq_zero_or_pos (T N) with hT0 | hTpos
    · have h := hM N; rw [hT0] at h; cases h
    · have hlt := hN 0 hTpos (M.init N) h0
      simp [Machine.init] at hlt
  · let w := r + N * 2 ^ k
    have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hwN : N ≤ w := by
      have : N * 1 ≤ N * 2 ^ k := Nat.mul_le_mul_left N h2k
      omega
    have hmod : r % 2 ^ k = w % 2 ^ k := (Nat.add_mul_mod_self_right r N (2 ^ k)).symm
    have hw_scan : ScansBelow M w (T w) (k : Int) := hscan w hwN
    obtain ⟨hrun_r, _, hscan_r⟩ :=
      computes_eq_of_mod_two_pow_of_scansBelow hM hr1 (by omega) hmod hw_scan
    intro s hs c hc
    by_cases hs_lt : s < T w
    · exact hscan_r s hs_lt c hc
    · exfalso
      have hadd := Machine.run_add hrun_r (s - T w)
      rw [Nat.add_sub_cancel' (by omega), hc] at hadd
      cases hadd

/-- **`Problem1` implies unbounded right-head excursion.** Under `Problem1`, for every `k` and `N`,
every machine `M` computing `center` in time `T` must move its head to cell `k` or higher on some
input `n ≥ N`. -/
theorem head_unbounded_of_problem1 (hP1 : Problem1) {M : Machine} {T : Nat → Nat}
    (hM : Computes M center T) (k N : Nat) :
    ∃ n, N ≤ n ∧ ∃ s < T n, ∃ c, M.run n s = .inr c ∧ (k : Int) ≤ c.head := by
  refine Classical.byContradiction fun hno => ?_
  have hscan : ∀ n, N ≤ n → ScansBelow M n (T n) (k : Int) := fun n hn s hs c hc =>
    Int.lt_of_not_ge fun hge => hno ⟨n, hn, s, hs, c, hc, hge⟩
  have hper := period_of_eventually_scansBelow hM hscan
  exact hP1 ⟨2 ^ (k - 1), 2 ^ k, Nat.two_pow_pos k, hper⟩

/-- **Unconditional canonical-window right-head lower bound on left diagonals.** For every
`k : Nat`, there exists a left diagonal `D j` (`j ≤ 2 ^ (2 * 2 ^ k)`) such that every machine `M`
computing `D j` in *any* time `T` must move its head to cell `k` or higher on some input `r` in the
canonical window `[2^(k-1), 2^(k-1) + 2^k)`. -/
theorem diagonal_canon_window_head_ge (k : Nat) :
    ∃ j ≤ 2 ^ (2 * 2 ^ k), ∀ (M : Machine) (T : Nat → Nat), Computes M (D j) T →
      ∃ r, 2 ^ (k - 1) ≤ r ∧ r < 2 ^ (k - 1) + 2 ^ k ∧
        ∃ s < T r, ∃ c, M.run r s = .inr c ∧ (k : Int) ≤ c.head := by
  obtain ⟨j, hj, hnot⟩ := D_period_unbounded (2 ^ k) (Nat.two_pow_pos k)
  refine ⟨j, hj, fun M T hM => Classical.byContradiction fun hno => ?_⟩
  have hwin : ∀ r, 2 ^ (k - 1) ≤ r → r < 2 ^ (k - 1) + 2 ^ k → ScansBelow M r (T r) (k : Int) :=
    fun r hr1 hr2 s hs c hc =>
      Int.lt_of_not_ge fun hge => hno ⟨r, hr1, hr2, s, hs, c, hc, hge⟩
  have hper := (period_and_halt_of_canon_window_scansBelow hM hwin).1
  exact hnot ⟨2 ^ (k - 1), fun m hm => by simpa [Nat.add_comm] using hper m hm⟩

/-- **Unconditional canonical-window `RightSpan` lower bound on left diagonals.** For every
`k : Nat`, there exists a left diagonal `D j` (`j ≤ 2 ^ (2 * 2 ^ k)`) such that every machine `M`
computing `D j` in *any* time `T` satisfies `k + 1 ≤ RightSpan M r (T r)` on some canonical root
`r ∈ [2^(k-1), 2^(k-1) + 2^k)`. -/
theorem diagonal_canon_window_rightSpan_ge (k : Nat) :
    ∃ j ≤ 2 ^ (2 * 2 ^ k), ∀ (M : Machine) (T : Nat → Nat), Computes M (D j) T →
      ∃ r, 2 ^ (k - 1) ≤ r ∧ r < 2 ^ (k - 1) + 2 ^ k ∧ k + 1 ≤ RightSpan M r (T r) := by
  obtain ⟨j, hj, hdiag⟩ := diagonal_canon_window_head_ge k
  refine ⟨j, hj, fun M T hM => ?_⟩
  obtain ⟨r, hr1, hr2, s, hs, c, hc, hge⟩ := hdiag M T hM
  refine ⟨r, hr1, hr2, Classical.byContradiction fun hlt => ?_⟩
  have hscan : ScansBelow M r (T r) (k : Int) := scansBelow_iff_rightSpan_le.mpr (by omega)
  have := hscan s hs c hc
  omega

/-! ## 1. Unvisited-cell tape invariance and left/right exterior rays -/

/-- A single head move decreases the head position by at most `1`. -/
theorem pred_le_move_apply (d : Move) (h : Int) : h - 1 ≤ d.apply h := by
  cases d <;> simp [Move.apply] <;> omega

/-- After `s` steps from `head = 0`, any active configuration `c` satisfies `-(s : Int) ≤ c.head`. -/
theorem run_neg_steps_le_head {M : Machine} {n : Nat} :
    ∀ {s : Nat} {c : Cfg M}, M.run n s = .inr c → -(s : Int) ≤ c.head
  | 0, c, hc => by
    injection hc with h
    subst h
    simp [Machine.init]
  | s + 1, c, hc => by
    simp only [Machine.run] at hc
    cases hr : M.run n s with
    | inl b => rw [hr] at hc; cases hc
    | inr c₀ =>
      rw [hr] at hc
      dsimp only at hc
      have ih := run_neg_steps_le_head hr
      unfold Cfg.step at hc
      cases hδ : M.δ c₀.state (c₀.tape c₀.head) with
      | inl b => rw [hδ] at hc; cases hc
      | inr val =>
        rcases val with ⟨p, a, d⟩
        rw [hδ] at hc
        injection hc with h
        subst h
        have hm := pred_le_move_apply d c₀.head
        dsimp only
        omega

/-- During the first `t` steps on input `n`, `M`'s head remains at or to the right of cell `L`. -/
def ScansAbove (M : Machine) (n t : Nat) (L : Int) : Prop :=
  ∀ s, s < t → ∀ c, M.run n s = .inr c → L ≤ c.head

/-- Monotonicity of `ScansAbove` in the step horizon `t`. -/
theorem ScansAbove.mono {M : Machine} {n t₁ t₂ : Nat} {L : Int}
    (h : ScansAbove M n t₂ L) (ht : t₁ ≤ t₂) : ScansAbove M n t₁ L :=
  fun s hs c hc => h s (Nat.lt_of_lt_of_le hs ht) c hc

/-- Any run of length `t ≤ k` from `head = 0` automatically satisfies `ScansAbove M n t (-(k : Int))`. -/
theorem scansAbove_neg_of_le {M : Machine} {n t k : Nat} (ht : t ≤ k) :
    ScansAbove M n t (-(k : Int)) := by
  intro s hs c hc
  have hle := run_neg_steps_le_head hc
  omega

/-- **Unvisited-cell tape invariance (`tape_eq_init_of_head_ne`).** If cell `i` is never visited by
the head during steps `0, …, t - 1`, then at step `t` cell `i` still holds its initial value
`(M.init n).tape i`. -/
theorem tape_eq_init_of_head_ne {M : Machine} {n : Nat} {i : Int} :
    ∀ {t : Nat} {c : Cfg M}, M.run n t = .inr c →
      (∀ s, s < t → ∀ c₀, M.run n s = .inr c₀ → c₀.head ≠ i) →
      c.tape i = (M.init n).tape i
  | 0, c, hc, _ => by
    injection hc with h
    subst h
    rfl
  | t + 1, c, hc, hne => by
    simp only [Machine.run] at hc
    cases hr : M.run n t with
    | inl b => rw [hr] at hc; cases hc
    | inr c₀ =>
      rw [hr] at hc
      dsimp only at hc
      have ih := tape_eq_init_of_head_ne hr (fun s hs c' hc' => hne s (by omega) c' hc')
      have hne_t : i ≠ c₀.head := Ne.symm (hne t (Nat.lt_succ_self t) c₀ hr)
      unfold Cfg.step at hc
      cases hδ : M.δ c₀.state (c₀.tape c₀.head) with
      | inl b => rw [hδ] at hc; cases hc
      | inr val =>
        rcases val with ⟨p, a, d⟩
        rw [hδ] at hc
        injection hc with h
        subst h
        dsimp only
        rw [ite_eq_right (fun h => hne_t h), ih]

/-- **Right exterior ray invariance (`tape_eq_init_of_scansBelow`).** Under `ScansBelow M n t B`,
every cell `i ≥ B` at step `t` still equals `(M.init n).tape i`. -/
theorem tape_eq_init_of_scansBelow {M : Machine} {n t : Nat} {B : Int} {c : Cfg M}
    (hr : M.run n t = .inr c) (hscan : ScansBelow M n t B) :
    ∀ i : Int, B ≤ i → c.tape i = (M.init n).tape i := by
  intro i hi
  refine tape_eq_init_of_head_ne hr (fun s hs c₀ hc₀ => ?_)
  have hlt := hscan s hs c₀ hc₀
  omega

/-- **Left exterior blank ray invariance (`tape_eq_zero_of_scansAbove`).** Under `ScansAbove M n t L`
with `L ≤ 0`, every cell `i < L` at step `t` is still blank (`0`). -/
theorem tape_eq_zero_of_scansAbove {M : Machine} {n t : Nat} {L : Int} {c : Cfg M}
    (hr : M.run n t = .inr c) (hscan : ScansAbove M n t L) (hL : L ≤ 0) :
    ∀ i : Int, i < L → c.tape i = ⟨0, by omega⟩ := by
  intro i hi
  rw [tape_eq_init_of_head_ne hr (fun s hs c₀ hc₀ => by have := hscan s hs c₀ hc₀; omega)]
  exact init_tape_neg M n (by omega)

/-! ## 2. Finite-box tape agreement and deterministic configuration-repeat periodicity -/

/-- **Finite-box tape agreement implies full infinite-tape agreement (`tape_eq_all_of_box_eq`).**
If the head stays inside `[L, B)` up to `t₂` (`t₁ ≤ t₂`), and the configurations `c₁` (at `t₁`) and
`c₂` (at `t₂`) agree on the finite box `L ≤ i < B`, then `c₁.tape i = c₂.tape i` for all `i : Int`. -/
theorem tape_eq_all_of_box_eq {M : Machine} {n t₁ t₂ : Nat} {L B : Int} {c₁ c₂ : Cfg M}
    (ht : t₁ ≤ t₂) (hr₁ : M.run n t₁ = .inr c₁) (hr₂ : M.run n t₂ = .inr c₂)
    (habove : ScansAbove M n t₂ L) (hbelow : ScansBelow M n t₂ B)
    (hbox : ∀ i : Int, L ≤ i → i < B → c₁.tape i = c₂.tape i) :
    ∀ i : Int, c₁.tape i = c₂.tape i := by
  intro i
  by_cases hL : i < L
  · have h1 := tape_eq_init_of_head_ne (i := i) hr₁ (fun s hs c₀ hc₀ => by
      have hle : L ≤ c₀.head := (habove.mono ht) s hs c₀ hc₀; omega)
    have h2 := tape_eq_init_of_head_ne (i := i) hr₂ (fun s hs c₀ hc₀ => by
      have hle : L ≤ c₀.head := habove s hs c₀ hc₀; omega)
    rw [h1, h2]
  · by_cases hB : i < B
    · exact hbox i (by omega) hB
    · have h1 := tape_eq_init_of_scansBelow hr₁ (hbelow.mono ht) i (by omega)
      have h2 := tape_eq_init_of_scansBelow hr₂ hbelow i (by omega)
      rw [h1, h2]

/-- If two configurations `c₁` and `c₂` have identical state, head, and tape on all of `Int`, then
`c₁.step = c₂.step` (with identical state, head, and tape if still running). -/
theorem step_congr_all {M : Machine} {c₁ c₂ : Cfg M}
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head) (ht : ∀ i : Int, c₁.tape i = c₂.tape i) :
    (∃ b, c₁.step = .inl b ∧ c₂.step = .inl b) ∨
      ∃ c₁' c₂', c₁.step = .inr c₁' ∧ c₂.step = .inr c₂' ∧
        c₁'.state = c₂'.state ∧ c₁'.head = c₂'.head ∧ (∀ i : Int, c₁'.tape i = c₂'.tape i) := by
  have hread : c₁.tape c₁.head = c₂.tape c₂.head := by rw [← hh, ht]
  unfold Cfg.step
  rw [hs, hread]
  cases hδ : M.δ c₂.state (c₂.tape c₂.head) with
  | inl b => exact Or.inl ⟨b, rfl, rfl⟩
  | inr val =>
    rcases val with ⟨p, a, d⟩
    refine Or.inr ⟨_, _, rfl, rfl, rfl, by rw [hh], fun i => ?_⟩
    dsimp only
    rw [hh]
    by_cases hih : i = c₂.head
    · simp [hih]
    · simp [hih, ht i]

/-- If `M.run n s₁` and `M.run n s₂` are in configurations with identical state, head, and tape,
then after `d` additional steps they remain in identical outcomes/configurations. -/
theorem run_shift_congr_all {M : Machine} {n : Nat} :
    ∀ (d s₁ s₂ : Nat) {c₁ c₂ : Cfg M},
      M.run n s₁ = .inr c₁ → M.run n s₂ = .inr c₂ →
      c₁.state = c₂.state → c₁.head = c₂.head → (∀ i : Int, c₁.tape i = c₂.tape i) →
      match M.run n (s₁ + d), M.run n (s₂ + d) with
      | .inl b₁, .inl b₂ => b₁ = b₂
      | .inr c₁', .inr c₂' =>
          c₁'.state = c₂'.state ∧ c₁'.head = c₂'.head ∧ ∀ i : Int, c₁'.tape i = c₂'.tape i
      | _, _ => False
  | 0, s₁, s₂, c₁, c₂, h1, h2, hs, hh, ht => by
    rw [Nat.add_zero, Nat.add_zero, h1, h2]
    exact ⟨hs, hh, ht⟩
  | d + 1, s₁, s₂, c₁, c₂, h1, h2, hs, hh, ht => by
    have ih := run_shift_congr_all d s₁ s₂ h1 h2 hs hh ht
    rw [show s₁ + (d + 1) = (s₁ + d) + 1 by omega, show s₂ + (d + 1) = (s₂ + d) + 1 by omega]
    simp only [Machine.run]
    cases hr₁ : M.run n (s₁ + d) with
    | inl b₁ =>
      cases hr₂ : M.run n (s₂ + d) with
      | inl b₂ => rw [hr₁, hr₂] at ih; exact ih
      | inr c₂' => rw [hr₁, hr₂] at ih; exact False.elim ih
    | inr c₁' =>
      cases hr₂ : M.run n (s₂ + d) with
      | inl b₂ => rw [hr₁, hr₂] at ih; exact False.elim ih
      | inr c₂' =>
        rw [hr₁, hr₂] at ih
        obtain ⟨hs', hh', ht'⟩ := ih
        rcases step_congr_all hs' hh' ht' with ⟨b, hb₁, hb₂⟩ | ⟨c₁'', c₂'', hc₁'', hc₂'', hst, hhd, htp⟩
        · dsimp only; rw [hb₁, hb₂]
        · dsimp only; rw [hc₁'', hc₂'']; exact ⟨hst, hhd, htp⟩

/-- **Finite-box repeat periodicity (`run_periodic_of_box_repeat`).** If the head stays inside
`[L, B)` up to `t₁ + p`, and the configurations at `t₁` and `t₁ + p` agree on `state`, `head`, and
the finite box `L ≤ i < B`, then for every `k, d : Nat`, `M.run n (t₁ + d + k * p)` is active with
the exact same `state`, `head`, and `tape` as `M.run n (t₁ + d)`. -/
theorem run_periodic_of_box_repeat {M : Machine} {n t₁ p : Nat} {L B : Int} {c₁ c₂ : Cfg M}
    (hr₁ : M.run n t₁ = .inr c₁) (hr₂ : M.run n (t₁ + p) = .inr c₂)
    (habove : ScansAbove M n (t₁ + p) L) (hbelow : ScansBelow M n (t₁ + p) B)
    (hst : c₁.state = c₂.state) (hhd : c₁.head = c₂.head)
    (hbox : ∀ i : Int, L ≤ i → i < B → c₁.tape i = c₂.tape i) :
    ∀ k d,
      match M.run n (t₁ + d), M.run n (t₁ + d + k * p) with
      | .inl b₁, .inl b₂ => b₁ = b₂
      | .inr c, .inr c' => c.state = c'.state ∧ c.head = c'.head ∧ ∀ i : Int, c.tape i = c'.tape i
      | _, _ => False := by
  have htall := tape_eq_all_of_box_eq (by omega) hr₁ hr₂ habove hbelow hbox
  intro k
  induction k with
  | zero =>
    intro d
    simp only [Nat.zero_mul, Nat.add_zero]
    cases M.run n (t₁ + d) <;> simp
  | succ k ih =>
    intro d
    have hstep := run_shift_congr_all (d + k * p) t₁ (t₁ + p) hr₁ hr₂ hst hhd htall
    rw [show t₁ + (d + k * p) = t₁ + d + k * p by omega, show t₁ + p + (d + k * p) = t₁ + d + (k + 1) * p by rw [Nat.succ_mul]; omega] at hstep
    have ih_d := ih d
    cases h0 : M.run n (t₁ + d) <;>
      cases h1 : M.run n (t₁ + d + k * p) <;>
      cases h2 : M.run n (t₁ + d + (k + 1) * p) <;>
      rw [h0, h1] at ih_d <;> rw [h1, h2] at hstep
    · exact Eq.trans ih_d hstep
    · exact False.elim hstep
    · exact False.elim ih_d
    · exact False.elim ih_d
    · exact False.elim ih_d
    · exact False.elim ih_d
    · exact False.elim hstep
    · exact ⟨Eq.trans ih_d.1 hstep.1, Eq.trans ih_d.2.1 hstep.2.1,
        fun i => Eq.trans (ih_d.2.2 i) (hstep.2.2 i)⟩

/-- If `M.run n (t₁ + p) = .inr c₂`, then for every `d ≤ p`, `M.run n (t₁ + d)` is also `.inr c`
for some active configuration `c`. -/
theorem run_inr_of_le {M : Machine} {n s t : Nat} {c₂ : Cfg M}
    (hst : s ≤ t) (hr : M.run n t = .inr c₂) : ∃ c₁, M.run n s = .inr c₁ := by
  cases hs : M.run n s with
  | inr c₁ => exact ⟨c₁, rfl⟩
  | inl b =>
    have hadd := Machine.run_add hs (t - s)
    rw [show s + (t - s) = t by omega, hr] at hadd
    cases hadd

/-- **Infinite-time non-halting and spatial trapping (`not_halts_and_trapped_of_box_repeat`).**
If `M` repeats its state, head, and finite-box `[L, B)` tape at `t₁` and `t₁ + p` (`0 < p`) while
staying inside `[L, B)` up to `t₁ + p`, then `M` NEVER halts on input `n` and its head remains
trapped inside `[L, B)` for ALL `t : Nat`. -/
theorem not_halts_and_trapped_of_box_repeat {M : Machine} {n t₁ p : Nat} {L B : Int} {c₁ c₂ : Cfg M}
    (hp : 0 < p) (hr₁ : M.run n t₁ = .inr c₁) (hr₂ : M.run n (t₁ + p) = .inr c₂)
    (habove : ScansAbove M n (t₁ + p) L) (hbelow : ScansBelow M n (t₁ + p) B)
    (hst : c₁.state = c₂.state) (hhd : c₁.head = c₂.head)
    (hbox : ∀ i : Int, L ≤ i → i < B → c₁.tape i = c₂.tape i) :
    (∀ t b, M.run n t ≠ .inl b) ∧ (∀ t, ScansAbove M n t L ∧ ScansBelow M n t B) := by
  have hper := run_periodic_of_box_repeat hr₁ hr₂ habove hbelow hst hhd hbox
  have hactive : ∀ s, ∃ c, M.run n s = .inr c ∧ L ≤ c.head ∧ c.head < B := by
    intro s
    by_cases hs : s < t₁ + p
    · obtain ⟨c, hc⟩ := run_inr_of_le (s := s) (t := t₁ + p) (by omega) hr₂
      exact ⟨c, hc, habove s hs c hc, hbelow s hs c hc⟩
    · let d := (s - t₁) % p
      let k := (s - t₁) / p
      have hdiv : (s - t₁) % p + p * ((s - t₁) / p) = s - t₁ := Nat.mod_add_div (s - t₁) p
      have hs_eq : s = t₁ + d + k * p := by
        dsimp only [d, k]
        rw [Nat.mul_comm] at hdiv
        omega
      have hd_lt : d < p := Nat.mod_lt (s - t₁) hp
      obtain ⟨c₀, hc₀⟩ := run_inr_of_le (s := t₁ + d) (t := t₁ + p) (by omega) hr₂
      have hp_kd := hper k d
      rw [← hs_eq, hc₀] at hp_kd
      cases hrun : M.run n s with
      | inl b => rw [hrun] at hp_kd; exact False.elim hp_kd
      | inr c =>
        rw [hrun] at hp_kd
        have hL : L ≤ c₀.head := habove (t₁ + d) (by omega) c₀ hc₀
        have hB : c₀.head < B := hbelow (t₁ + d) (by omega) c₀ hc₀
        rw [hp_kd.2.1] at hL hB
        exact ⟨c, rfl, hL, hB⟩
  refine ⟨fun t b h => ?_, fun t => ⟨fun s _ c hc => ?_, fun s _ c hc => ?_⟩⟩
  · obtain ⟨c, hc, _, _⟩ := hactive t
    rw [hc] at h; cases h
  · obtain ⟨c', hc', hL, _⟩ := hactive s
    rw [hc] at hc'; injection hc' with heq; subst heq; exact hL
  · obtain ⟨c', hc', _, hB⟩ := hactive s
    rw [hc] at hc'; injection hc' with heq; subst heq; exact hB

/-- **Dyadic ray non-halting and trapping (`not_halts_dyadic_ray_of_box_repeat`).** If `M` has a
finite-box repeat inside `[L, B)` (`1 ≤ B`) at `t₁` and `t₁ + p` (`0 < p`) on `n ≥ 2 ^ (B - 1)`,
then for every `m ≥ 2 ^ (B - 1)` with `m % 2 ^ B = n % 2 ^ B`, `M` never halts on `m` and stays
below `B` for all `t : Nat`. -/
theorem not_halts_dyadic_ray_of_box_repeat {M : Machine} {n m t₁ p B : Nat} {L : Int} {c₁ c₂ : Cfg M}
    (hp : 0 < p) (hn : 2 ^ (B - 1) ≤ n) (hm : 2 ^ (B - 1) ≤ m)
    (hmod : m % 2 ^ B = n % 2 ^ B)
    (hr₁ : M.run n t₁ = .inr c₁) (hr₂ : M.run n (t₁ + p) = .inr c₂)
    (habove : ScansAbove M n (t₁ + p) L) (hbelow : ScansBelow M n (t₁ + p) (B : Int))
    (hst : c₁.state = c₂.state) (hhd : c₁.head = c₂.head)
    (hbox : ∀ i : Int, L ≤ i → i < (B : Int) → c₁.tape i = c₂.tape i) :
    (∀ t b, M.run m t ≠ .inl b) ∧ (∀ t, ScansBelow M m t (B : Int)) := by
  obtain ⟨hnh_n, htrap_n⟩ :=
    not_halts_and_trapped_of_box_repeat hp hr₁ hr₂ habove hbelow hst hhd hbox
  have hinit := init_tape_eq_of_mod_two_pow_eq M hm hn hmod
  refine ⟨fun t b h => ?_, fun t => (run_eq_of_init_eq_of_scansBelow hinit (htrap_n t).2).2⟩
  have heq := (run_eq_of_init_eq_of_scansBelow hinit (htrap_n t).2).1 b
  exact hnh_n t b (heq.mp h)

/-! ## 1. Unconditional `k ≤ 13` Canonical-Window and Infinitely-Often `RightSpan` Bounds for `center` -/

/-- For every `k ≤ 13`, `center` is not `2^k`-periodic from `2^(k-1)` onward (`2^(k-1) + 2^k ≤ 12288 < 16359`). -/
theorem not_center_period_two_pow_le_thirteen {k : Nat} (hk : k ≤ 13)
    (hper : ∀ m, 2 ^ (k - 1) ≤ m → center (m + 2 ^ k) = center m) : False := by
  have hwin : 16359 ≤ 2 ^ (k - 1) + 2 ^ k :=
    Rule30FactorWindow.transient_add_period_ge (2 ^ (k - 1)) (2 ^ k) (Nat.two_pow_pos k)
      fun t ht => hper t ht
  have h1 : 2 ^ (k - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ k ≤ 2 ^ 13 := Nat.pow_le_pow_right (by decide) hk
  have e12 : (2 : Nat) ^ 12 = 4096 := rfl
  have e13 : (2 : Nat) ^ 13 = 8192 := rfl
  omega

/-- **Unconditional Canonical-Window Step Lower Bound for `center` (`center_canon_window_time_ge`):**
for every `k ≤ 13` (without `Problem1`), every machine `M` computing `center` in time `T` takes at
least `k + 1` steps on some input `r` in the finite canonical window `[2^(k-1), 2^(k-1) + 2^k)`. -/
theorem center_canon_window_time_ge {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {k : Nat} (hk : k ≤ 13) :
    ∃ r, 2 ^ (k - 1) ≤ r ∧ r < 2 ^ (k - 1) + 2 ^ k ∧ k + 1 ≤ T r := by
  refine Classical.byContradiction fun hno => ?_
  have hwin : ∀ r, 2 ^ (k - 1) ≤ r → r < 2 ^ (k - 1) + 2 ^ k → T r ≤ k := fun r hr1 hr2 =>
    Nat.le_of_not_lt fun hlt => hno ⟨r, hr1, hr2, hlt⟩
  exact not_center_period_two_pow_le_thirteen hk (period_of_canon_window_time_le hM hwin)

/-- **Unconditional Canonical-Window Right-Head Lower Bound for `center` (`center_canon_window_head_ge`):**
for every `k ≤ 13` (without `Problem1`), every machine `M` computing `center` in *any* time `T` must
move its head to cell `k` or higher on some input `r` in `[2^(k-1), 2^(k-1) + 2^k)`. -/
theorem center_canon_window_head_ge {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {k : Nat} (hk : k ≤ 13) :
    ∃ r, 2 ^ (k - 1) ≤ r ∧ r < 2 ^ (k - 1) + 2 ^ k ∧
      ∃ s < T r, ∃ c, M.run r s = .inr c ∧ (k : Int) ≤ c.head := by
  refine Classical.byContradiction fun hno => ?_
  have hwin : ∀ r, 2 ^ (k - 1) ≤ r → r < 2 ^ (k - 1) + 2 ^ k → ScansBelow M r (T r) (k : Int) :=
    fun r hr1 hr2 s hs c hc =>
      Int.lt_of_not_ge fun hge => hno ⟨r, hr1, hr2, s, hs, c, hc, hge⟩
  exact not_center_period_two_pow_le_thirteen hk
    (period_and_halt_of_canon_window_scansBelow hM hwin).1

/-- **Unconditional Canonical-Window `RightSpan` Lower Bound for `center`
(`center_canon_window_rightSpan_ge`):** for every `k ≤ 13` (without `Problem1`), every machine `M`
computing `center` in *any* time `T` satisfies `k + 1 ≤ RightSpan M r (T r)` on some input `r` in
`[2^(k-1), 2^(k-1) + 2^k)`. -/
theorem center_canon_window_rightSpan_ge {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {k : Nat} (hk : k ≤ 13) :
    ∃ r, 2 ^ (k - 1) ≤ r ∧ r < 2 ^ (k - 1) + 2 ^ k ∧ k + 1 ≤ RightSpan M r (T r) := by
  obtain ⟨r, hr1, hr2, s, hs, c, hc, hge⟩ := center_canon_window_head_ge hM hk
  refine ⟨r, hr1, hr2, Classical.byContradiction fun hlt => ?_⟩
  have hscan : ScansBelow M r (T r) (k : Int) := scansBelow_iff_rightSpan_le.mpr (by omega)
  have := hscan s hs c hc
  omega

/-- **Unconditional Infinitely-Often Right-Head Excursion for `k ≤ 13` (`head_unbounded_le_thirteen`):**
for every `k ≤ 13` and every threshold `N : Nat` (without `Problem1`), every machine `M` computing
`center` in *any* time `T` moves its head to cell `k` or higher on some input `n ≥ N`. -/
theorem head_unbounded_le_thirteen {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {k : Nat} (hk : k ≤ 13) (N : Nat) :
    ∃ n, N ≤ n ∧ ∃ s < T n, ∃ c, M.run n s = .inr c ∧ (k : Int) ≤ c.head := by
  refine Classical.byContradiction fun hno => ?_
  have hscan : ∀ n, N ≤ n → ScansBelow M n (T n) (k : Int) := fun n hn s hs c hc =>
    Int.lt_of_not_ge fun hge => hno ⟨n, hn, s, hs, c, hc, hge⟩
  exact not_center_period_two_pow_le_thirteen hk (period_of_eventually_scansBelow hM hscan)

/-- **Unconditional Infinitely-Often `RightSpan` Bound for `k ≤ 13` (`rightSpan_unbounded_le_thirteen`):**
for every `k ≤ 13` and every threshold `N : Nat` (without `Problem1`), every machine `M` computing
`center` in *any* time `T` satisfies `k + 1 ≤ RightSpan M n (T n)` on some input `n ≥ N`. -/
theorem rightSpan_unbounded_le_thirteen {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {k : Nat} (hk : k ≤ 13) (N : Nat) :
    ∃ n, N ≤ n ∧ k + 1 ≤ RightSpan M n (T n) := by
  obtain ⟨n, hn, s, hs, c, hc, hge⟩ := head_unbounded_le_thirteen hM hk N
  refine ⟨n, hn, Classical.byContradiction fun hlt => ?_⟩
  have hscan : ScansBelow M n (T n) (k : Int) := scansBelow_iff_rightSpan_le.mpr (by omega)
  have := hscan s hs c hc
  omega

/-! ## 2. Uniform Spatial `RightSpan` Lower Bounds for All Inputs (`k = 1, 2, 3, 4` and `n < 16`) -/

/-- Generic converter from a verified `List.all` residue-flip check to a uniform spatial bound
`k + 1 ≤ RightSpan M n (T n)` for all `n ≥ 2^(k-1)`. -/
theorem rightSpan_gt_of_all_flip {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {k : Nat} (hall : (List.range' (2 ^ (k - 1)) (2 ^ k)).all
      (fun r => fastCenter r != fastCenter (r + flipWitness k r * 2 ^ k)) = true)
    {n : Nat} (hn : 2 ^ (k - 1) ≤ n) : k + 1 ≤ RightSpan M n (T n) := by
  obtain ⟨hmem, hr, hmod⟩ := canonRep_spec hn
  have hu := List.all_eq_true.mp hall (canonRep k n) hmem
  have hne : center (canonRep k n) ≠ center (canonRep k n + flipWitness k (canonRep k n) * 2 ^ k) := by
    rw [center_eq_fastCenter, center_eq_fastCenter]
    intro heq
    rw [heq, bne_self_eq_false] at hu
    exact Bool.noConfusion hu
  exact k_lt_rightSpan_of_mod_two_pow_ne hM hr (by omega) hn
    (by rw [Nat.add_mul_mod_self_right]) hne hmod

/-- **Unconditional `2`-Cell `RightSpan` Bound (`two_le_rightSpan`):** every machine computing
`center` satisfies `2 ≤ RightSpan M n (T n)` on every input `n ≥ 1`. -/
theorem two_le_rightSpan {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn : 1 ≤ n) : 2 ≤ RightSpan M n (T n) := by
  have h := dyadic_residues_flip_up_to_four
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact rightSpan_gt_of_all_flip hM (k := 1) h.1.1.1 hn

/-- **Unconditional `3`-Cell `RightSpan` Bound (`three_le_rightSpan`):** every machine computing
`center` satisfies `3 ≤ RightSpan M n (T n)` on every input `n ≥ 2`. -/
theorem three_le_rightSpan {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn : 2 ≤ n) : 3 ≤ RightSpan M n (T n) := by
  have h := dyadic_residues_flip_up_to_four
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact rightSpan_gt_of_all_flip hM (k := 2) h.1.1.2 hn

/-- **Unconditional `4`-Cell `RightSpan` Bound (`four_le_rightSpan`):** every machine computing
`center` satisfies `4 ≤ RightSpan M n (T n)` on every input `n ≥ 4`. -/
theorem four_le_rightSpan {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn : 4 ≤ n) : 4 ≤ RightSpan M n (T n) := by
  have h := dyadic_residues_flip_up_to_four
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact rightSpan_gt_of_all_flip hM (k := 3) h.1.2 hn

/-- **Unconditional `5`-Cell `RightSpan` Bound (`five_le_rightSpan`):** every machine computing
`center` satisfies `5 ≤ RightSpan M n (T n)` on every input `n ≥ 8`. -/
theorem five_le_rightSpan {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn : 8 ≤ n) : 5 ≤ RightSpan M n (T n) := by
  have h := dyadic_residues_flip_up_to_four
  rw [Bool.and_eq_true] at h
  exact rightSpan_gt_of_all_flip hM (k := 4) h.2 hn

/-- **Full-Input Spatial Scan Bound up to `n < 16` (`log2_succ_succ_le_rightSpan_lt_16`):** on every
input `1 ≤ n < 16`, every machine computing `center` satisfies `Nat.log2 n + 2 ≤ RightSpan M n (T n)`
(scanning all binary digits of `n` plus the first blank cell). -/
theorem log2_succ_succ_le_rightSpan_lt_16 {M : Machine} {T : Nat → Nat} (hM : Computes M center T)
    {n : Nat} (hn1 : 1 ≤ n) (hn16 : n < 16) : Nat.log2 n + 2 ≤ RightSpan M n (T n) := by
  by_cases h2 : n < 2
  · have hn : n = 1 := by omega
    have hlog : Nat.log2 n = 0 := by rw [hn]; rfl
    rw [hlog]; exact two_le_rightSpan hM hn1
  · by_cases h4 : n < 4
    · have hlog : Nat.log2 n = 1 := by
        rcases (show n = 2 ∨ n = 3 by omega) with rfl | rfl <;> rfl
      rw [hlog]; exact three_le_rightSpan hM (by omega)
    · by_cases h8 : n < 8
      · have hlog : Nat.log2 n = 2 := by
          rcases (show n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 by omega) with rfl | rfl | rfl | rfl <;> rfl
        rw [hlog]; exact four_le_rightSpan hM (by omega)
      · have hlog : Nat.log2 n = 3 := by
          have hge : 2 ^ 3 ≤ n := by omega
          have hlt : n < 2 ^ 4 := by omega
          exact Nat.le_antisymm (Nat.le_of_lt_succ ((Nat.log2_lt (by omega)).mpr hlt))
            ((Nat.le_log2 (by omega)).mpr hge)
        rw [hlog]; exact five_le_rightSpan hM (by omega)

/-! ## 3. Two-Time Head-Distance Bound and Bidirectional Excursion Turnaround Inequality -/

/-- A single head move changes the head position by at most `1` in either direction. -/
theorem move_apply_bounds (d : Move) (h : Int) : h - 1 ≤ d.apply h ∧ d.apply h ≤ h + 1 := by
  cases d <;> simp [Move.apply] <;> omega

/-- **General Two-Time Head-Distance Bound (`run_head_dist_le`):** if `M.run n s₁ = .inr c₁` and
`M.run n (s₁ + d) = .inr c₂`, then `c₁.head - d ≤ c₂.head ∧ c₂.head ≤ c₁.head + d`. -/
theorem run_head_dist_le {M : Machine} {n s₁ : Nat} {c₁ : Cfg M}
    (h1 : M.run n s₁ = .inr c₁) :
    ∀ {d : Nat} {c₂ : Cfg M}, M.run n (s₁ + d) = .inr c₂ →
      c₁.head - (d : Int) ≤ c₂.head ∧ c₂.head ≤ c₁.head + (d : Int)
  | 0, c₂, h2 => by
    rw [Nat.add_zero, h1] at h2
    injection h2 with h
    subst h
    omega
  | d + 1, c₂, h2 => by
    rw [show s₁ + (d + 1) = (s₁ + d) + 1 by omega] at h2
    simp only [Machine.run] at h2
    cases hr : M.run n (s₁ + d) with
    | inl b => rw [hr] at h2; cases h2
    | inr c₀ =>
      rw [hr] at h2
      dsimp only at h2
      have ih := run_head_dist_le h1 hr
      unfold Cfg.step at h2
      cases hδ : M.δ c₀.state (c₀.tape c₀.head) with
      | inl b => rw [hδ] at h2; cases h2
      | inr val =>
        rcases val with ⟨p, a, mv⟩
        rw [hδ] at h2
        injection h2 with h
        subst h
        have hm := move_apply_bounds mv c₀.head
        dsimp only
        omega

/-- **Bidirectional Excursion Turnaround Inequality (`time_ge_of_left_and_right_visit`):** if a run
of length `T` from `head = 0` visits a cell `c₁.head ≤ -(L : Int)` at step `s₁ < T` and visits a
cell `c₂.head ≥ (R : Int)` at step `s₂ < T`, then `(2 * L + R + 1 ≤ T) ∨ (2 * R + L + 1 ≤ T)`, and
in particular `L + R + min L R + 1 ≤ T`. -/
theorem time_ge_of_left_and_right_visit {M : Machine} {n s₁ s₂ T L R : Nat} {c₁ c₂ : Cfg M}
    (hs₁ : s₁ < T) (hs₂ : s₂ < T)
    (hr₁ : M.run n s₁ = .inr c₁) (hr₂ : M.run n s₂ = .inr c₂)
    (hL : c₁.head ≤ -(L : Int)) (hR : (R : Int) ≤ c₂.head) :
    ((2 * L + R + 1 ≤ T) ∨ (2 * R + L + 1 ≤ T)) ∧ L + R + min L R + 1 ≤ T := by
  have h0 : M.run n 0 = .inr (M.init n) := rfl
  have hinit_hd : (M.init n).head = 0 := rfl
  have hd₁ := run_head_dist_le h0 (show M.run n (0 + s₁) = .inr c₁ by simpa using hr₁)
  have hd₂ := run_head_dist_le h0 (show M.run n (0 + s₂) = .inr c₂ by simpa using hr₂)
  rw [hinit_hd] at hd₁ hd₂
  have hor : (2 * L + R + 1 ≤ T) ∨ (2 * R + L + 1 ≤ T) := by
    by_cases hle : s₁ ≤ s₂
    · left
      have h12 := run_head_dist_le hr₁ (show M.run n (s₁ + (s₂ - s₁)) = .inr c₂ by
        rwa [Nat.add_sub_cancel' hle])
      omega
    · right
      have h21 := run_head_dist_le hr₂ (show M.run n (s₂ + (s₁ - s₂)) = .inr c₁ by
        rwa [Nat.add_sub_cancel' (by omega)])
      omega
  refine ⟨hor, ?_⟩
  have hmin : min L R ≤ L ∧ min L R ≤ R := ⟨Nat.min_le_left L R, Nat.min_le_right L R⟩
  rcases hor with h | h <;> omega

/-- **Negative-Worktape Turnaround Lower Bound Under Blank-Reach Flip (`time_ge_of_neg_visit_and_ray_flip`):**
for any input `n ≥ 1` with `f (n + u * 2^(Nat.log2 n + 1)) ≠ f n`, if a machine `M` computing `f` in
time `T` visits cell `-(L : Int)` or lower before halting (`s₁ < T n`), then
`(Nat.log2 n + 1) + L + min L (Nat.log2 n + 1) + 1 ≤ T n`. -/
theorem time_ge_of_neg_visit_and_ray_flip {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (hM : Computes M f T) {n u s₁ L : Nat} {c₁ : Cfg M} (hn : 1 ≤ n)
    (hflip : f (n + u * 2 ^ (Nat.log2 n + 1)) ≠ f n)
    (hs₁ : s₁ < T n) (hr₁ : M.run n s₁ = .inr c₁) (hL : c₁.head ≤ -(L : Int)) :
    L + (Nat.log2 n + 1) + min L (Nat.log2 n + 1) + 1 ≤ T n := by
  obtain ⟨s₂, hs₂, c₂, hr₂, hR⟩ := exists_head_gt_log2_of_ray_flip hM hn hflip
  have h := (time_ge_of_left_and_right_visit hs₁ hs₂ hr₁ hr₂ hL
    (show ((Nat.log2 n + 1 : Nat) : Int) ≤ c₂.head by omega)).2
  exact h

end Rule30Problem3Bounds
end Ruliology.CellularAutomata
