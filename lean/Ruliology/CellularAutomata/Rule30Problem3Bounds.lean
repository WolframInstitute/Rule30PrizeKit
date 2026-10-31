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
  `evPer_two_pow_of_eventually_time_le`, `time_unbounded_of_problem1`, `diagonal_time_unbounded`).**
  Any single pair `r, m ≥ 2^(k-1)` with `r ≡ m (mod 2^k)` and `f r ≠ f m` forces `k + 1 ≤ T n` for
  every `n ≥ 2^(k-1)` in that residue class, and flipping above the MSB forces
  `Nat.log2 n + 2 ≤ T n` (`log2_succ_succ_le_time_of_ray_flip`). Moreover, if `T n ≤ k` from some
  `N` on, every residue class mod `2^k` has a witness `m + N * 2^k ≥ N`, so `f` has period `2^k`
  from the fixed threshold `2^(k-1)` independent of `N` (`period_of_eventually_time_le`). Combining
  this with `Rule30FactorWindow.transient_add_period_ge` (`T₀ + P ≥ 16359`) proves unconditionally
  (without `Problem1`) that for every `k ≤ 13`, every machine computing `center` takes at least
  `k + 1` steps infinitely often (`time_unbounded_le_thirteen`, up to `14` steps), while
  `Rule30LeftUnbounded.D_period_unbounded` yields left diagonals requiring `≥ k + 1` steps
  infinitely often for every `k` (`diagonal_time_unbounded`).
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

end Rule30Problem3Bounds
end Ruliology.CellularAutomata
