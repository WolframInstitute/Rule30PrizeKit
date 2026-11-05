module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Prize Problem 3: the effort of computing the center column

    Problem 3: Does computing the nth cell of the center column require at least O(n)
               computational effort?

Effort needs a model of computation. The reference model here is a deterministic one-tape Turing
machine, with finitely many states and tape symbols, that reads the binary digits of `n`, least
significant first, and halts with the answer. Its effort is its number of steps. Three versions of
the problem, each implying the next:

* `Problem3`, the formal statement published with the prize: no machine computes `center n` within
  `C · (n + 1)` steps, for any constant `C`; that is, no machine whose time divided by `n` has a
  finite limit superior.
* `Problem3Verbal`, the question's "at least O(n)": no machine computes it in time `o(n)`.
* `Problem3Robust`: no machine computes it in time `n^o(1)`, that is within `n^ε` steps from some
  `n` on, for every `ε > 0`. This version does not depend on the model.

**Why only the last one is model independent.** The reasonable sequential models simulate one
another with polynomial overhead: Turing machines with any number of tapes, random-access machines
that pay for the length of the numbers they handle, and input in any base `b ≥ 2`, in either digit
order. A polynomial overhead multiplies exponents by constants, so whether some positive power
`n^ε` is needed is the same in all of them. A bound of `n` itself is not:
* a one-tape machine simulates several tapes in quadratic time, so a lower bound of `n` steps on
  one tape gives only `√n` on several;
* a random-access machine that does bitwise operations on unbounded integers at unit cost computes
  `c(n)` in `O(n)` operations, as bit `n` of `Fⁿ(1)` with `F(x) = x XOR (2x OR 4x)`.

Unary input is a different problem. It is exponentially longer, and on it every machine needs more
than `n` steps, because the center column is not eventually constant.

* `Machine`, `Machine.run`: the machine and its run on the input `n`.
* `Computes M f T`: on every input `n`, `M` halts within `T n` steps with the answer `f n`.
* `problem3Verbal_of_problem3`, `problem3Robust_of_problem3Verbal`: the chain of implications.
* `computes_lowBit`: a machine that answers with the last binary digit in one step, as a check of
  the conventions.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Problem3

open Rule30Prize

/-- A head move: one cell left, none, or one cell right. -/
inductive Move
  | left
  | stay
  | right

/-- The head position after a move. -/
def Move.apply : Move → Int → Int
  | .left, h => h - 1
  | .stay, h => h
  | .right, h => h + 1

/-- A deterministic one-tape Turing machine with the states `0, …, q` and the tape symbols
`0, …, s + 2`. Symbol `0` is the blank, and `1` and `2` are the binary digits `0` and `1`; the
machine starts in state `0`. In state `p` reading `a`, `δ p a` is either `.inl b`, halt with the
answer `b`, or `.inr (p', a', d)`: go to state `p'`, write `a'` and move the head by `d`. -/
structure Machine where
  /-- The last state. -/
  q : Nat
  /-- The number of tape symbols besides the blank and the two digits. -/
  s : Nat
  /-- The transition table. -/
  δ : Fin (q + 1) → Fin (s + 3) → Bool ⊕ (Fin (q + 1) × Fin (s + 3) × Move)

/-- A configuration: the state, the head position and the tape. -/
structure Cfg (M : Machine) where
  state : Fin (M.q + 1)
  head : Int
  tape : Int → Fin (M.s + 3)

/-- The input `n`: its binary digits, least significant first, on the cells `0, 1, …` (cell `i`
holds a digit iff `2 ^ i ≤ n`), blanks elsewhere, and the head on cell `0` in state `0`. -/
def Machine.init (M : Machine) (n : Nat) : Cfg M where
  state := ⟨0, Nat.succ_pos _⟩
  head := 0
  tape := fun i => if 0 ≤ i ∧ 2 ^ i.toNat ≤ n then
      (if n.testBit i.toNat then ⟨2, by omega⟩ else ⟨1, by omega⟩) else ⟨0, by omega⟩

/-- One step: the answer if the machine halts, the next configuration otherwise. -/
def Cfg.step {M : Machine} (c : Cfg M) : Bool ⊕ Cfg M :=
  match M.δ c.state (c.tape c.head) with
  | .inl b => .inl b
  | .inr (p, a, d) => .inr ⟨p, d.apply c.head, fun i => if i = c.head then a else c.tape i⟩

/-- The run on the input `n`: after `t` steps, the answer if the machine has halted, and the
configuration otherwise. -/
def Machine.run (M : Machine) (n : Nat) : Nat → Bool ⊕ Cfg M
  | 0 => .inr (M.init n)
  | t + 1 => match M.run n t with
    | .inl b => .inl b
    | .inr c => c.step

/-- `M` computes `f` within time `T`: on every input `n` it halts within `T n` steps with the
answer `f n`. -/
def Computes (M : Machine) (f : Nat → Bool) (T : Nat → Nat) : Prop :=
  ∀ n, M.run n (T n) = .inl (f n)

/-- **Problem 3**, the prize's formal statement: no machine computes `center n` within
`C · (n + 1)` steps, whatever the constant `C`. -/
def Problem3 : Prop := ¬ ∃ (M : Machine) (C : Nat), Computes M center fun n => C * (n + 1)

/-- **Problem 3** in the words of the question, "at least `O(n)`": no machine computes `center n`
in time `o(n)`, that is within `T n` steps where, for every `k`, `k · T n ≤ n` from some `n` on. -/
def Problem3Verbal : Prop :=
  ¬ ∃ (M : Machine) (T : Nat → Nat), Computes M center T ∧ ∀ k, ∃ N, ∀ n, N ≤ n → k * T n ≤ n

/-- **Problem 3**, independent of the model: no machine computes `center n` in time `n^o(1)`, that
is within `T n` steps where, for every `k`, `(T n)^k ≤ n` from some `n` on. -/
def Problem3Robust : Prop :=
  ¬ ∃ (M : Machine) (T : Nat → Nat), Computes M center T ∧ ∀ k, ∃ N, ∀ n, N ≤ n → T n ^ k ≤ n

/-- A machine that has halted stays halted. -/
theorem Machine.run_add {M : Machine} {n t : Nat} {b : Bool} (h : M.run n t = .inl b) (k : Nat) :
    M.run n (t + k) = .inl b := by
  induction k with
  | zero => exact h
  | succ k ih => rw [← Nat.add_assoc, Machine.run, ih]

/-- More time does no harm. -/
theorem Computes.mono {M : Machine} {f : Nat → Bool} {T T' : Nat → Nat} (h : Computes M f T)
    (hT : ∀ n, T n ≤ T' n) : Computes M f T' := fun n => by
  have := Machine.run_add (h n) (T' n - T n)
  rwa [Nat.add_sub_cancel' (hT n)] at this

/-- The sum `T 0 + ⋯ + T (N - 1)`. -/
def partialSum (T : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => partialSum T N + T N

theorem le_partialSum (T : Nat → Nat) {m N : Nat} (h : m < N) : T m ≤ partialSum T N := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [partialSum]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · have := ih h; omega
    · subst h; omega

/-- **The formal statement implies the verbal one.** A machine in time `o(n)` takes at most `n`
steps from some `N` on, so at most `C · (n + 1)` steps for `C = T 0 + ⋯ + T (N - 1) + 1`. -/
theorem problem3Verbal_of_problem3 (h : Problem3) : Problem3Verbal := by
  rintro ⟨M, T, hM, ho⟩
  obtain ⟨N, hN⟩ := ho 1
  refine h ⟨M, partialSum T N + 1, hM.mono fun n => ?_⟩
  by_cases hn : N ≤ n
  · have h1 := hN n hn
    have h2 : 1 * (n + 1) ≤ (partialSum T N + 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · have h1 := le_partialSum T (show n < N by omega)
    have h2 : (partialSum T N + 1) * 1 ≤ (partialSum T N + 1) * (n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-- **The verbal statement implies the model-independent one.** Time `n^o(1)` is time `o(n)`:
once `(T n)^2 ≤ n` and `k^2 ≤ n`, also `k · T n ≤ n`. -/
theorem problem3Robust_of_problem3Verbal (h : Problem3Verbal) : Problem3Robust := by
  rintro ⟨M, T, hM, hT⟩
  refine h ⟨M, T, hM, fun k => ?_⟩
  obtain ⟨N, hN⟩ := hT 2
  refine ⟨N + k * k, fun n hn => ?_⟩
  have h2 : T n * T n ≤ n := by
    have := hN n (by omega)
    rwa [Nat.pow_two] at this
  by_cases hk : k ≤ T n
  · exact Nat.le_trans (Nat.mul_le_mul_right _ hk) h2
  · have : k * T n ≤ k * k := Nat.mul_le_mul_left _ (by omega)
    omega

theorem problem3Robust_of_problem3 (h : Problem3) : Problem3Robust :=
  problem3Robust_of_problem3Verbal (problem3Verbal_of_problem3 h)

/-! ### A check of the conventions: the last digit in one step -/

/-- Reads cell `0` and answers whether it holds the digit `1`. -/
def lowBit : Machine where
  q := 0
  s := 0
  δ := fun _ a => .inl (a.val == 2)

theorem computes_lowBit : Computes lowBit (fun n => n % 2 == 1) fun _ => 1 := by
  intro n
  have h1 : (1 ≤ n) = (n ≠ 0) := propext (by omega)
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;>
    simp [Machine.run, Cfg.step, lowBit, Machine.init, Nat.testBit_zero, h1, h2] <;>
    split <;> simp_all

/-! ### Output Uniqueness, Minimum Step Bound, Output-Negation Closure, and Constant-Time Exclusion -/

/-- **Positive Step Bound for Any Halting Computation (`computes_one_le_time`):** because
`M.run n 0 = .inr (M.init n)`, any time bound `T` satisfying `Computes M f T` must satisfy
`1 ≤ T n` on every input `n : Nat`. -/
theorem computes_one_le_time {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (h : Computes M f T) (n : Nat) : 1 ≤ T n := by
  rcases Nat.eq_zero_or_pos (T n) with h0 | hpos
  · have hn := h n
    rw [h0, Machine.run] at hn
    nomatch hn
  · exact hpos

/-- **Deterministic Halted-Output Agreement (`run_halted_unique`):** if a machine `M` on
input `n` has halted with answer `b₁` at step `t₁` and answer `b₂` at step `t₂`, then `b₁ = b₂`. -/
theorem run_halted_unique {M : Machine} {n t₁ t₂ : Nat} {b₁ b₂ : Bool}
    (h₁ : M.run n t₁ = .inl b₁) (h₂ : M.run n t₂ = .inl b₂) : b₁ = b₂ := by
  rcases Nat.le_total t₁ t₂ with hle | hle
  · have hadd := Machine.run_add h₁ (t₂ - t₁)
    rw [Nat.add_sub_cancel' hle, h₂] at hadd
    exact (Sum.inl.inj hadd).symm
  · have hadd := Machine.run_add h₂ (t₁ - t₂)
    rw [Nat.add_sub_cancel' hle, h₁] at hadd
    exact Sum.inl.inj hadd

/-- **Uniqueness of Computed Function (`computes_unique`):** if a machine `M` computes `f₁` within
time `T₁` and `f₂` within time `T₂`, then `f₁` and `f₂` agree on every input `n`. -/
theorem computes_unique {M : Machine} {f₁ f₂ : Nat → Bool} {T₁ T₂ : Nat → Nat}
    (h₁ : Computes M f₁ T₁) (h₂ : Computes M f₂ T₂) (n : Nat) : f₁ n = f₂ n :=
  run_halted_unique (h₁ n) (h₂ n)

/-- **Output-Negated Turing Machine (`negateMachine`):** flips every halting answer `.inl b` to
`.inl (!b)` in the transition table `M.δ` while keeping all non-halting transitions `.inr` identical. -/
def negateMachine (M : Machine) : Machine where
  q := M.q
  s := M.s
  δ := fun p a => match M.δ p a with
    | .inl b => .inl (!b)
    | .inr next => .inr next

/-- **Configuration Equivalence Under `negateMachine` (`toNegateCfg`):** reinterprets a
configuration of `M` as a configuration of `negateMachine M` with identical state, head, and tape. -/
def toNegateCfg {M : Machine} (c : Cfg M) : Cfg (negateMachine M) where
  state := c.state
  head := c.head
  tape := c.tape

/-- **One-Step Simulation of `negateMachine` (`step_toNegateCfg`):** a single step of
`toNegateCfg c` under `negateMachine M` either halts with `!b` when `c.step = .inl b` or steps to
`toNegateCfg c'` when `c.step = .inr c'`. -/
theorem step_toNegateCfg {M : Machine} (c : Cfg M) :
    (toNegateCfg c).step = match c.step with
      | .inl b => Sum.inl (!b)
      | .inr c' => Sum.inr (toNegateCfg c') := by
  unfold Cfg.step toNegateCfg negateMachine
  dsimp
  cases M.δ c.state (c.tape c.head) <;> rfl

/-- **Exact Run Simulation of `negateMachine` (`run_negateMachine`):** at every step `t`, running
`negateMachine M` on `n` negates any halted output `.inl b` and preserves any active configuration
`.inr c`. -/
theorem run_negateMachine (M : Machine) (n t : Nat) :
    (negateMachine M).run n t = match M.run n t with
      | .inl b => Sum.inl (!b)
      | .inr c => Sum.inr (toNegateCfg c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Machine.run]
    rw [ih]
    cases M.run n t with
    | inl b => rfl
    | inr c => exact step_toNegateCfg c

/-- **Zero-Overhead Output-Negation Closure (`computes_not`):** if `M` computes `f` within time `T`,
then `negateMachine M` computes `fun n => !f n` within the exact same time bound `T`. -/
theorem computes_not {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (h : Computes M f T) : Computes (negateMachine M) (fun n => !f n) T := by
  intro n
  rw [run_negateMachine, h n]

/-- **One-Step Even-Parity Machine (`computes_evenBit`):** `negateMachine lowBit` computes whether
`n` is even (`!(n % 2 == 1)`) in 1 step on every input `n`. -/
theorem computes_evenBit :
    Computes (negateMachine lowBit) (fun n => !(n % 2 == 1)) fun _ => 1 :=
  computes_not computes_lowBit

/-- **Constant-Output One-Step Machine (`constMachine`):** halts immediately at step 1 with the
constant Boolean answer `b`. -/
def constMachine (b : Bool) : Machine where
  q := 0
  s := 0
  δ := fun _ _ => .inl b

/-- **One-Step Computability of Constant Functions (`computes_constMachine`):** for every `b : Bool`,
`constMachine b` computes `fun _ => b` in 1 step. -/
theorem computes_constMachine (b : Bool) :
    Computes (constMachine b) (fun _ => b) fun _ => 1 := by
  intro n
  rfl

/-- **Bounded-Time Exclusion from `Problem3Robust` (`no_bounded_time_of_problem3Robust`):** if
`Problem3Robust` holds, then no machine `M` can compute `center` within a constant step bound
`fun _ => B` for any `B : Nat`. -/
theorem no_bounded_time_of_problem3Robust (h : Problem3Robust) (M : Machine) (B : Nat) :
    ¬ Computes M center (fun _ => B) := by
  intro hM
  exact h ⟨M, fun _ => B, hM, fun k => ⟨B ^ k, fun _ hn => hn⟩⟩

/-! ### Parity-Dispatch Combinator, 1-Step Locality Characterization, and Unconditional 1-Step Exclusion for `center` -/

/-- **One-Step Parity-Dispatch Machine (`iteLowBitMachine`):** given two Boolean answers `b₀, b₁`,
halts in 1 step with `b₁` when cell `0` holds symbol `2` (`n % 2 == 1`) and `b₀` otherwise. -/
def iteLowBitMachine (b₀ b₁ : Bool) : Machine where
  q := 0
  s := 0
  δ := fun _ a => .inl (if a.val == 2 then b₁ else b₀)

/-- **One-Step Evaluation of `iteLowBitMachine` (`computes_ite_lowBit`):** for any `b₀, b₁ : Bool`,
`iteLowBitMachine b₀ b₁` computes `fun n => if n % 2 == 1 then b₁ else b₀` in 1 step on all inputs. -/
theorem computes_ite_lowBit (b₀ b₁ : Bool) :
    Computes (iteLowBitMachine b₀ b₁) (fun n => if n % 2 == 1 then b₁ else b₀) fun _ => 1 := by
  intro n
  have h1 : (1 ≤ n) = (n ≠ 0) := propext (by omega)
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;>
    simp [Machine.run, Cfg.step, iteLowBitMachine, Machine.init, Nat.testBit_zero, h1, h2] <;>
    split <;> simp_all

/-- **Initial Cell-0 Agreement for Positive Inputs of Equal Parity (`init_tape_zero_eq_of_pos_of_mod_two_eq`):**
for any machine `M` and positive inputs `m, n ≥ 1` with `m % 2 = n % 2`, the initial symbol at head
position `0` is identical: `(M.init m).tape 0 = (M.init n).tape 0`. -/
theorem init_tape_zero_of_pos (M : Machine) {n : Nat} (hn : 1 ≤ n) :
    (M.init n).tape 0 = if n % 2 == 1 then ⟨2, by omega⟩ else ⟨1, by omega⟩ := by
  simp [Machine.init, Nat.testBit_zero, hn]

/-- **Initial Cell-0 Agreement for Positive Inputs of Equal Parity (`init_tape_zero_eq_of_pos_of_mod_two_eq`):**
for any machine `M` and positive inputs `m, n ≥ 1` with `m % 2 = n % 2`, the initial symbol at head
position `0` is identical: `(M.init m).tape 0 = (M.init n).tape 0`. -/
theorem init_tape_zero_eq_of_pos_of_mod_two_eq (M : Machine) {m n : Nat}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmod : m % 2 = n % 2) :
    (M.init m).tape 0 = (M.init n).tape 0 := by
  rw [init_tape_zero_of_pos M hm, init_tape_zero_of_pos M hn, hmod]

/-- **One-Step Transition Dichotomy (`run_one_eq_inl_iff`):** for any machine `M`, input `n : Nat`,
and answer `b : Bool`, `M.run n 1 = .inl b` if and only if `M.δ ⟨0, Nat.succ_pos _⟩ ((M.init n).tape 0) = .inl b`. -/
theorem run_one_eq_inl_iff (M : Machine) (n : Nat) (b : Bool) :
    M.run n 1 = .inl b ↔ M.δ ⟨0, Nat.succ_pos _⟩ ((M.init n).tape 0) = .inl b := by
  change (M.init n).step = .inl b ↔ _
  unfold Cfg.step
  change (match M.δ ⟨0, Nat.succ_pos _⟩ ((M.init n).tape 0) with
    | .inl b' => Sum.inl b'
    | .inr (p, a, d) => Sum.inr _) = .inl b ↔ _
  cases M.δ ⟨0, Nat.succ_pos _⟩ ((M.init n).tape 0) with
  | inl b' => simp
  | inr trip => simp

/-- **One-Step Run Agreement for Positive Inputs of Equal Parity (`run_one_eq_of_pos_of_mod_two_eq`):**
for any machine `M` and positive inputs `m, n ≥ 1` with `m % 2 = n % 2`, if `M.run m 1 = .inl b`,
then `M.run n 1 = .inl b`. -/
theorem run_one_eq_of_pos_of_mod_two_eq (M : Machine) {m n : Nat} {b : Bool}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmod : m % 2 = n % 2) (hrun : M.run m 1 = .inl b) :
    M.run n 1 = .inl b := by
  rw [run_one_eq_inl_iff] at hrun ⊢
  rw [← init_tape_zero_eq_of_pos_of_mod_two_eq M hm hn hmod]
  exact hrun

/-- **Parity Determination of 1-Step Computable Functions (`computes_time_one_eq_of_pos_of_mod_two_eq`):**
if a machine `M` computes `f` within time `T` and `T m ≤ 1`, `T n ≤ 1` on positive inputs `m, n ≥ 1`
with `m % 2 = n % 2`, then `f m = f n`. -/
theorem computes_time_one_eq_of_pos_of_mod_two_eq {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (h : Computes M f T) {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hTm : T m ≤ 1) (hTn : T n ≤ 1) (hmod : m % 2 = n % 2) :
    f m = f n := by
  have hm1 : T m = 1 := by have := computes_one_le_time h m; omega
  have hn1 : T n = 1 := by have := computes_one_le_time h n; omega
  have hrun_m : M.run m 1 = .inl (f m) := by rw [← hm1]; exact h m
  have hrun_n : M.run n 1 = .inl (f n) := by rw [← hn1]; exact h n
  have hrun_n' := run_one_eq_of_pos_of_mod_two_eq M hm hn hmod hrun_m
  exact run_halted_unique hrun_n' hrun_n

/-- **Exact Values of `center 2` and `center 4` (`center_two_ne_center_four`):** at even steps `2`
and `4`, `center 2 = false` and `center 4 = true`, so `center 2 ≠ center 4`. -/
theorem center_two_ne_center_four : center 2 = false ∧ center 4 = true ∧ center 2 ≠ center 4 := by
  decide

/-- **Unconditional 1-Step Exclusion for the Rule 30 Center Column (`not_computes_center_time_one`):**
no machine `M` can compute `center` within 1 step on even inputs `2` and `4` (`T 2 ≤ 1 ∧ T 4 ≤ 1`);
in particular, `¬ Computes M center (fun _ => 1)` holds unconditionally (without assuming `Problem3Robust`). -/
theorem not_computes_center_time_one (M : Machine) :
    ¬ Computes M center (fun _ => 1) := by
  intro h
  have heq := computes_time_one_eq_of_pos_of_mod_two_eq h (m := 2) (n := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  exact center_two_ne_center_four.2.2 heq

/-- **Two-Step Lower Bound on Either Input 2 or Input 4 (`two_le_time_two_or_four`):** for every
machine `M` and step function `T` satisfying `Computes M center T`, either `2 ≤ T 2` or `2 ≤ T 4`. -/
theorem two_le_time_two_or_four {M : Machine} {T : Nat → Nat} (h : Computes M center T) :
    2 ≤ T 2 ∨ 2 ≤ T 4 := by
  by_cases h2 : 2 ≤ T 2
  · exact Or.inl h2
  · right
    by_cases h4 : 2 ≤ T 4
    · exact h4
    · exfalso
      have heq := computes_time_one_eq_of_pos_of_mod_two_eq h (m := 2) (n := 4)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact center_two_ne_center_four.2.2 heq

/-- **Explicit Linear-Bound Exceedance Witness Under `Problem3` (`exists_gt_mul_of_problem3`):**
if `Problem3` holds, then for every machine `M` computing `center` in time `T` and every constant
`C : Nat`, there exists an input `n : Nat` such that `C * (n + 1) < T n`. -/
theorem exists_gt_mul_of_problem3 (hP3 : Problem3) {M : Machine} {T : Nat → Nat}
    (hM : Computes M center T) (C : Nat) :
    ∃ n, C * (n + 1) < T n := by
  refine Classical.byContradiction fun hne => ?_
  apply hP3
  refine ⟨M, C, hM.mono (fun n => ?_)⟩
  rcases Nat.lt_or_ge (C * (n + 1)) (T n) with hlt | hge
  · exact False.elim (hne ⟨n, hlt⟩)
  · exact hge

/-- **Cofinal Sublinear Exceedance Witnesses Under `Problem3Verbal` (`exists_gt_mul_of_problem3Verbal`):**
if `Problem3Verbal` holds, then for every machine `M` computing `center` in time `T`, there exists a
slope `k ≥ 1` such that for every threshold `N : Nat`, some input `n ≥ N` satisfies `n < k * T n`. -/
theorem exists_gt_mul_of_problem3Verbal (hP3V : Problem3Verbal) {M : Machine} {T : Nat → Nat}
    (hM : Computes M center T) :
    ∃ k, 1 ≤ k ∧ ∀ N, ∃ n, N ≤ n ∧ n < k * T n := by
  refine Classical.byContradiction fun hne => ?_
  apply hP3V
  refine ⟨M, T, hM, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, fun n _ => by simp⟩
  · refine Classical.byContradiction fun hN => ?_
    apply hne
    refine ⟨k, hk, fun N => Classical.byContradiction fun hn => hN ⟨N, fun n hge => ?_⟩⟩
    rcases Nat.lt_or_ge n (k * T n) with hlt | hle
    · exact False.elim (hn ⟨n, hge, hlt⟩)
    · exact hle

/-- **Cofinal Polynomial-Root Exceedance Witnesses Under `Problem3Robust` (`exists_gt_pow_of_problem3Robust`):**
if `Problem3Robust` holds, then for every machine `M` computing `center` in time `T`, there exists an
exponent `k ≥ 1` such that for every threshold `N : Nat`, some input `n ≥ N` satisfies `n < T n ^ k`. -/
theorem exists_gt_pow_of_problem3Robust (hP3R : Problem3Robust) {M : Machine} {T : Nat → Nat}
    (hM : Computes M center T) :
    ∃ k, 1 ≤ k ∧ ∀ N, ∃ n, N ≤ n ∧ n < T n ^ k := by
  refine Classical.byContradiction fun hne => ?_
  apply hP3R
  refine ⟨M, T, hM, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun n hn => by simpa using hn⟩
  · refine Classical.byContradiction fun hN => ?_
    apply hne
    refine ⟨k, hk, fun N => Classical.byContradiction fun hn => hN ⟨N, fun n hge => ?_⟩⟩
    rcases Nat.lt_or_ge n (T n ^ k) with hlt | hle
    · exact False.elim (hn ⟨n, hge, hlt⟩)
    · exact hle

/-! ### Two-Step Light-Cone Locality on `i ≤ 1`, Unconditional 2-Step Exclusion, and the `3 ≤ T 3 ∨ 3 ≤ T 7` Lower Bound -/

/-- **Single-Step Rightward Reach Bound (`apply_le_add_one`):** for every move `d : Move` and
head position `h : Int`, `d.apply h ≤ h + 1`. -/
theorem apply_le_add_one (d : Move) (h : Int) : d.apply h ≤ h + 1 := by
  cases d <;> simp [Move.apply] <;> omega

/-- **Step-1 Head Bound from Origin (`apply_zero_le_one`):** starting from head position `0`,
after one move `d` the head position satisfies `d.apply 0 ≤ 1`. -/
theorem apply_zero_le_one (d : Move) : d.apply 0 ≤ 1 := by
  simpa using apply_le_add_one d 0

/-- **Blank Initial Tape on the Negative Half-Line (`init_tape_neg`):** for any machine `M`,
input `n : Nat`, and negative cell `i < 0`, `(M.init n).tape i` holds the blank symbol `0`. -/
theorem init_tape_neg (M : Machine) (n : Nat) {i : Int} (hi : i < 0) :
    (M.init n).tape i = ⟨0, by omega⟩ := by
  have hnot : ¬ (0 ≤ i ∧ 2 ^ i.toNat ≤ n) := fun h => by omega
  simp [Machine.init, hnot]

/-- **Initial Tape Agreement on All Cells `i ≤ 1` (`init_tape_eq_of_le_one`):** if inputs `m, n`
produce the same initial symbols on cells `0` and `1`, then `(M.init m).tape i = (M.init n).tape i`
for every cell `i ≤ 1`. -/
theorem init_tape_eq_of_le_one (M : Machine) {m n : Nat}
    (h0 : (M.init m).tape 0 = (M.init n).tape 0)
    (h1 : (M.init m).tape 1 = (M.init n).tape 1)
    {i : Int} (hi : i ≤ 1) :
    (M.init m).tape i = (M.init n).tape i := by
  rcases (by omega : i < 0 ∨ i = 0 ∨ i = 1) with hneg | rfl | rfl
  · rw [init_tape_neg M m hneg, init_tape_neg M n hneg]
  · exact h0
  · exact h1

/-- **Halted Persistence to Any Later Step Bound (`run_le_eq_inl`):** if `M` computes `f` within
time `T` and `T n ≤ k`, then `M.run n k = .inl (f n)`. -/
theorem run_le_eq_inl {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (h : Computes M f T) {n k : Nat} (hk : T n ≤ k) :
    M.run n k = .inl (f n) := by
  have hadd := Machine.run_add (h n) (k - T n)
  rwa [Nat.add_sub_cancel' hk] at hadd

/-- **Two-Step Halting Equivalence Under Cell-`{0, 1}` Agreement
(`run_two_eq_inl_iff_of_init_zero_one_eq`):** if `(M.init m).tape 0 = (M.init n).tape 0` and
`(M.init m).tape 1 = (M.init n).tape 1`, then for every answer `b : Bool`,
`M.run m 2 = .inl b ↔ M.run n 2 = .inl b`. -/
theorem run_two_eq_inl_iff_of_init_zero_one_eq (M : Machine) {m n : Nat}
    (h0 : (M.init m).tape 0 = (M.init n).tape 0)
    (h1 : (M.init m).tape 1 = (M.init n).tape 1) (b : Bool) :
    M.run m 2 = .inl b ↔ M.run n 2 = .inl b := by
  simp only [Machine.run, Cfg.step]
  have hhead0 : (M.init m).head = 0 := rfl
  have hhead0' : (M.init n).head = 0 := rfl
  have hstate0 : (M.init m).state = (M.init n).state := rfl
  rw [hhead0, hhead0', hstate0, h0]
  cases M.δ (M.init n).state ((M.init n).tape 0) with
  | inl b0 => rfl
  | inr trip =>
    rcases trip with ⟨p, a, d⟩
    dsimp only
    have hcell : (if d.apply 0 = 0 then a else (M.init m).tape (d.apply 0)) =
        (if d.apply 0 = 0 then a else (M.init n).tape (d.apply 0)) := by
      split
      · rfl
      · exact init_tape_eq_of_le_one M h0 h1 (apply_zero_le_one d)
    rw [hcell]
    cases M.δ p (if d.apply 0 = 0 then a else (M.init n).tape (d.apply 0)) <;> simp

/-- **Two-Step Output Determination by Cells `0` and `1`
(`computes_time_two_eq_of_init_zero_one_eq`):** if `M` computes `f` within time `T` with
`T m ≤ 2` and `T n ≤ 2`, and `m, n` agree on initial tape cells `0` and `1`, then `f m = f n`. -/
theorem computes_time_two_eq_of_init_zero_one_eq {M : Machine} {f : Nat → Bool} {T : Nat → Nat}
    (h : Computes M f T) {m n : Nat} (hTm : T m ≤ 2) (hTn : T n ≤ 2)
    (h0 : (M.init m).tape 0 = (M.init n).tape 0)
    (h1 : (M.init m).tape 1 = (M.init n).tape 1) :
    f m = f n := by
  have hm2 : M.run m 2 = .inl (f m) := run_le_eq_inl h hTm
  have hn2 : M.run n 2 = .inl (f n) := run_le_eq_inl h hTn
  have hn2' : M.run n 2 = .inl (f m) :=
    (run_two_eq_inl_iff_of_init_zero_one_eq M h0 h1 (f m)).mp hm2
  exact run_halted_unique hn2' hn2

/-- **Initial Cell-`{0, 1}` Agreement for Inputs `2` and `6` (`init_two_eq_init_six`):**
inputs `2` and `6` (`2 ≡ 6 mod 4`) have identical initial symbols on cells `0` and `1`. -/
theorem init_two_eq_init_six (M : Machine) :
    (M.init 2).tape 0 = (M.init 6).tape 0 ∧ (M.init 2).tape 1 = (M.init 6).tape 1 :=
  ⟨rfl, rfl⟩

/-- **Initial Cell-`{0, 1}` Agreement for Inputs `3` and `7` (`init_three_eq_init_seven`):**
inputs `3` and `7` (`3 ≡ 7 mod 4`) have identical initial symbols on cells `0` and `1`. -/
theorem init_three_eq_init_seven (M : Machine) :
    (M.init 3).tape 0 = (M.init 7).tape 0 ∧ (M.init 3).tape 1 = (M.init 7).tape 1 :=
  ⟨rfl, rfl⟩

/-- **Exact Values of `center 3` and `center 7` (`center_three_ne_center_seven`):** at steps `3`
and `7`, `center 3 = true` and `center 7 = false`, so `center 3 ≠ center 7`. -/
theorem center_three_ne_center_seven : center 3 = true ∧ center 7 = false ∧ center 3 ≠ center 7 := by
  decide

/-- **Unconditional 2-Step Exclusion for the Rule 30 Center Column (`not_computes_center_time_two`):**
no machine `M` can compute `center` within 2 steps on all inputs (`¬ Computes M center (fun _ => 2)`),
unconditionally (without assuming `Problem3Robust`). -/
theorem not_computes_center_time_two (M : Machine) :
    ¬ Computes M center (fun _ => 2) := by
  intro h
  obtain ⟨h0, h1⟩ := init_three_eq_init_seven M
  have heq := computes_time_two_eq_of_init_zero_one_eq h (m := 3) (n := 7) (by omega) (by omega) h0 h1
  exact center_three_ne_center_seven.2.2 heq

/-- **Three-Step Lower Bound on Either Input 3 or Input 7 (`three_le_time_three_or_seven`):** for
every machine `M` and step bound `T` satisfying `Computes M center T`, either `3 ≤ T 3` or `3 ≤ T 7`. -/
theorem three_le_time_three_or_seven {M : Machine} {T : Nat → Nat} (h : Computes M center T) :
    3 ≤ T 3 ∨ 3 ≤ T 7 := by
  by_cases h3 : 3 ≤ T 3
  · exact Or.inl h3
  · right
    by_cases h7 : 3 ≤ T 7
    · exact h7
    · exfalso
      obtain ⟨h0, h1⟩ := init_three_eq_init_seven M
      have heq := computes_time_two_eq_of_init_zero_one_eq h (m := 3) (n := 7) (by omega) (by omega) h0 h1
      exact center_three_ne_center_seven.2.2 heq

end Rule30Problem3
end Ruliology.CellularAutomata
