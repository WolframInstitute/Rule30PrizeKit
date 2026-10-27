module

public import Ruliology.CellularAutomata.Rule30Prize

/-! Exact predecessor profiles and a linear closed-cycle certificate interface.
This is not an absorption theorem. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Period21Profiles

def width : Nat := 21
def modulus : Nat := 2 ^ width
abbrev State := Nat × Nat
def rotate (a : Nat) : Nat := (a >>> 1) ||| ((a.testBit 0).toNat <<< 20)
def step (p : State) : State :=
  ((rotate p.1 ^^^ (p.1 ||| p.2)) % modulus, p.1)

def advance {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => advance f n (f a)

theorem advance_add {α : Type} (f : α → α) (m n : Nat) (a : α) :
    advance f (m + n) a = advance f n (advance f m a) := by
  induction m generalizing a with
  | zero => simp [advance]
  | succ m ih => simpa only [Nat.succ_add, advance] using ih (f a)

structure SafePath {α : Type} (f : α → α) (forbidden : α) (n : Nat) (a b : α) : Prop where
  endpoint : advance f n a = b
  avoid : ∀ k, k < n → advance f k a ≠ forbidden

theorem SafePath.trans {α : Type} {f : α → α} {forbidden a b c : α} {m n : Nat}
    (h : SafePath f forbidden m a b) (g : SafePath f forbidden n b c) :
    SafePath f forbidden (m + n) a c := by
  refine ⟨by rw [advance_add, h.endpoint, g.endpoint], ?_⟩
  intro k hk
  by_cases hkm : k < m
  · exact h.avoid k hkm
  · have he : k = m + (k - m) := by omega
    rw [he, advance_add, h.endpoint]
    exact g.avoid (k - m) (by omega)

def safeCheck {α : Type} [DecidableEq α] (f : α → α) (forbidden : α) : Nat → α → Bool
  | 0, _ => true
  | n + 1, a => decide (a ≠ forbidden) && safeCheck f forbidden n (f a)

theorem safeCheck_sound {α : Type} [DecidableEq α] (f : α → α) (forbidden : α)
    (n : Nat) (a : α) (h : safeCheck f forbidden n a = true) :
    ∀ k, k < n → advance f k a ≠ forbidden := by
  induction n generalizing a with
  | zero => intro k hk; omega
  | succ n ih =>
    simp only [safeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    intro k hk
    cases k with
    | zero => exact h.1
    | succ k => exact ih (f a) h.2 k (by omega)

def checkPath {α : Type} [DecidableEq α] (f : α → α) (forbidden : α)
    (n : Nat) (a b : α) : Bool :=
  decide (advance f n a = b) && safeCheck f forbidden n a

theorem checkPath_sound {α : Type} [DecidableEq α] (f : α → α) (forbidden : α)
    (n : Nat) (a b : α) (h : checkPath f forbidden n a b = true) :
    SafePath f forbidden n a b := by
  simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, safeCheck_sound f forbidden n a h.2⟩

theorem SafePath.repeat {α : Type} {f : α → α} {forbidden a : α} {n : Nat}
    (h : SafePath f forbidden n a a) (q : Nat) :
    SafePath f forbidden (q * n) a a := by
  induction q with
  | zero => exact ⟨by simp [advance], by intro k hk; omega⟩
  | succ q ih => simpa only [Nat.succ_mul] using ih.trans h

theorem advance_return_mul {α : Type} {f : α → α} {a : α} {p : Nat}
    (h : advance f p a = a) (q : Nat) : advance f (q * p) a = a := by
  induction q with
  | zero => simp [advance]
  | succ q ih => rw [Nat.succ_mul, advance_add, ih, h]

theorem no_return_of_safe_cycle {α : Type} {f : α → α} {seed c : α} {r n : Nat}
    (hn : 0 < n) (reach : advance f r seed = c) (cycle : SafePath f seed n c c) :
    ∀ p, 0 < p → advance f p seed ≠ seed := by
  have avoid : ∀ k, advance f k c ≠ seed := by
    intro k
    have hkn : k + 1 ≤ (k + 1) * n := by
      have := Nat.mul_le_mul_left (k + 1) hn
      simpa using this
    exact (cycle.repeat (k + 1)).avoid k (by omega)
  intro p hp hret
  have hmul := advance_return_mul hret (r + 1)
  have hrp : r + 1 ≤ (r + 1) * p := by
    have := Nat.mul_le_mul_left (r + 1) hp
    simpa using this
  have he : (r + 1) * p = r + ((r + 1) * p - r) := by omega
  rw [he, advance_add, reach] at hmul
  exact avoid _ hmul

theorem inverse_advance {α : Type} (f : α → α) (s : Nat → α)
    (h : ∀ n, f (s (n + 1)) = s n) (a n : Nat) :
    advance f n (s (a + n)) = s a := by
  induction n with
  | zero => simp [advance]
  | succ n ih =>
    rw [advance, show a + (n + 1) = (a + n) + 1 by omega, h]
    exact ih

theorem inverse_collision {α : Type} (f : α → α) (s : Nat → α)
    (h : ∀ n, f (s (n + 1)) = s n) {i j : Nat} (hij : i < j) (he : s i = s j) :
    ∃ p, 0 < p ∧ advance f p (s 0) = s 0 := by
  have hi : advance f i (s i) = s 0 := by simpa using inverse_advance f s h 0 i
  have hj : advance f i (s j) = s (j - i) := by
    simpa only [show j - i + i = j by omega] using inverse_advance f s h (j - i) i
  have hz : s (j - i) = s 0 := by rw [← hj, ← he, hi]
  refine ⟨j - i, by omega, ?_⟩
  have hp := inverse_advance f s h 0 (j - i)
  simpa only [Nat.zero_add, hz] using hp

/-- Every bounded infinite right continuation makes its starting profile pair periodic
under the uniquely determined LEFT predecessor map. -/
theorem bounded_inverse_return (s : Nat → State)
    (hb : ∀ n, (s n).1 < modulus ∧ (s n).2 < modulus)
    (hs : ∀ n, step (s (n + 1)) = s n) :
    ∃ p, 0 < p ∧ advance step p (s 0) = s 0 := by
  let code : Nat → Nat := fun n => (s n).1 + modulus * (s n).2
  have hc : ∀ n, code n < 2 ^ 42 := by
    intro n
    have h := hb n
    dsimp [code, modulus, width] at *
    omega
  let bits : Nat → List Bool := fun n => (List.range 42).map (fun k => (code n).testBit k)
  obtain ⟨i, j, hij, _, he⟩ := Ruliology.CellularAutomata.Rule30Jen.pigeonhole 42 bits
    (fun n => by simp only [bits, List.length_map, List.length_range])
  have hv : code i = code j := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 42
    · have h := congrArg (fun l : List Bool => l.getD k false) he
      simp only [bits, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hk, Option.map_some, Option.getD_some] at h
      exact h
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hc i)
          (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hc j)
          (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hbi := hb i
  have hbj := hb j
  have hp : s i = s j := by
    apply Prod.ext
    · dsimp [code, modulus, width] at hv hbi hbj
      omega
    · dsimp [code, modulus, width] at hv hbi hbj
      omega
  exact inverse_collision step s hs hij hp

end Ruliology.CellularAutomata.Rule30Period21Profiles
