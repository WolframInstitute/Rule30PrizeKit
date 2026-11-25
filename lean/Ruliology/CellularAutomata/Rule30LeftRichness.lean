module

public import Ruliology.CellularAutomata.Rule30MaskedForkRate
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Jen
public import Ruliology.CellularAutomata.Rule30MaskedJen
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers

/-!
# Rule 30: a periodic center leaves its left side poor

Let `leftWord t n` be the `n` cells just left of the center at time `t`, nearest first. Solving
the rule for the left neighbour, `cell t (i - 1) = cell (t + 1) i ⊕ (cell t i ∨ cell t (i + 1))`,
shows that `leftWord t m` is determined by the `m + 1` center readings from `t` on and the `m`
OR readings `cell ∙ 0 ∨ cell ∙ 1` from `t` on (`leftWord_eq`). Under a proposed center period `P`
after `T`, the center readings depend only on the phase, and `Rule30MaskedForkRate` bounds the OR
words compatible with a center word of length `2 n` by `2 ^ (n + 1)`. Hence any list of times
with pairwise different left words of length `2 n` has at most `T + P · 2 ^ (n + 1)` entries
(`length_le_of_periodic`).

So Problem 1 follows once the left side of the center is rich enough: if for all `T` and `P > 0`
some width `2 n` carries more than `T + P · 2 ^ (n + 1)` different left words
(`problem1_of_rich_left`). In growth terms, a periodic center allows at most `1/2` bit per cell
of different left words, while the singleton shows every `n`-bit word to the left of the center
at some time for every `n ≤ 17` (computation, not part of this module). The same counting with a
six-cell strip automaton of 2,555 states lowers `1/2` to `log₂(21/2)/12 ≈ 0.2827` bit per cell
(`strip_or_word_count`, `length_le_of_periodic_strip`, `problem1_of_strip_rich_left`); an earlier,
unformalized certificate with 4594 reachable strip states gave `log₂(32/3)/12 ≈ 0.2846`. For
rules 90, 150 and 210 the singleton's left words number at most `4 n` (`rule90_leftWords_le_4n`,
`rule150_leftWords_le_4n`, `rule210_leftWords_le_4n`), so a proof of the richness hypothesis must
use the OR of rule 30. The hypothesis is open.

Contributed by Katip Kurtuluş with Claude (Anthropic), ChatGPT (OpenAI) and Gemini (Google); the
strip certificate and the `4 n` bounds by G.P.J.W. Quint and Gemini.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30LeftRichness

open Rule30Jen Rule30MaskedJen Rule30MaskedForkRate Rule30Realization

/-- The `n` cells just left of the center at time `t`, nearest first. -/
def leftWord (t n : Nat) : List Bool := (List.range n).map (fun (k : Nat) => cell t (-((k : Int) + 1)))

/-! ### Reconstruction from the center and the OR readings -/

/-- Equal center readings on `[0, m]` and equal OR readings on `[0, m)` give equal cells in the
triangle to the left: column `-j` agrees at offsets `k` with `k + j ≤ m`. -/
theorem columns_eq {s t m : Nat}
    (hc : ∀ k, k ≤ m → cell (s + k) 0 = cell (t + k) 0)
    (ho : ∀ k, k < m → orCol 0 (s + k) = orCol 0 (t + k)) :
    ∀ j k : Nat, k + j ≤ m → cell (s + k) (-(j : Int)) = cell (t + k) (-(j : Int)) := by
  have step : ∀ j, (∀ k, k + j ≤ m → cell (s + k) (-(j : Int)) = cell (t + k) (-(j : Int))) ∧
      (∀ k, k + (j + 1) ≤ m →
        cell (s + k) (-((j + 1 : Nat) : Int)) = cell (t + k) (-((j + 1 : Nat) : Int))) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun k hk => by simpa using hc k (by omega), fun k hk => ?_⟩
      have e : (-((0 + 1 : Nat) : Int)) = 0 - 1 := by omega
      rw [e, cell_left' (s + k) 0, cell_left' (t + k) 0,
        show s + k + 1 = s + (k + 1) by omega, show t + k + 1 = t + (k + 1) by omega,
        hc (k + 1) (by omega), ho k (by omega)]
    | succ j ih =>
      refine ⟨ih.2, fun k hk => ?_⟩
      have e : (-((j + 1 + 1 : Nat) : Int)) = (-((j + 1 : Nat) : Int)) - 1 := by omega
      have e2 : (-((j + 1 : Nat) : Int)) + 1 = -((j : Nat) : Int) := by omega
      rw [e, cell_left (s + k), cell_left (t + k), e2,
        show s + k + 1 = s + (k + 1) by omega, show t + k + 1 = t + (k + 1) by omega,
        ih.2 (k + 1) (by omega), ih.2 k (by omega), ih.1 k (by omega)]
  intro j k hk
  exact (step j).1 k hk

/-- The left word of length `m` is determined by `m + 1` center readings and `m` OR readings. -/
theorem leftWord_eq {s t m : Nat}
    (hc : ∀ k, k ≤ m → cell (s + k) 0 = cell (t + k) 0)
    (ho : ∀ k, k < m → orCol 0 (s + k) = orCol 0 (t + k)) :
    leftWord s m = leftWord t m := by
  unfold leftWord
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  have h := columns_eq hc ho (k + 1) 0 (by omega)
  simpa [show ((k + 1 : Nat) : Int) = (k : Int) + 1 by omega] using h

/-! ### Segments -/

theorem segment_length' (f : Nat → Bool) (t n : Nat) : (segment f t n).length = n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [segment, ih]

theorem segment_at {f : Nat → Bool} {i j n : Nat}
    (h : segment f i n = segment f j n) (k : Nat) (hk : k < n) : f (i + k) = f (j + k) := by
  induction n generalizing i j k with
  | zero => omega
  | succ n ih =>
    have hh := List.cons.inj h
    cases k with
    | zero => simpa using hh.1
    | succ k =>
      simpa only [show i + (k + 1) = i + 1 + k by omega, show j + (k + 1) = j + 1 + k by omega] using
        ih hh.2 k (by omega)

theorem segment_congr {f g : Nat → Bool} {i j n : Nat}
    (h : ∀ k, k < n → f (i + k) = g (j + k)) : segment f i n = segment g j n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    simp only [segment, List.cons.injEq]
    refine ⟨by simpa using h 0 (by omega), ih ?_⟩
    intro k hk
    simpa only [show i + 1 + k = i + (k + 1) by omega, show j + 1 + k = j + (k + 1) by omega] using
      h (k + 1) (by omega)

/-! ### Counting under a proposed period -/

/-- Under a proposed period the center reading depends only on the phase. -/
theorem center_phase {T P : Nat} (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) :
    ∀ t, T ≤ t → cell t 0 = cell (T + (t - T) % P) 0 := by
  have shift : ∀ q x, T ≤ x → cell (x + P * q) 0 = cell x 0 := by
    intro q
    induction q with
    | zero => intro x _; simp
    | succ q ih =>
      intro x hx
      rw [show x + P * (q + 1) = (x + P * q) + P by rw [Nat.mul_succ]; omega,
        per _ (by omega), ih x hx]
  intro t ht
  have hd := Nat.mod_add_div (t - T) P
  have := shift ((t - T) / P) (T + (t - T) % P) (by omega)
  rw [show T + (t - T) % P + P * ((t - T) / P) = t by omega] at this
  exact this

/-- The key of a time: the time itself before `T`, afterwards the phase and the OR word. -/
def key (T P n t : Nat) : Nat × List Bool :=
  if t < T then (t, []) else (T + (t - T) % P, segment (orCol 0) t (2 * n))

theorem leftWord_of_key {T P n : Nat}
    (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) {a b : Nat}
    (h : key T P n a = key T P n b) : leftWord a (2 * n) = leftWord b (2 * n) := by
  unfold key at h
  by_cases ha : a < T <;> by_cases hb : b < T <;> simp only [ha, hb, ↓reduceIte] at h
  · rw [(Prod.mk.inj h).1]
  · have := (Prod.mk.inj h).1; omega
  · have := (Prod.mk.inj h).1; omega
  · obtain ⟨hphase, hor⟩ := Prod.mk.inj h
    apply leftWord_eq
    · intro k _
      rw [center_phase per (a + k) (by omega), center_phase per (b + k) (by omega)]
      congr 2
      have h1 : (a + k - T) % P = ((a - T) % P + k % P) % P := by
        rw [show a + k - T = (a - T) + k by omega, Nat.add_mod]
      have h2 : (b + k - T) % P = ((b - T) % P + k % P) % P := by
        rw [show b + k - T = (b - T) + k by omega, Nat.add_mod]
      rw [h1, h2, show (a - T) % P = (b - T) % P by omega]
    · intro k hk
      exact segment_at hor k (by omega)

/-- The possible keys, at most `T + P · 2 ^ (n + 1)` of them. -/
def keyList (T P n : Nat) : List (Nat × List Bool) :=
  (List.range T).map (fun t => (t, [])) ++
    (List.range P).flatMap (fun p =>
      (words (segment (fun i => cell i 0) (T + p) (2 * n)) State.free).map (fun w => (T + p, w)))

theorem key_mem {T P n : Nat} (hp : 0 < P) (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (t : Nat) : key T P n t ∈ keyList T P n := by
  unfold key keyList
  by_cases ht : t < T
  · simp only [ht, ↓reduceIte]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  · simp only [ht, ↓reduceIte]
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨(t - T) % P, List.mem_range.mpr (Nat.mod_lt _ hp), ?_⟩
    refine List.mem_map.mpr ⟨segment (orCol 0) t (2 * n), ?_, rfl⟩
    have obs := observations_mem seed t (2 * n) State.free trivial
    have e1 : segment (fun i => evol seed i 0 || evol seed i 1) t (2 * n) =
        segment (orCol 0) t (2 * n) := by
      apply segment_congr
      intro k _
      simp [orCol, evol_seed]
    have e2 : segment (fun i => evol seed i 0) t (2 * n) =
        segment (fun i => cell i 0) (T + (t - T) % P) (2 * n) := by
      apply segment_congr
      intro k _
      rw [evol_seed, center_phase per (t + k) (by omega),
        center_phase per (T + (t - T) % P + k) (by omega)]
      congr 2
      rw [show t + k - T = (t - T) + k by omega,
        show T + (t - T) % P + k - T = (t - T) % P + k by omega, Nat.mod_add_mod]
    rw [e1, e2] at obs
    exact obs

theorem flatMap_length_le {β : Type} (l : List Nat) (f : Nat → List β) (c : Nat)
    (h : ∀ x, x ∈ l → (f x).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem keyList_length (T P n : Nat) : (keyList T P n).length ≤ T + P * 2 ^ (n + 1) := by
  unfold keyList
  rw [List.length_append, List.length_map, List.length_range]
  have := flatMap_length_le (List.range P)
    (fun p => (words (segment (fun i => cell i 0) (T + p) (2 * n)) State.free).map (fun w => (T + p, w)))
    (2 ^ (n + 1)) (fun p _ => by
      rw [List.length_map]
      exact masked_word_count n _ (segment_length' _ _ _))
  rw [List.length_range] at this
  omega

/-- **Counting bound.** Under a proposed center period `P` after `T`, a list of times with pairwise
different left words of length `2 n` has at most `T + P · 2 ^ (n + 1)` entries. -/
theorem length_le_of_periodic {T P : Nat} (hp : 0 < P)
    (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (n : Nat) (ts : List Nat)
    (hnd : (ts.map (fun t => leftWord t (2 * n))).Nodup) :
    ts.length ≤ T + P * 2 ^ (n + 1) := by
  have hk : (ts.map (key T P n)).Nodup := by
    rw [List.Nodup, List.pairwise_map] at hnd ⊢
    exact hnd.imp (fun hne heq => hne (leftWord_of_key per heq))
  have hsub : ts.map (key T P n) ⊆ keyList T P n := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact key_mem hp per t
  calc ts.length = (ts.map (key T P n)).length := (List.length_map _).symm
    _ ≤ (keyList T P n).length := hk.length_le_of_subset hsub
    _ ≤ T + P * 2 ^ (n + 1) := keyList_length T P n

/-- **Problem 1 from a rich left side.** If for all `T` and `P > 0` some width `2 n` carries more
than `T + P · 2 ^ (n + 1)` different left words, the center column is not eventually periodic. -/
theorem problem1_of_rich_left
    (h : ∀ T P : Nat, 0 < P → ∃ n : Nat, ∃ ts : List Nat,
      (ts.map (fun t => leftWord t (2 * n))).Nodup ∧ T + P * 2 ^ (n + 1) < ts.length) :
    Rule30Prize.Problem1 := by
  rintro ⟨T, P, hp, per⟩
  obtain ⟨n, ts, hnd, hlt⟩ := h T P hp
  have := length_le_of_periodic hp (fun t ht => by simpa [Rule30Prize.center] using per t ht) n ts hnd
  omega

end Rule30LeftRichness

/-! ### Formalized 2,555-State Six-Cell Strip 21/2 Certificate and Linear 4n Barriers for Rules 90, 150, and 210 -/

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000

namespace Rule30LeftRichnessStripCert
open Ruliology.CellularAutomata
open Rule30Jen Rule30MaskedJen Rule30Realization Rule30ZeroBoundaryBarriers

/-! ### 1. Monomorphic Tree, 16-Bit SIMD Engine, and 6-Cell Nibble Cover -/
def n0 : Nat := Nat.zero
def k1 : Nat := 1
def k4 : Nat := 4
def k13 : Nat := 13
def k15 : Nat := 15
def k16 : Nat := 16
def k26 : Nat := 26
def k39 : Nat := 39
def k64 : Nat := 64
def kP : Nat := 21
def kQ : Nat := 2
def kwMin : Nat := 48
def kw0 : Nat := 441
def kM : Nat := 2555
def kBsuf : Nat := 8
def kBhi : Nat := 4
def kBtot : Nat := 12
def kLanes : Nat := 256
def m13 : Nat := 8191
def lim15 : Nat := 32767
def all64 : Nat := 0xffffffffffffffff
def b0 : Nat := 0
def b1 : Nat := 1
def b2 : Nat := 2
def b3 : Nat := 3
def b4 : Nat := 4
def b5 : Nat := 5
def b6 : Nat := 6
def b7 : Nat := 7
def b8 : Nat := 8
def b9 : Nat := 9
def b10 : Nat := 10
def b11 : Nat := 11
def vsh0 : Nat := 4096
def vsh1 : Nat := 8192
def vsh2 : Nat := 16384
def vsh3 : Nat := 32768
def vsh4 : Nat := 65536
def vsh5 : Nat := 131072
def vsh6 : Nat := 262144
def vsh7 : Nat := 524288
def vsh8 : Nat := 1048576
def vsh9 : Nat := 2097152
def vsh10 : Nat := 4194304
def vsh11 : Nat := 8388608
def vm0 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def repL : Nat := 0x1000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001
def hi2L : Nat := 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000
def msbL : Nat := 0x8000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000
structure VMasks where (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 : Nat)
structure S1 where (a b : Nat)
structure S2 where (a b : S1)
structure S3 where (a b : S2)
structure S4 where (a b : S3)
structure S5 where (a b : S4)
structure S6 where (a b : S5)
structure S7 where (a b : S6)
structure S8 where (a b : S7)
structure S9 where (a b : S8)
structure S10 where (a b : S9)
structure S11 where (a b : S10)
structure S12 where (a b : S11)
def z1 : S1 := S1.mk n0 n0
def z2 : S2 := S2.mk z1 z1
def z3 : S3 := S3.mk z2 z2
def z4 : S4 := S4.mk z3 z3
def z5 : S5 := S5.mk z4 z4
def z6 : S6 := S6.mk z5 z5
def z7 : S7 := S7.mk z6 z6
def z8 : S8 := S8.mk z7 z7
def z9 : S9 := S9.mk z8 z8
def z10 : S10 := S10.mk z9 z9
def z11 : S11 := S11.mk z10 z10
def z12 : S12 := S12.mk z11 z11
noncomputable def g1 (t : S1) (i : Nat) : Nat := Bool.rec t.a t.b (Nat.testBit i b0)
noncomputable def g2 (t : S2) (i : Nat) : Nat := Bool.rec (g1 t.a i) (g1 t.b i) (Nat.testBit i b1)
noncomputable def g3 (t : S3) (i : Nat) : Nat := Bool.rec (g2 t.a i) (g2 t.b i) (Nat.testBit i b2)
noncomputable def g4 (t : S4) (i : Nat) : Nat := Bool.rec (g3 t.a i) (g3 t.b i) (Nat.testBit i b3)
noncomputable def g5 (t : S5) (i : Nat) : Nat := Bool.rec (g4 t.a i) (g4 t.b i) (Nat.testBit i b4)
noncomputable def g6 (t : S6) (i : Nat) : Nat := Bool.rec (g5 t.a i) (g5 t.b i) (Nat.testBit i b5)
noncomputable def g7 (t : S7) (i : Nat) : Nat := Bool.rec (g6 t.a i) (g6 t.b i) (Nat.testBit i b6)
noncomputable def g8 (t : S8) (i : Nat) : Nat := Bool.rec (g7 t.a i) (g7 t.b i) (Nat.testBit i b7)
noncomputable def g9 (t : S9) (i : Nat) : Nat := Bool.rec (g8 t.a i) (g8 t.b i) (Nat.testBit i b8)
noncomputable def g10 (t : S10) (i : Nat) : Nat := Bool.rec (g9 t.a i) (g9 t.b i) (Nat.testBit i b9)
noncomputable def g11 (t : S11) (i : Nat) : Nat := Bool.rec (g10 t.a i) (g10 t.b i) (Nat.testBit i b10)
noncomputable def g12 (t : S12) (i : Nat) : Nat := Bool.rec (g11 t.a i) (g11 t.b i) (Nat.testBit i b11)
noncomputable def uv1 (ms : VMasks) (c : Nat) : S1 := S1.mk (Nat.land c ms.m0) (Nat.land (Nat.shiftRight c vsh0) ms.m0)
noncomputable def uv2 (ms : VMasks) (c : Nat) : S2 := S2.mk (uv1 ms (Nat.land c ms.m1)) (uv1 ms (Nat.shiftRight c vsh1))
noncomputable def uv3 (ms : VMasks) (c : Nat) : S3 := S3.mk (uv2 ms (Nat.land c ms.m2)) (uv2 ms (Nat.shiftRight c vsh2))
noncomputable def uv4 (ms : VMasks) (c : Nat) : S4 := S4.mk (uv3 ms (Nat.land c ms.m3)) (uv3 ms (Nat.shiftRight c vsh3))
noncomputable def uv5 (ms : VMasks) (c : Nat) : S5 := S5.mk (uv4 ms (Nat.land c ms.m4)) (uv4 ms (Nat.shiftRight c vsh4))
noncomputable def uv6 (ms : VMasks) (c : Nat) : S6 := S6.mk (uv5 ms (Nat.land c ms.m5)) (uv5 ms (Nat.shiftRight c vsh5))
noncomputable def uv7 (ms : VMasks) (c : Nat) : S7 := S7.mk (uv6 ms (Nat.land c ms.m6)) (uv6 ms (Nat.shiftRight c vsh6))
noncomputable def uv8 (ms : VMasks) (c : Nat) : S8 := S8.mk (uv7 ms (Nat.land c ms.m7)) (uv7 ms (Nat.shiftRight c vsh7))
noncomputable def uv9 (ms : VMasks) (c : Nat) : S9 := S9.mk (uv8 ms (Nat.land c ms.m8)) (uv8 ms (Nat.shiftRight c vsh8))
noncomputable def uv10 (ms : VMasks) (c : Nat) : S10 := S10.mk (uv9 ms (Nat.land c ms.m9)) (uv9 ms (Nat.shiftRight c vsh9))
noncomputable def uv11 (ms : VMasks) (c : Nat) : S11 := S11.mk (uv10 ms (Nat.land c ms.m10)) (uv10 ms (Nat.shiftRight c vsh10))
noncomputable def uv12 (ms : VMasks) (c : Nat) : S12 := S12.mk (uv11 ms (Nat.land c ms.m11)) (uv11 ms (Nat.shiftRight c vsh11))
noncomputable def pv1 (t : S1) : Nat := Nat.lor t.a (Nat.shiftLeft t.b vsh0)
noncomputable def pv2 (t : S2) : Nat := Nat.lor (pv1 t.a) (Nat.shiftLeft (pv1 t.b) vsh1)
noncomputable def pv3 (t : S3) : Nat := Nat.lor (pv2 t.a) (Nat.shiftLeft (pv2 t.b) vsh2)
noncomputable def pv4 (t : S4) : Nat := Nat.lor (pv3 t.a) (Nat.shiftLeft (pv3 t.b) vsh3)
noncomputable def pv5 (t : S5) : Nat := Nat.lor (pv4 t.a) (Nat.shiftLeft (pv4 t.b) vsh4)
noncomputable def pv6 (t : S6) : Nat := Nat.lor (pv5 t.a) (Nat.shiftLeft (pv5 t.b) vsh5)
noncomputable def pv7 (t : S7) : Nat := Nat.lor (pv6 t.a) (Nat.shiftLeft (pv6 t.b) vsh6)
noncomputable def pv8 (t : S8) : Nat := Nat.lor (pv7 t.a) (Nat.shiftLeft (pv7 t.b) vsh7)
noncomputable def pv9 (t : S9) : Nat := Nat.lor (pv8 t.a) (Nat.shiftLeft (pv8 t.b) vsh8)
noncomputable def pv10 (t : S10) : Nat := Nat.lor (pv9 t.a) (Nat.shiftLeft (pv9 t.b) vsh9)
noncomputable def pv11 (t : S11) : Nat := Nat.lor (pv10 t.a) (Nat.shiftLeft (pv10 t.b) vsh10)
noncomputable def pv12 (t : S12) : Nat := Nat.lor (pv11 t.a) (Nat.shiftLeft (pv11 t.b) vsh11)
noncomputable def mp0 (f : Nat -> Nat) (r : Nat) : Nat := Bool.rec (Nat.land (f r) vm0) n0 (Nat.beq r n0)
noncomputable def mp1 (f : Nat -> Nat) (r : S1) : S1 := S1.mk (mp0 f r.a) (mp0 f r.b)
noncomputable def mp2 (f : Nat -> Nat) (r : S2) : S2 := S2.mk (mp1 f r.a) (mp1 f r.b)
noncomputable def mp3 (f : Nat -> Nat) (r : S3) : S3 := S3.mk (mp2 f r.a) (mp2 f r.b)
noncomputable def mp4 (f : Nat -> Nat) (r : S4) : S4 := S4.mk (mp3 f r.a) (mp3 f r.b)
noncomputable def mp5 (f : Nat -> Nat) (r : S5) : S5 := S5.mk (mp4 f r.a) (mp4 f r.b)
noncomputable def mp6 (f : Nat -> Nat) (r : S6) : S6 := S6.mk (mp5 f r.a) (mp5 f r.b)
noncomputable def mp7 (f : Nat -> Nat) (r : S7) : S7 := S7.mk (mp6 f r.a) (mp6 f r.b)
noncomputable def mp8 (f : Nat -> Nat) (r : S8) : S8 := S8.mk (mp7 f r.a) (mp7 f r.b)
noncomputable def mp9 (f : Nat -> Nat) (r : S9) : S9 := S9.mk (mp8 f r.a) (mp8 f r.b)
noncomputable def mp10 (f : Nat -> Nat) (r : S10) : S10 := S10.mk (mp9 f r.a) (mp9 f r.b)
noncomputable def mp11 (f : Nat -> Nat) (r : S11) : S11 := S11.mk (mp10 f r.a) (mp10 f r.b)
noncomputable def mp12 (f : Nat -> Nat) (r : S12) : S12 := S12.mk (mp11 f r.a) (mp11 f r.b)
noncomputable def al0 (f : Nat -> Nat -> Bool) (r v : Nat) : Bool := Bool.rec (f r v) true (Nat.beq r n0)
noncomputable def al1 (f : Nat -> Nat -> Bool) (r v : S1) : Bool := Bool.rec false (al0 f r.b v.b) (al0 f r.a v.a)
noncomputable def al2 (f : Nat -> Nat -> Bool) (r v : S2) : Bool := Bool.rec false (al1 f r.b v.b) (al1 f r.a v.a)
noncomputable def al3 (f : Nat -> Nat -> Bool) (r v : S3) : Bool := Bool.rec false (al2 f r.b v.b) (al2 f r.a v.a)
noncomputable def al4 (f : Nat -> Nat -> Bool) (r v : S4) : Bool := Bool.rec false (al3 f r.b v.b) (al3 f r.a v.a)
noncomputable def al5 (f : Nat -> Nat -> Bool) (r v : S5) : Bool := Bool.rec false (al4 f r.b v.b) (al4 f r.a v.a)
noncomputable def al6 (f : Nat -> Nat -> Bool) (r v : S6) : Bool := Bool.rec false (al5 f r.b v.b) (al5 f r.a v.a)
noncomputable def al7 (f : Nat -> Nat -> Bool) (r v : S7) : Bool := Bool.rec false (al6 f r.b v.b) (al6 f r.a v.a)
noncomputable def al8 (f : Nat -> Nat -> Bool) (r v : S8) : Bool := Bool.rec false (al7 f r.b v.b) (al7 f r.a v.a)
noncomputable def al9 (f : Nat -> Nat -> Bool) (r v : S9) : Bool := Bool.rec false (al8 f r.b v.b) (al8 f r.a v.a)
noncomputable def al10 (f : Nat -> Nat -> Bool) (r v : S10) : Bool := Bool.rec false (al9 f r.b v.b) (al9 f r.a v.a)
noncomputable def al11 (f : Nat -> Nat -> Bool) (r v : S11) : Bool := Bool.rec false (al10 f r.b v.b) (al10 f r.a v.a)
noncomputable def al12 (f : Nat -> Nat -> Bool) (r v : S12) : Bool := Bool.rec false (al11 f r.b v.b) (al11 f r.a v.a)
def rsTree : S12 := S12.mk (S11.mk (S10.mk (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xdc800c004001) (0xa4801800a004)) (S1.mk (0x74802000e9fb) (0xd68028012001))) (S2.mk (S1.mk (0x8b803401800b) (0x52003c01c9fb)) (S1.mk (0xc88048022010) (0x6d80500269fb)))) (S3.mk (S2.mk (S1.mk (0x8000593f6015) (0x6f006002e9fb)) (S1.mk (0xd18068012019) (0x88807403801b))) (S2.mk (S1.mk (0x41807c03c9fb) (0x950088042020)) (S1.mk (0x5200900469fb) (0x5d80993f6025))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x9680a004e004) (0x5580a402e9fb)) (S1.mk (0xb980ac01202a) (0x6d80b40589fb))) (S2.mk (S1.mk (0x7e00bd3f602e) (0x9e00c400a030)) (S1.mk (0x8a00cc012032) (0x6680d00269fb)))) (S3.mk (S2.mk (S1.mk (0x7a80d93f6035) (0xa3001800a037)) (S1.mk (0xc600e4070019) (0x8880ec07401b))) (S2.mk (S1.mk (0x3e80f40789fb) (0x8680fc04203e)) (S1.mk (0x4a81040809fb) (0x4c010d3f6042)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x69811808a044) (0x4e812008e9fb)) (S1.mk (0x9a812c094049) (0x4a81340989fb))) (S2.mk (S1.mk (0x62013d3f604e) (0x6d814400a050)) (S1.mk (0x62014804e032) (0x45014c01c9fb)))) (S3.mk (S2.mk (S1.mk (0xa90154022054) (0x69815d3f6056)) (S1.mk (0x82816400a058) (0xb5816c0b4019))) (S2.mk (S1.mk (0x6d80b40b89fb) (0x7901793f605d)) (S1.mk (0x96817c094030) (0x7a0184012060))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x82818c018062) (0xc281940c8010)) (S1.mk (0x57019800a9fb) (0x81019d3f6019))) (S2.mk (S1.mk (0x7c01a53f6068) (0x9081ac00a06a)) (S1.mk (0x8900cc0d8032) (0x7e01b80da00b)))) (S3.mk (S2.mk (S1.mk (0x6081c00de9fb) (0xba81c8070071)) (S1.mk (0x3381d00e69fb) (0x7f80fc042075))) (S2.mk (S1.mk (0x4881dc0ec9fb) (0x4781e53f6078)) (S1.mk (0x5b81f00f607a) (0x8401f80fa049))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4382000fe9fb) (0x5802093f6081)) (S1.mk (0x5702000da050) (0x5a821004e083))) (S2.mk (S1.mk (0x528218018085) (0x3e814c03c9fb)) (S1.mk (0x7d0224110087) (0x51022c1149fb)))) (S3.mk (S2.mk (S1.mk (0x5e82353f608c) (0x77023c00a08e)) (S1.mk (0x52024001c9fb) (0xae8248122019))) (S2.mk (S1.mk (0x4a82501269fb) (0x5682593f6095)) (S1.mk (0x70825d3f6030) (0x7301840129fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x3682600189fb) (0x7d82653f6010)) (S1.mk (0x70026d3f609a) (0x4b014d3f6032))) (S2.mk (S1.mk (0x84827404e09c) (0x99827c13c02a)) (S1.mk (0x73028414006a) (0x7882880d8083)))) (S3.mk (S2.mk (S1.mk (0x5282900da0a3) (0xa0829c14c0a5)) (S1.mk (0x4782a41509fb) (0xb602ac0700aa))) (S2.mk (S1.mk (0x6682b41589fb) (0x9382bc0940ae)) (S1.mk (0x7002c4160060) (0xb182cc0c80b2)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x3c82d41689fb) (0x80819d3f60b6)) (S1.mk (0x8502e016e01b) (0x8782e80420b9))) (S2.mk (S1.mk (0x5402f01769fb) (0xaf02f80120bd)) (S1.mk (0x65813d3f60bf) (0x898300070032)))) (S3.mk (S2.mk (S1.mk (0x960308182030) (0x7981840120c3)) (S1.mk (0x5a83140180c4) (0xb4031c18c010))) (S2.mk (S1.mk (0x6f032002e9fb) (0x3083240da9fb)) (S1.mk (0x81032c0420ca) (0x4b03341989fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6d833d3f60ce) (0x8c034400a0d0)) (S1.mk (0xba8348070071) (0x4003501a69fb))) (S2.mk (S1.mk (0x4003593f60d5) (0x5803600f60d7)) (S1.mk (0x4383640fe9fb) (0x58036d3f60da)))) (S3.mk (S2.mk (S1.mk (0x5282000da06d) (0x4f03741b8083)) (S1.mk (0x40037816e085) (0x3d03801be9fb))) (S2.mk (S1.mk (0x6b03881100e1) (0x3583901c69fb)) (S1.mk (0x9d03981220e5) (0x3683a01ce9fb)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4f03a53f60e9) (0x6303ad3f60ea)) (S1.mk (0x5f03b00129fb) (0x4b03b404e9fb))) (S2.mk (S1.mk (0x6503bd3f60ee) (0x3203c00389fb)) (S1.mk (0x5a83c53f6020) (0x7703c804e0da)))) (S3.mk (S2.mk (S1.mk (0x3783d01e69fb) (0x6d03d80fe0f5)) (S1.mk (0x5a03dc0589fb) (0x6203e53f60f8))) (S2.mk (S1.mk (0x6903ec1f406a) (0x7303f40d80fc)) (S1.mk (0x5103fc0da0fe) (0x8e84042000a5))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5a840d3f6102) (0x4004101509fb)) (S1.mk (0xa68418070105) (0x4a813420e9fb))) (S2.mk (S1.mk (0x5684253f6108) (0x670428094050)) (S1.mk (0x5f042c04e060) (0x6e04300c8083)))) (S3.mk (S2.mk (S1.mk (0x4184393f610d) (0x730184012050)) (S1.mk (0x88043c00a09c) (0x78044013c032))) (S2.mk (S1.mk (0x7304453f600b) (0x88044c022112)) (S1.mk (0x4404542289fb) (0x92845c0b4116)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x3b84601be9fb) (0x93046818c119)) (S1.mk (0x7284713f611b) (0x4b847803811d))) (S2.mk (S1.mk (0x5f848023e0ca) (0x96848408a004)) (S1.mk (0x3d848c2449fb) (0xa20494012124)))) (S3.mk (S2.mk (S1.mk (0x45049c24c9fb) (0x5104a53f6128)) (S1.mk (0x8784ac00a12a) (0xb48348258071))) (S2.mk (S1.mk (0x5f04b825a9fb) (0x7284c13f612f)) (S1.mk (0x7384c8018131) (0xb184cc0c80b2))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5984d42689fb) (0x8084dd3f6136)) (S1.mk (0x8d80a004e037) (0xae04e00700bd))) (S2.mk (S1.mk (0x4684e401c9fb) (0x4884ed3f613a)) (S1.mk (0x9b04f4278037) (0x2f84fc27c9fb)))) (S3.mk (S2.mk (S1.mk (0x798504042140) (0x51050816e044)) (S1.mk (0x9a812c094143) (0x5f85142889fb))) (S2.mk (S1.mk (0x69815d3f6146) (0x7f052000a147)) (S1.mk (0xa4816c292019) (0x7385293f6004))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x79852d3f6071) (0x4f85301be9fb)) (S1.mk (0xac05380c814d) (0x34054029e9fb))) (S2.mk (S1.mk (0x4c054816e151) (0x6405502a60b9)) (S1.mk (0x4605582aa9fb) (0x980560012157)))) (S3.mk (S2.mk (S1.mk (0x7a85693f6159) (0x3b820d3f615b)) (S1.mk (0x56857008a050) (0x8d857404e049))) (S2.mk (S1.mk (0x5305780b89fb) (0x5885813f615f)) (S1.mk (0x7d858404e06a) (0x7301840d8050))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6d058c0da162) (0xaa059013c010)) (S1.mk (0xa20598070165) (0x4383640da9fb))) (S2.mk (S1.mk (0x4c85a13f6167) (0x4383642d206d)) (S1.mk (0x4c859c1b816a) (0x3385b016e16b)))) (S3.mk (S2.mk (S1.mk (0x6585b416e0e1) (0x4f05bd3f616e)) (S1.mk (0x6305c53f6170) (0x5085c80229fb))) (S2.mk (S1.mk (0x3085cc0fe9fb) (0x5a05d53f6174)) (S1.mk (0x4705dd3f6176) (0x3d85e42f09fb)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4b014d3f617a) (0x6405f016e17b)) (S1.mk (0x5f05f80fe17d) (0x4186002fe9fb))) (S2.mk (S1.mk (0x3d86053f6147) (0x82060800a147)) (S1.mk (0x9184182fe105) (0x3f060c20e9fb)))) (S3.mk (S2.mk (S1.mk (0x4184393f6184) (0x5f061404e050)) (S1.mk (0x718618018162) (0x66861c13c083))) (S2.mk (S1.mk (0x70026d3f6188) (0x5706253f6112)) (S1.mk (0x79862801809c) (0x66844013c083))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x2d06313f618b) (0x64063409418c)) (S1.mk (0x880638022112) (0x46064031e9fb))) (S2.mk (S1.mk (0x3085cd3f6191) (0x59064c018192)) (S1.mk (0x72065432816e) (0x67065d3f6196)))) (S3.mk (S2.mk (S1.mk (0x758664182198) (0x70066c3340c3)) (S1.mk (0x3686703289fb) (0x85067818c19d))) (S2.mk (S1.mk (0x39868033e9fb) (0x6e84713f61a1)) (S1.mk (0x36868c34411d) (0x5f869423e1a4))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x27869c34c9fb) (0x9506a40121a8)) (S1.mk (0x6906a800a085) (0x5706ac110032))) (S2.mk (S1.mk (0x4b86b53f61ac) (0x7906bc00a1ae)) (S1.mk (0xa586c4360071) (0x4386c825a9fb)))) (S3.mk (S2.mk (S1.mk (0x6486cd3f60ae) (0x6704281609fb)) (S1.mk (0x7806d13f60b2) (0x7006d93f61b5))) (S2.mk (S1.mk (0x6c06dd3f60bd) (0x4406053f6044)) (S1.mk (0x5186e00949fb) (0xa706e40220bf))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5d86e93f6116) (0x6806f00421bb)) (S1.mk (0x6586f53f609c) (0x99827c13c1be))) (S2.mk (S1.mk (0x4406fc0989fb) (0x4f87053f61c0)) (S1.mk (0x6d814400a06d) (0x8c07081b80aa)))) (S3.mk (S2.mk (S1.mk (0x4707113f61c3) (0x6a871804e1c5)) (S1.mk (0x83072038e157) (0x880724018037))) (S2.mk (S1.mk (0x7b0300070083) (0x2987280749fb)) (S1.mk (0x4d872d3f603e) (0x2487343989fb)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6f073c04e1ce) (0xa40740022087)) (S1.mk (0x4d07483a29fb) (0x4007513f61d3))) (S2.mk (S1.mk (0x6087540fa058) (0xb5016c0b40b6)) (S1.mk (0x3b875c3ac9fb) (0x5387653f61d8)))) (S3.mk (S2.mk (S1.mk (0x60876c1101da) (0x5b07743b8085)) (S1.mk (0x5f07780da17b) (0x9d05900fe010))) (S2.mk (S1.mk (0x5987803be9fb) (0x4382000da9fb)) (S1.mk (0x6d87893f61e1) (0x85878c094174))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x70042c160060) (0x71879016e162)) (S1.mk (0x7c879413c0b9) (0x9a879c0701e6))) (S2.mk (S1.mk (0x5787a43d09fb) (0x6a07ad3f61ea)) (S1.mk (0x9b07b0278037) (0x8183000701ed)))) (S3.mk (S2.mk (S1.mk (0x9707b8292071) (0x50810d3f61ef)) (S1.mk (0x4f07c53f61f0) (0x5807c83349fb))) (S2.mk (S1.mk (0x52044001c9fb) (0xc107d00221f3)) (S1.mk (0x3b87d41b89fb) (0x3085cd3f606d))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5407dc0f61f6) (0x7887e02d2049)) (S1.mk (0x5c07e81101f9) (0x7687ec27808e))) (S2.mk (S1.mk (0x6707f43f89fb) (0x7307fd3f61fe)) (S1.mk (0x6908000da06a) (0x4908040da085)))) (S3.mk (S2.mk (S1.mk (0x9a08081100a5) (0x3108104069fb)) (S1.mk (0x730814022083) (0x898818070032))) (S2.mk (S1.mk (0x58840d3f6207) (0x86082404e208)) (S1.mk (0x9d082c4140bd) (0x3e88344189fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x3d083d3f620e) (0x49084007411d)) (S1.mk (0x4d884423e140) (0x2f084c4249fb))) (S2.mk (S1.mk (0x7a0854094214) (0x51085c42c9fb)) (S1.mk (0x5608653f6218) (0x668868018147)))) (S3.mk (S2.mk (S1.mk (0xa0016c2920b6) (0x90887000a21b)) (S1.mk (0x84887843a032) (0x3085cd3f6050))) (S2.mk (S1.mk (0x64087d3f6087) (0x99088012209a)) (S1.mk (0x5b865d3f6221) (0x6e088c182222)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6688900940c3) (0x95089418c054)) (S1.mk (0x7308993f601b) (0x7c089c04215b))) (S2.mk (S1.mk (0xa188a4012228) (0x7308ac00a22a)) (S1.mk (0x8b88b013c165) (0x5808b93f622d)))) (S3.mk (S2.mk (S1.mk (0x4108c045e9fb) (0x2408c43449fb)) (S1.mk (0x2e88c81109fb) (0x2808cc16e9fb))) (S2.mk (S1.mk (0x2f88d53f6234) (0x5488d80fe234)) (S1.mk (0x5f061404e06d) (0x5288dc1b8050))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7188e0038162) (0x5c861c13c1bb)) (S1.mk (0x6008e93f6239) (0x3b856d3f6083))) (S2.mk (S1.mk (0x6588ec01822a) (0x66814c13c083)) (S1.mk (0x5408f008a1f6) (0x3d08f42d218c)))) (S3.mk (S2.mk (S1.mk (0x4188f80fe9fb) (0x4809013f623f)) (S1.mk (0x5709042789fb) (0x63090d3f6242))) (S2.mk (S1.mk (0x5b8910042231) (0x4a891416e192)) (S1.mk (0x6d891c328246) (0x4389200fe9fb)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5189293f6249) (0x48092c110083)) (S1.mk (0x9c0930110010) (0x4a09393f624d))) (S2.mk (S1.mk (0x36893d3f6222) (0x7009413f6054)) (S1.mk (0x8782e804210d) (0x5a89453f6228)))) (S3.mk (S2.mk (S1.mk (0x85894827809c) (0x4f894c13c9fb)) (S1.mk (0x8a095002210d) (0x3509553f607a))) (S2.mk (S1.mk (0x2e09580fa9fb) (0x7809613f6257)) (S1.mk (0x8b896413c239) (0x3c89680989fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5706253f625b) (0x3689701409fb)) (S1.mk (0x3e09753f60a3) (0x5e897814c10d))) (S2.mk (S1.mk (0x3009804be9fb) (0x7609881b8261)) (S1.mk (0x7a09904c60ae) (0x6e02c416016a)))) (S3.mk (S2.mk (S1.mk (0x500998018265) (0x8709a04ce14d)) (S1.mk (0x6789a84d29fb) (0x7809b13f626b))) (S2.mk (S1.mk (0x4289b93f626d) (0x6489bc04e265)) (S1.mk (0x6e09c04ce157) (0x36896820e9fb)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4581d93f6271) (0x8509c8140037)) (S1.mk (0x2809cc2d29fb) (0x3a89d53f6274))) (S2.mk (S1.mk (0x4e09dc4ec050) (0x6f073c04e278)) (S1.mk (0x2909e84f29fb) (0x3109f13f627b)))) (S3.mk (S2.mk (S1.mk (0x5189f80fa27d) (0xac0a004fe0b6)) (S1.mk (0x7b8a053f60a5) (0x6008e93f6282))) (S2.mk (S1.mk (0x5b0a10110283) (0x580a1850a085)) (S1.mk (0x5f0a1c34417b) (0x8c0a240fe288))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x400a283be9fb) (0x8f0a3007028b)) (S1.mk (0x4f0a353f60dd) (0x6e0a380c8083))) (S2.mk (S1.mk (0x6b8a3c070050) (0x858a4027809c)) (S1.mk (0x6e044013c1ed) (0x6c0a44292032)))) (S3.mk (S2.mk (S1.mk (0x5e8a4d3f6292) (0xb980ac0121be)) (S1.mk (0x5d88181b8032) (0x3e8a5008a9fb))) (S2.mk (S1.mk (0x678a553f6049) (0x5d0a580229fb)) (S1.mk (0x7d8a5c278058) (0x518a653f6298))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x530a693f606a) (0x5e8a6c0d89fb)) (S1.mk (0x9b0598258165) (0x510920344050))) (S2.mk (S1.mk (0x518a7004e13e) (0x508a7401811d)) (S1.mk (0x7f0a7823e054) (0x4f8a7c01c9fb)))) (S3.mk (S2.mk (S1.mk (0x8e0a842922a0) (0xa78a8c0222a2)) (S1.mk (0x2806313f62a4) (0x4b8a940fa203))) (S2.mk (S1.mk (0x298a9c54c9fb) (0x298aa53f62a8)) (S1.mk (0x430aac0fa2aa) (0x850ab855a2ac))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x88027c0fe02a) (0x4a8abc0989fb)) (S1.mk (0x5d8ac53f62b0) (0x4d0ac81402a8))) (S2.mk (S1.mk (0x470acc54c083) (0x758ad414c2b4)) (S1.mk (0x490adc56c9fb) (0x3d8ae53f62b8)))) (S3.mk (S2.mk (S1.mk (0x638aec0f62ba) (0x528af02fe203)) (S1.mk (0x4e0af80382bd) (0x6e8b045802bf))) (S2.mk (S1.mk (0x478b0c5849fb) (0x560b153f62c4)) (S1.mk (0x6b0b1804215b) (0x478b2058e9fb)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x660b293f62c9) (0x7f0b2c04e174)) (S1.mk (0x698614160050) (0x9c019c13c0b2))) (S2.mk (S1.mk (0x6a0b30042231) (0x8b88a40942cd)) (S1.mk (0x700b3800a1f6) (0x8a8b3c2d2071)))) (S3.mk (S2.mk (S1.mk (0x6682b45a09fb) (0x690b493f62d1)) (S1.mk (0x7a0b4c00a222) (0x7580cc094032))) (S2.mk (S1.mk (0xba0b540222d4) (0x4b8b5c5ac9fb)) (S1.mk (0xb607080700aa) (0x5b8b60140050))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x608b640180a3) (0x558b6814c083)) (S1.mk (0x668b713f62db) (0x930b7804e2dd))) (S2.mk (S1.mk (0xac0b7c02202a) (0x4b0b853f62e0)) (S1.mk (0x298b893f6085) (0x5e8b901102e3)))) (S3.mk (S2.mk (S1.mk (0x8b8b94122116) (0x5b8b9804e1f6)) (S1.mk (0x6003d82d20f5) (0x8b8ba02002e7))) (S2.mk (S1.mk (0x530ba85d29fb) (0x758bb13f62eb)) (S1.mk (0x8d0bb41820ea) (0x7983b00120c3)))))))))) (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x798bb818c0e9) (0x4d8bbd3f60ca)) (S1.mk (0x8a0bc40122f0) (0x2e0bcc5e49fb))) (S2.mk (S1.mk (0x378bd13f62f4) (0x6e8bd53f602a)) (S1.mk (0x6808b13f6165) (0x680bd8278085)))) (S3.mk (S2.mk (S1.mk (0x6a8bdc0da242) (0x968be0042054)) (S1.mk (0x4d8be458e9fb) (0x928bec2922fa))) (S2.mk (S1.mk (0x4d0bf45f89fb) (0x4186053f62fe)) (S1.mk (0x4887c53f6058) (0x490c005fe9fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x46872d3f6075) (0x470c082d2301)) (S1.mk (0x2f0c106069fb) (0x380c193f6305))) (S2.mk (S1.mk (0x598c1c16e08e) (0x840c24122308)) (S1.mk (0x4b0c2858e9fb) (0x600c313f630b)))) (S3.mk (S2.mk (S1.mk (0x5b0c380da30d) (0x658acc61e083)) (S1.mk (0x7c0c40110020) (0x568c440380c4))) (S2.mk (S1.mk (0xb4031c18c0a5) (0x558c4c6249fb)) (S1.mk (0x6f8c553f6314) (0x5b83640fe050)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x908c5813c105) (0x718c5c2d20ae)) (S1.mk (0x408c6001816b) (0x818c6416e14d))) (S2.mk (S1.mk (0x780c6d3f631a) (0x818c7013c157)) (S1.mk (0x6706f004231d) (0x8b857404e143)))) (S3.mk (S2.mk (S1.mk (0x6906a800a06d) (0x9b0a0063c019)) (S1.mk (0x658c7d3f6162) (0x8f0c8013c0bf))) (S2.mk (S1.mk (0x78014c13c032) (0x658c8403822a)) (S1.mk (0x5c814c13c1bb) (0x4c8c882689fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x520c913f6323) (0x2985a93f61f6)) (S1.mk (0x2e03e93f6325) (0x2406893f6231))) (S2.mk (S1.mk (0x380c9816e1f6) (0x308c9c2d216b)) (S1.mk (0x5f891c2d2246) (0x5c0ca53f6328)))) (S3.mk (S2.mk (S1.mk (0x710ca804218b) (0x700cac278192)) (S1.mk (0x718440328032) (0x7c879413c10d))) (S2.mk (S1.mk (0x5e8cb0110077) (0x418cb93f632d)) (S1.mk (0x4d8cc13f632f) (0x4c0cc93f6331))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x578cd06669fb) (0x658cd93f6335)) (S1.mk (0x700cdc074162) (0x5b861c13c31d))) (S2.mk (S1.mk (0x6c8ce42d2338) (0x448ce814c231)) (S1.mk (0x5a8cec04e06d) (0x710cf063c261)))) (S3.mk (S2.mk (S1.mk (0x4c8cf93f633d) (0x5e83ad3f60d0)) (S1.mk (0x558cfc0709fb) (0x4d8d013f60f5))) (S2.mk (S1.mk (0x8b8bc40120f5) (0x4903642d2050)) (S1.mk (0x5a8d0404e16a) (0x418d0816e083))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x64094c13c050) (0x5c0d0c63c032)) (S1.mk (0xa00d10022335) (0x5d06e93f6345))) (S2.mk (S1.mk (0xa280ac0941be) (0x348d1811016b)) (S1.mk (0x35838d3f60e4) (0x8b8d1c110037)))) (S3.mk (S2.mk (S1.mk (0x6b0a3c070085) (0x818d20328116)) (S1.mk (0x418d253f610e) (0x630d2d3f634a))) (S2.mk (S1.mk (0x418d353f634c) (0x3d8d3823e1bb)) (S1.mk (0x6f0d4009434f) (0x3d0d486a29fb)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x390d513f6353) (0x590d5401806d)) (S1.mk (0x6c8d581b8328) (0x2f0d606ae9fb))) (S2.mk (S1.mk (0x908d680c8359) (0x3e0d6c16e11d)) (S1.mk (0x5b8d7023e0b9) (0x350d786ba9fb)))) (S3.mk (S2.mk (S1.mk (0x860d7c414157) (0x5f8d846c09fb)) (S1.mk (0x740d8d3f6362) (0x8b8d946c8037))) (S2.mk (S1.mk (0x820300070366) (0x4c892034406d)) (S1.mk (0x480d9c1b813e) (0x758da423e368))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7b8dac29236a) (0x560db53f636c)) (S1.mk (0xa78db8022119) (0x2f84f93f613f))) (S2.mk (S1.mk (0x498dbc0f616b) (0x390dc016e203)) (S1.mk (0x3085cc0da9fb) (0x560dc93f6371)))) (S3.mk (S2.mk (S1.mk (0x3c8dcc2d22aa) (0x2d8dd46e89fb)) (S1.mk (0x2e0d5d3f6376) (0x3b8de06ee2a8))) (S2.mk (S1.mk (0x2d8de854c379) (0x400df00da37b)) (S1.mk (0x610df86fa2b4) (0x390dfc1509fb)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x9c8e04070380) (0x73018401218c)) (S1.mk (0x700e0800a192) (0x418e0c3442bd))) (S2.mk (S1.mk (0x688e14580384) (0x378e1c70c9fb)) (S1.mk (0x478e253f6388) (0x568e2c04238a)))) (S3.mk (S2.mk (S1.mk (0x868e304ec004) (0xa188a401238d)) (S1.mk (0x4c0e3d3f638e) (0x5e0e4400a390))) (S2.mk (S1.mk (0x7288b0724165) (0x5f06141609fb)) (S1.mk (0x5d8e4d3f61e6) (0x79052d3f6394))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x990e58022395) (0x728e5d3f60aa)) (S1.mk (0x6d05293f6037) (0x6b0a3c0709fb))) (S2.mk (S1.mk (0x4881d93f6077) (0x770e60122032)) (S1.mk (0x6e8bd53f61be) (0x990e6414c2e7)))) (S3.mk (S2.mk (S1.mk (0x648e68182050) (0x5f0e6c04e0c3)) (S1.mk (0x650e7018c083) (0x6b0e793f639d))) (S2.mk (S1.mk (0x5e83bd3f639f) (0x5a8e853f63a0)) (S1.mk (0x728e8c13c3a2) (0x590e953f63a4)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8d8b7804e037) (0x918ea074e3a6)) (S1.mk (0x6e0ea404e044) (0xa280ac09402a))) (S2.mk (S1.mk (0x2e035d3f60d7) (0x4a0ead3f63aa)) (S1.mk (0x2f0eb01f89fb) (0x2e03e93f63ad)))) (S3.mk (S2.mk (S1.mk (0x2e0eb41f49fb) (0x2f0eb13f60fc)) (S1.mk (0x2d0eb93f60fe) (0x4d0ebc2000e4))) (S2.mk (S1.mk (0x848ec011009c) (0x298ec87629fb)) (S1.mk (0x610ed013c3b3) (0x538ed93f63b5))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6b0ee13f63b7) (0x650ee87729fb)) (S1.mk (0x5a0ef13f63bb) (0x4d8d013f63bd))) (S2.mk (S1.mk (0x68011808a147) (0x7d8ef82fe124)) (S1.mk (0x5f0efc25a9fb) (0x538f053f63c0)))) (S3.mk (S2.mk (S1.mk (0x480f0c2d23c2) (0x4a8f1029e16a)) (S1.mk (0x3a8f140da16b) (0x770f1c16e3c6))) (S2.mk (S1.mk (0x630f253f63c8) (0x3e0f293f6151)) (S1.mk (0x4b8f2c2a618b) (0x5a8f3008a192))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2f0f3879a9fb) (0x730f403283cf)) (S1.mk (0x558f487a29fb) (0x588f513f63d3))) (S2.mk (S1.mk (0x650f587aa192) (0x670f5c32810e)) (S1.mk (0x7a0f6004e338) (0x458f645d29fb)))) (S3.mk (S2.mk (S1.mk (0x550e853f63da) (0x748f6c04e331)) (S1.mk (0x6383b0666050) (0x8e026c13c054))) (S2.mk (S1.mk (0x7887e02d2143) (0x680bd827806d)) (S1.mk (0x848f701100bf) (0xa10f74070116))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6707f41269fb) (0x7b0f782d2030)) (S1.mk (0x73018401216a) (0x940f7c16e010))) (S2.mk (S1.mk (0x908f8404e3e0) (0xa50f880c802a)) (S1.mk (0x52003c03c9fb) (0x5a04253f63e3)))) (S3.mk (S2.mk (S1.mk (0x5a8f913f6119) (0x688f9423e020)) (S1.mk (0x5e8f9d3f63e6) (0x758fa0344037))) (S2.mk (S1.mk (0x6d830007013e) (0x898fa403800b)) (S1.mk (0xa901540223ea) (0xa40fac0b4314)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x568fb13f622a) (0x3d038013c9fb)) (S1.mk (0x2f0fb53f61bb) (0x580fb93f617b))) (S2.mk (S1.mk (0x5f05f80fe325) (0x810fbc1b8105)) (S1.mk (0x6a8fc0110112) (0x908fc408a2dd)))) (S3.mk (S2.mk (S1.mk (0x828fc80221a8) (0x4c0fcc1589fb)) (S1.mk (0x630fd53f63f4) (0x870fd804e0ae))) (S2.mk (S1.mk (0x698428160050) (0x9c0fdc13c14d)) (S1.mk (0x830fe004e157) (0x5d8fe404e18c))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x518fe80fa192) (0xa40fec3280b6)) (S1.mk (0x338ff47f89fb) (0x35838d3f63fe))) (S2.mk (S1.mk (0x470ffc110085) (0x818a440b4032)) (S1.mk (0x7890013f62e7) (0x73100413c32f)))) (S3.mk (S2.mk (S1.mk (0x898ce413c402) (0x5b02553f6403)) (S1.mk (0x8c101000a0d0) (0xae101474e0aa))) (S2.mk (S1.mk (0x4a90180989fb) (0x5d8a4d3f6407)) (S1.mk (0x4f1020140085) (0x5990243be9fb))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5a102d3f640a) (0x4310305e42aa)) (S1.mk (0x50903455a32d) (0x34103c81c9fb))) (S2.mk (S1.mk (0x3710453f6410) (0x4510481f42a8)) (S1.mk (0x40104c54c0fc) (0x5b1050200176)))) (S3.mk (S2.mk (S1.mk (0x7e105416e037) (0x92905c070416)) (S1.mk (0x5690653f6418) (0x70106c0f641a))) (S2.mk (S1.mk (0x601070772203) (0x4890741f42bd)) (S1.mk (0x6c107c58041e) (0x4210848409fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7690880942f0) (0x5190902a6423)) (S1.mk (0x66909884a9fb) (0x6290a13f6427))) (S2.mk (S1.mk (0x8510a400a058) (0x8183005fe032)) (S1.mk (0x8c10a8360116) (0x8210ac0c816e)))) (S3.mk (S2.mk (S1.mk (0x4c10b13f60b9) (0x7190b841442d)) (S1.mk (0x8b90bc6c8037) (0x7a0300070430))) (S2.mk (S1.mk (0x7d045c292345) (0x3e90c40f69fb)) (S1.mk (0x2810c84069fb) (0x5a90cc0429fb)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xa188a40122cd) (0x6210d013c18b)) (S1.mk (0x5710d93f6435) (0x5e90dc04e192))) (S2.mk (S1.mk (0x4f894c328050) (0x3210e13f6192)) (S1.mk (0x3c10e4110231) (0x3910ed3f643a)))) (S3.mk (S2.mk (S1.mk (0x6a90f004e22a) (0x64038013c050)) (S1.mk (0x8401f80fa143) (0x8490f414c335))) (S2.mk (S1.mk (0x6003d80fe325) (0x4108c011006d)) (S1.mk (0x4d90f81b8085) (0x5690fc0f6050))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5d8fe404e203) (0x4f11000182bd)) (S1.mk (0x5e9104580083) (0x55110802e9fb))) (S2.mk (S1.mk (0x6391113f6443) (0x7311153f62dd)) (S1.mk (0x5f91180229fb) (0x710ca80422a4)))) (S3.mk (S2.mk (S1.mk (0x6a111c2782aa) (0x79912055a116)) (S1.mk (0x5591242d234f) (0x6511293f63ea))) (S2.mk (S1.mk (0x6511301b844b) (0x5a8cec04e085)) (S1.mk (0x4708c0110050) (0x6808b13f644d))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x601138328083) (0x6511413f644f)) (S1.mk (0x4091453f642d) (0x5d11493f6380))) (S2.mk (S1.mk (0xa98b7c0221be) (0x6d114c27806d)) (S1.mk (0x3c91513f617d) (0x8d9154022323)))) (S3.mk (S2.mk (S1.mk (0x7a0f741b8116) (0x3811593f6060)) (S1.mk (0x72115d3f6062) (0x5d11600c89fb))) (S2.mk (S1.mk (0x4411653f61c5) (0x51916838e9fb)) (S1.mk (0x38116d3f61ce) (0x4791713f6058))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x8511740b4292) (0x2991780749fb)) (S1.mk (0x4791813f645f) (0x4391853f61da))) (S2.mk (S1.mk (0x3f11883b89fb) (0x6082553f62a2)) (S1.mk (0x7f118c13c174) (0x3591948c89fb)))) (S3.mk (S2.mk (S1.mk (0x38919d3f6466) (0x6a871804e468)) (S1.mk (0x7d11a88d21e6) (0x4711ad3f6140))) (S2.mk (S1.mk (0x6e11b409446c) (0x4191bc8dc9fb)) (S1.mk (0x3d07513f6470) (0x8411c8292471)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x530ba81989fb) (0x7091d13f6473)) (S1.mk (0x8391d400a1da) (0x7306ac3b8032))) (S2.mk (S1.mk (0x4511dc8ec9fb) (0xa591e4022478)) (S1.mk (0x5711e82789fb) (0x5a05d53f647b)))) (S3.mk (S2.mk (S1.mk (0x7211f016e09c) (0x660e8c13c46c)) (S1.mk (0x6991f404e147) (0x8511f82923a6))) (S2.mk (S1.mk (0x6311fd3f6131) (0x4f12000c89fb)) (S1.mk (0xa0920438e02a) (0x5512093f60e1))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x3912113f6483) (0x63921404e2e0)) (S1.mk (0x5b85cc0fe050) (0x48121820013f))) (S2.mk (S1.mk (0x36122090e9fb) (0x3612293f6489)) (S1.mk (0x3392313f648b) (0x2392347249fb)))) (S3.mk (S2.mk (S1.mk (0x45123d3f648e) (0x2392449209fb)) (S1.mk (0x2f924d3f6492) (0x2812513f611d))) (S2.mk (S1.mk (0x49125423e15b) (0x1d925c92c9fb)) (S1.mk (0x6a12642fe498) (0x48126d3f649a)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6e127000a2e3) (0x9b052c1be071)) (S1.mk (0x84927414c0bf) (0x4292782a638a))) (S2.mk (S1.mk (0x54127c4ec192) (0x6c8f403284a0)) (S1.mk (0x4212889429fb) (0x3b92913f64a3)))) (S3.mk (S2.mk (S1.mk (0x5112947aa390) (0x5a0d2472410e)) (S1.mk (0x238e293f616b) (0x66929816e338))) (S2.mk (S1.mk (0x8b929c022371) (0x6192a009406d)) (S1.mk (0x5b12a46ee331) (0x578cd0666379))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x2392a93f637b) (0x6d92ac6fa0bf)) (S1.mk (0x2392b49589fb) (0x5c84402d2032))) (S2.mk (S1.mk (0x8b92b82780d0) (0x7212bd3f63e0)) (S1.mk (0xa18f880c81be) (0x818818258032)))) (S3.mk (S2.mk (S1.mk (0x6692c13f6105) (0x9012c4022124)) (S1.mk (0x7212c93f614d) (0x7012d13f64b3))) (S2.mk (S1.mk (0x5592d53f6157) (0x7e12d81f4037)) (S1.mk (0x7403000700f3) (0x6d12dc0da09c)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6992e00f6044) (0x640634094203)) (S1.mk (0x4e12e40182aa) (0x79112055a345))) (S2.mk (S1.mk (0x6912e800a2a8) (0x5712ec54c032)) (S1.mk (0x7892f001812a) (0x5212f40de9fb)))) (S3.mk (S2.mk (S1.mk (0xaf07082584be) (0x8012fc110054)) (S1.mk (0x571300110147) (0x5993042fe085))) (S2.mk (S1.mk (0x2810c93f64c2) (0x2b13113f64c3)) (S1.mk (0x34931823e4c5) (0x5a13202fe4c7))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x819324022325) (0x3593286a29fb)) (S1.mk (0x3293313f64cb) (0x4393380384cd))) (S2.mk (S1.mk (0x6790a899e345) (0x60934009411d)) (S1.mk (0x45134423e060) (0x7a9348344062)))) (S3.mk (S2.mk (S1.mk (0x6204300c813e) (0x5a134c0de9fb)) (S1.mk (0x7213553f64d4) (0x69935833e1c5))) (S2.mk (S1.mk (0x64135c38e4c2) (0x5193600184c3)) (S1.mk (0x8693640b43c8) (0x6b136d3f64da))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6b13702d247b) (0x52937441416a)) (S1.mk (0x3b137803816b) (0x56938016e4df))) (S2.mk (S1.mk (0x5993893f64e1) (0x4593913f64e3)) (S1.mk (0x77139404e17b) (0x6308d80fe42d)))) (S3.mk (S2.mk (S1.mk (0x7193981100d0) (0x5f8cfc070085)) (S1.mk (0x3c139c23e31d) (0x5813a40fa4e8))) (S2.mk (S1.mk (0x5e93a814c077) (0x3693ac6a29fb)) (S1.mk (0x3713b53f64ec) (0x59021801806d))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7013b863c345) (0x5c13bc0589fb)) (S1.mk (0x6413c53f64f0) (0x5793cc1404f2))) (S2.mk (S1.mk (0x6691389e8083) (0x52044003c9fb)) (S1.mk (0x7893d814c4f5) (0x4e13e13f64f7)))) (S3.mk (S2.mk (S1.mk (0x8c93e455a09a) (0x5213ed3f64fa)) (S1.mk (0x638aec0f6222) (0x8613f0580054))) (S2.mk (S1.mk (0x890bc4012325) (0x7985981b8165)) (S1.mk (0x8213f40c816e) (0x8193f801242d)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8513fc16e00b) (0x8f044c022368)) (S1.mk (0xa414000b40e5) (0x6714093f6501))) (S2.mk (S1.mk (0x67140c38e050) (0x7594100941ce)) (S1.mk (0x6d9414018058) (0x7014180b4083)))) (S3.mk (S2.mk (S1.mk (0x86941c02233d) (0x8680fc042508)) (S1.mk (0x79942408a09c) (0xaf02ac5fe0aa))) (S2.mk (S1.mk (0x4f942813c9fb) (0x2810c93f618c)) (S1.mk (0x4a142c0429fb) (0x8c1430360165))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6c943413c325) (0xa4074002250e)) (S1.mk (0x9514404fe50f) (0x5394493f6511))) (S2.mk (S1.mk (0x72944c094222) (0x6e02c4094060)) (S1.mk (0xa394500c8054) (0x8f1454414228)))) (S3.mk (S2.mk (S1.mk (0x7d1458292054) (0x70145d3f62ac)) (S1.mk (0x59146014c0e4) (0xa11464070116))) (S2.mk (S1.mk (0x3c146ca349fb) (0x3614713f6484)) (S1.mk (0x36893d3f62ba) (0x4d14753f62bf))))))))))) (S10.mk (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x69911802218c) (0x81147804e228)) (S1.mk (0x6e147c00a2aa) (0x6b948004e222))) (S2.mk (S1.mk (0xaa059013c0a5) (0x969484258380)) (S1.mk (0x53948d3f6522) (0x6b025d3f6524)))) (S3.mk (S2.mk (S1.mk (0x5a94993f6525) (0x6614a13f6527)) (S1.mk (0x6814a43440d0) (0x6b081807013e))) (S2.mk (S1.mk (0x4d0ebc2003fe) (0x5894a81b83b3)) (S1.mk (0x4094b0a569fb) (0x3b12293f652d))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x3b14bd3f652e) (0x3e94c4a609fb)) (S1.mk (0x4b94cd3f6532) (0x3814d53f6534))) (S2.mk (S1.mk (0x5914d82d21a8) (0x8894dc0221f9)) (S1.mk (0x6214e00381ae) (0xa506c4360394)))) (S3.mk (S2.mk (S1.mk (0x6714e404e3c2) (0x5994e829e050)) (S1.mk (0x6d14ec344162) (0x8014f413c53c))) (S2.mk (S1.mk (0x5a14fd3f653e) (0x4915002a64c3)) (S1.mk (0x54950433e050) (0x7b150c04e542)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4e9514a889fb) (0x47151d3f6546)) (S1.mk (0x8d1520328257) (0x45952416e07a))) (S2.mk (S1.mk (0x6415280fa214) (0x6d952c0589fb)) (S1.mk (0x7615353f654c) (0x73153814021b)))) (S3.mk (S2.mk (S1.mk (0x73153c43a083) (0xa0954014c010)) (S1.mk (0x650a301b828b) (0x6f95441b81e6))) (S2.mk (S1.mk (0x5e154809416b) (0x4c954c0181f6)) (S1.mk (0x7795502d2471) (0x9e9558022555))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4a955c7aa9fb) (0x4895613f62e3)) (S1.mk (0x2987d93f616a) (0x670a553f6143))) (S2.mk (S1.mk (0x7095640fa2cd) (0x621568140222)) (S1.mk (0x618288094083) (0x6a956c14c112)))) (S3.mk (S2.mk (S1.mk (0x32157014c9fb) (0x4895742d2325)) (S1.mk (0x3e957816e06d) (0x4b957c1b816b))) (S2.mk (S1.mk (0x71958013c112) (0x8a12c402234f)) (S1.mk (0x5815893f6561) (0x64158d3f63c6))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5895902a610d) (0x4e15953f63cf)) (S1.mk (0x66959d3f6566) (0x7195a01f409c))) (S2.mk (S1.mk (0x62844013c0f3) (0x6e88140221bb)) (S1.mk (0x6f8c553f650f) (0x7f15a4200335)))) (S3.mk (S2.mk (S1.mk (0x7395ac1b856a) (0x6795b00b413f)) (S1.mk (0x5d894c13c18c) (0x6295b404e2e3))) (S2.mk (S1.mk (0x77118c1be174) (0x7095b827822a)) (S1.mk (0x4e01e53f6261) (0x7715bc03809c))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5c844013c1bb) (0x4b11382d2083)) (S1.mk (0x71814c1be032) (0x7c95c13f61f3))) (S2.mk (S1.mk (0x3c95c432816b) (0x92827c32802a)) (S1.mk (0x4615c93f6366) (0x5a90cc04216b)))) (S3.mk (S2.mk (S1.mk (0x6a06dd3f6573) (0x4815d023e083)) (S1.mk (0x5e95d93f6575) (0x3e15dc55a16a))) (S2.mk (S1.mk (0x4c15e014c1bb) (0x9d95e8070579)) (S1.mk (0x2e830d3f657b) (0x5690fc0f606d)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4c15f01b8203) (0x5391045801bb)) (S1.mk (0x4795f93f657d) (0x78014c13c17a))) (S2.mk (S1.mk (0x3d15fc0fe9fb) (0x3d16053f6580)) (S1.mk (0x3e1608344085) (0x43160c11013e)))) (S3.mk (S2.mk (S1.mk (0x4908f80da11d) (0x4116100fe9fb)) (S1.mk (0x8a16142d22fa) (0x3b88f42d2203))) (S2.mk (S1.mk (0x40961816e2aa) (0x80161c55a308)) (S1.mk (0x4396200fe9fb) (0x5196293f6589))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x47162c0da2a8) (0x7a163004e0d0)) (S1.mk (0x91963474e3a6) (0x8816380f6030))) (S2.mk (S1.mk (0x730184012203) (0x9c163c5800a5)) (S1.mk (0x509644b209fb) (0x4c01e53f6592)))) (S3.mk (S2.mk (S1.mk (0x73965004e593) (0xa30b7cb2a02a)) (S1.mk (0x6316593f6395) (0x5e965c0da22a))) (S2.mk (S1.mk (0x711660022231) (0x7b96641103ea)) (S1.mk (0xa1070825859a) (0x4f942813c16b)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5d8e4d3f659b) (0xb116740b459c)) (S1.mk (0x4816780fe16b) (0x48167c1101f6))) (S2.mk (S1.mk (0x4396802d2085) (0x6b968413c112)) (S1.mk (0x5416881b84c7) (0x4116100da9fb)))) (S3.mk (S2.mk (S1.mk (0x4196913f65a3) (0x438d482d211d)) (S1.mk (0x37169423e16a) (0x2d062c34416b))) (S2.mk (S1.mk (0x3c169816e13e) (0x28169d3f6169)) (S1.mk (0x5116a033e37b) (0x3a16a46fa4c2))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x2816a898a9fb) (0x2386893f65ab)) (S1.mk (0x3596b06ee4c3) (0x3b96b4328379))) (S2.mk (S1.mk (0x2e16b93f631d) (0x5c96c004e5af)) (S1.mk (0x1e96c8b629fb) (0x2487313f61cd)))) (S3.mk (S2.mk (S1.mk (0x4916cc0fa06d) (0x6f16d063c3c8)) (S1.mk (0x4816d81105b5) (0x5496e0b6e085))) (S2.mk (S1.mk (0x8396e40fe0bf) (0x95049401234f)) (S1.mk (0x5416e816e4e8) (0x5416ec14c1f5)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5288040da06d) (0x5316f4b789fb)) (S1.mk (0x4296fd3f65be) (0x4297006ee4f2))) (S2.mk (S1.mk (0x4996b49e8379) (0x6097046fa4f5)) (S1.mk (0x79970855a1e6) (0x880bd40fe02a)))) (S3.mk (S2.mk (S1.mk (0x7297113f65c3) (0x6d17185805c5)) (S1.mk (0x1d971c23e9fb) (0x7f17240125c8))) (S2.mk (S1.mk (0x28125023a9fb) (0x24172d3f65ca)) (S1.mk (0xa3173013c1f3) (0x5d0a5802216b))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7c1734360032) (0xa38fac0b450f)) (S1.mk (0x631738414050) (0x84973c6c809c))) (S2.mk (S1.mk (0x66844013c430) (0x5a9418292083)) (S1.mk (0xa097440225d0) (0x7e974802215b)))) (S3.mk (S2.mk (S1.mk (0x7d174c1103c6) (0x57175020010d)) (S1.mk (0x7b17593f65d5) (0x5d08e93f65d7))) (S2.mk (S1.mk (0x7f97600fe2a2) (0x5e17693f65d9)) (S1.mk (0x87176c27812a) (0x79143413c0f5))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x679770110323) (0x6717793f65dd)) (S1.mk (0x2c977c4c69fb) (0x3397813f6265))) (S2.mk (S1.mk (0x2d17844ce9fb) (0x2f97884ec9fb)) (S1.mk (0x33116d3f6278) (0x32978d3f627d)))) (S3.mk (S2.mk (S1.mk (0x6a17904fe249) (0x92827c3281be)) (S1.mk (0x4117993f65e5) (0x3d979d3f6283))) (S2.mk (S1.mk (0x3697a050a9fb) (0x2396ac3449fb)) (S1.mk (0x4e17a93f65e9) (0x1e97ac6f29fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6f97b53f65ec) (0x5497bd3f65ee)) (S1.mk (0x6897c004207a) (0x6797c93f65f1))) (S2.mk (S1.mk (0x8117d02785f3) (0x7b0818bea032)) (S1.mk (0x6b17dc23e5f6) (0x7817e53f65f8)))) (S3.mk (S2.mk (S1.mk (0x5897e84ce10d) (0x9e97f00705fb)) (S1.mk (0x7f17f404e22d) (0x6608c045e050))) (S2.mk (S1.mk (0x7b06e813c16e) (0x5f97fd3f65fe)) (S1.mk (0x3a18013f6423) (0x56857008a06d)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5298081b8601) (0x67180c038058)) (S1.mk (0x6798105fe1bb) (0x40157816e050))) (S2.mk (S1.mk (0x56181404e16b) (0x7a9818042112)) (S1.mk (0x7d181c13c323) (0x38116d3f6301)))) (S3.mk (S2.mk (S1.mk (0x4198213f608e) (0x5f98241220e4)) (S1.mk (0x6f98280fe34f) (0x4118313f660b))) (S2.mk (S1.mk (0x4218353f630d) (0x3d983861e9fb)) (S1.mk (0x7614841b8380) (0x6a18413f660f))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x77184418234a) (0x64094c13c0c3)) (S1.mk (0x3d18493f60c4) (0x72184c18c34c))) (S2.mk (S1.mk (0x379854c289fb) (0x65185d3f6616)) (S1.mk (0x7d986045e34f) (0x59186416806d)))) (S3.mk (S2.mk (S1.mk (0x5618681b8366) (0x7f986c13c56a)) (S1.mk (0x4d98702d2222) (0x61987409416a))) (S2.mk (S1.mk (0x780f4013c3cf) (0x8418781b80bd)) (S1.mk (0x930fec2d20b6) (0x798504042176))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xa002ac2fe0aa) (0x7c187c018170)) (S1.mk (0x7306ac022083) (0x7818813f62a0))) (S2.mk (S1.mk (0x8d161c55a257) (0x7f988414c020)) (S1.mk (0x6118893f63a6) (0x80188c11002a)))) (S3.mk (S2.mk (S1.mk (0x5b989008a07a) (0x831894022077)) (S1.mk (0x5889453f62cd) (0x5b18993f6338))) (S2.mk (S1.mk (0x7f189c13c28b) (0x818d20328345)) (S1.mk (0x7118a008a0da) (0x8218a4278058))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x958e045fe380) (0x6b13702d2174)) (S1.mk (0x5f042c16016a) (0x8998a816e0b2))) (S2.mk (S1.mk (0x8b18ac13c1e6) (0x8998b063c2fa)) (S1.mk (0x8998b413c3a6) (0x54894c13c085)))) (S3.mk (S2.mk (S1.mk (0x6a18b82fe34f) (0x9883481b8071)) (S1.mk (0x4389200da9fb) (0x4818bd3f6367))) (S2.mk (S1.mk (0x3b98c011016a) (0x4c18c432818c)) (S1.mk (0x8818c863c09a) (0x7f18cc2000bf)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x7f18d016e054) (0x8388b01be165)) (S1.mk (0x6192a0094085) (0x4918d4110060))) (S2.mk (S1.mk (0x7c18d80da062) (0x6998dc08a1c5)) (S1.mk (0x64135c38e18c) (0x7498e004e1da)))) (S3.mk (S2.mk (S1.mk (0x5b05c83b8050) (0x7498e413c33d)) (S1.mk (0x6318e899e328) (0x4818ec20e9fb))) (S2.mk (S1.mk (0x4c18f53f663c) (0x4998f84c611d)) (S1.mk (0x4018fc344265) (0x4799004ce13e))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5299043be9fb) (0x4d190d3f6642)) (S1.mk (0x58191033e265) (0x4699144ce4c2))) (S2.mk (S1.mk (0x4199184c64c3) (0x4495c432816a)) (S1.mk (0x5c991c4fe32d) (0x7d827c2d202a)))) (S3.mk (S2.mk (S1.mk (0x6d99200fe5e9) (0x75992416e3ea)) (S1.mk (0x61192d3f664a) (0x6897c00421f6))) (S2.mk (S1.mk (0x7219301b817b) (0x7819340fe228)) (S1.mk (0x6899382785b5) (0x66814cb6e032))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x54193c4ce4e8) (0x61087d3f65f6)) (S1.mk (0x57102014006d) (0x7d194063c054))) (S2.mk (S1.mk (0x5c13bc0b89fb) (0x5a99493f6651)) (S1.mk (0x55194c4c64f2) (0x5415c49e816a)))) (S3.mk (S2.mk (S1.mk (0x851954070654) (0x431958110234)) (S1.mk (0x6a1960122657) (0x7919693f6659))) (S2.mk (S1.mk (0x8c8308182524) (0x6d8a3c0700c3)) (S1.mk (0x93046818c525) (0x6019713f665b))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa204940123e6) (0x7919742d2165)) (S1.mk (0x6b99793f6308) (0x5c197c11010d))) (S2.mk (S1.mk (0x7d198074e261) (0x67998804e661)) (S1.mk (0x9b0f88cc602a) (0x5599953f6664)))) (S3.mk (S2.mk (S1.mk (0x4396780fe9fb) (0x81199863c0e5)) (S1.mk (0x74999c16e119) (0x7c19a013c34f))) (S2.mk (S1.mk (0x3b99a53f634f) (0x5999a832813f)) (S1.mk (0x4c09353f61f9) (0x5819b13f666b)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8499b413c2cd) (0x6599b808a22a)) (S1.mk (0x5d838013c18c) (0x5b96780fe050))) (S2.mk (S1.mk (0x6a19bc0944e8) (0x4d99c063c083)) (S1.mk (0x7599c400a4f2) (0x7804409e8032)))) (S3.mk (S2.mk (S1.mk (0x7f19c8022192) (0x7d8fc80224c7)) (S1.mk (0x6119cc00a4cd) (0x6d943099e165))) (S2.mk (S1.mk (0x7599d01b8579) (0x6519d40fe112)) (S1.mk (0x8199d813c335) (0x7819dc02218b))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6e1118022050) (0x4901e53f6654)) (S1.mk (0x3f89693f61ed) (0x7c99e0278147))) (S2.mk (S1.mk (0x4719e53f63a2) (0x6d11153f6037)) (S1.mk (0x5f19e874e9fb) (0x3999ed3f63b3)))) (S3.mk (S2.mk (S1.mk (0x5219f13f6124) (0x5d19f434412a)) (S1.mk (0xb38348258394) (0x3499f93f63c2))) (S2.mk (S1.mk (0x5b9a013f667f) (0x489a041f4192)) (S1.mk (0x5a11dc3280f3) (0x479a0d3f6682)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4c0cc93f65f3) (0x4b1a10bea9fb)) (S1.mk (0x489a193f6685) (0x4d8d013f6687))) (S2.mk (S1.mk (0x4a9a253f6688) (0xa013b874e116)) (S1.mk (0x3d1a28200231) (0x789a2c0703b3)))) (S3.mk (S2.mk (S1.mk (0x4c9a353f668c) (0x5e9a393f641a)) (S1.mk (0x4c90707729fb) (0x4d9a3d3f641e))) (S2.mk (S1.mk (0x8c9a4013c3ea) (0x959484258691)) (S1.mk (0x9e1a480c83c6) (0x8a97240123cf))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4a9a4c0989fb) (0x620cd93f6694)) (S1.mk (0x570b6014006d) (0x5c1a540380a3))) (S2.mk (S1.mk (0x859a5814c3ea) (0x4e9a60d2e9fb)) (S1.mk (0x5d1a640c89fb) (0x709a6813c15b)))) (S3.mk (S2.mk (S1.mk (0x7d827c2d21be) (0x73143413c2f0)) (S1.mk (0x799a6c04e12a) (0x701a702781f6))) (S2.mk (S1.mk (0xa31a7400a037) (0xae1a7874e0aa)) (S1.mk (0x4c9a7d3f6246) (0x481a80110325)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x489a853f64df) (0x78044013c17a)) (S1.mk (0x5e9a884fe2e0) (0x5188b93f647b))) (S2.mk (S1.mk (0x469a90d469fb) (0x411a993f66a5)) (S1.mk (0x3d11453f66a7) (0x2f84fd3f613e)))) (S3.mk (S2.mk (S1.mk (0x571aa023e271) (0x3b1aa93f66a9)) (S1.mk (0x2410c93f61a2) (0x2385ad3f638a))) (S2.mk (S1.mk (0x391aac4ce390) (0x471ab53f66ac)) (S1.mk (0x2810c93f6203) (0x251ab93f62aa))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6b9abc55a112) (0x1d0e40d609fb)) (S1.mk (0x238e493f648d) (0x561ac53f62b4))) (S2.mk (S1.mk (0x7a1acc0706b2) (0x2d9ad13f62bd)) (S1.mk (0x561ad4580325) (0x301adcd6c9fb)))) (S3.mk (S2.mk (S1.mk (0x3f89693f66b8) (0x9188a4012246)) (S1.mk (0x4a9ae4122231) (0x5e8f9c0fe34f))) (S2.mk (S1.mk (0x669ae81589fb) (0x5b9af13f66bb)) (S1.mk (0x521af418238a) (0x411af82d20c3))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x531afc18c390) (0x619b0045e5c8)) (S1.mk (0x63186c2d256a) (0x88048408a037))) (S2.mk (S1.mk (0x6b0a3c07018c) (0x581b0404e37b)) (S1.mk (0x5a9b086fa3cf) (0x251b0d3f65af)))) (S3.mk (S2.mk (S1.mk (0x298b893f606d) (0x9b0a0063c0b6)) (S1.mk (0x2b1b113f65b5) (0x2b1b14b6e9fb))) (S2.mk (S1.mk (0x959b18022228) (0x50189d3f628b)) (S1.mk (0x6b1b1d3f6471) (0x889b240226c8))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x679b2804e0a3) (0x8e9b2c14c02a)) (S1.mk (0x921b3004e1be) (0x6d05f80fe0f5))) (S2.mk (S1.mk (0x651b340944c7) (0x8e9b3833e004)) (S1.mk (0x7301840124c2) (0x641b3c00a4c3)))) (S3.mk (S2.mk (S1.mk (0x8d88a4094228) (0x6e9b4011006a)) (S1.mk (0x6d1b440d8085) (0x9917300fe1f3))) (S2.mk (S1.mk (0x6c94343280f5) (0x761b4808a0d0)) (S1.mk (0x678cfc07018c) (0x359b513f66d3)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2f1b5423e16b) (0x349b5d3f66d6)) (S1.mk (0x3b83713f61f5) (0x3e1b606fa1bb))) (S2.mk (S1.mk (0x751acc0706d9) (0x4c1b680f64cd)) (S1.mk (0x2e9b6c99e203) (0x471b705804c5)))) (S3.mk (S2.mk (S1.mk (0x3e9b793f66dd) (0x5b1b804ec6df)) (S1.mk (0x479b8429e1a2) (0x181b8d3f66e2))) (S2.mk (S1.mk (0x859b900f6037) (0x6b0a3c070203)) (S1.mk (0x629b942782aa) (0x5b9b9855a1ed))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7b1b9c110143) (0x769ba00f606a)) (S1.mk (0x6f866c0d8203) (0x4b1ba40da2bd))) (S2.mk (S1.mk (0x949ba85801f3) (0x4c1bac0de9fb)) (S1.mk (0x6f9bb004e36c) (0x681bb40fe3a2)))) (S3.mk (S2.mk (S1.mk (0x8b9bb8110037) (0x5f99e874e085)) (S1.mk (0x6d1bbc0946d6) (0x741bc003812a))) (S2.mk (S1.mk (0x9a859825844d) (0x8c826c13c3ea)) (S1.mk (0x709bc427822a) (0x6e014c13c1ed)))))))))) (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x401bc80fa16b) (0x459bcc0fa1f6)) (S1.mk (0x631bd02d267f) (0x749bd814c6f5))) (S2.mk (S1.mk (0x6b1be13f66f7) (0x641be53f6368)) (S1.mk (0x888ce413c338) (0x7e19b4328228)))) (S3.mk (S2.mk (S1.mk (0x489be82001bb) (0x731bf02fe6fb)) (S1.mk (0x839bf40b416e) (0x501bf80f6169))) (S2.mk (S1.mk (0x400dfc958203) (0x4d9bfc5800fc)) (S1.mk (0x4795f93f6700) (0x801c08094701))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6c9c10e06060) (0x8b1c180c8705)) (S1.mk (0x381c1c2a616b) (0x779c2438e708))) (S2.mk (S1.mk (0x441c2ce149fb) (0x409c353f670c)) (S1.mk (0x771c38038170) (0x6e86ac0221bb)))) (S3.mk (S2.mk (S1.mk (0x951c3c0b464a) (0x649c453f6710)) (S1.mk (0x609c4d3f6712) (0x6890a899e116))) (S2.mk (S1.mk (0x569c5016e16e) (0x729c593f6715)) (S1.mk (0x849c5c292165) (0x89976013c020)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6899e874e050) (0x8e1c60094124)) (S1.mk (0x728818258083) (0x941c640b4282))) (S2.mk (S1.mk (0x6b1c6c11071a) (0x84027c0fe1be)) (S1.mk (0x671b9855a032) (0x60014c724032)))) (S3.mk (S2.mk (S1.mk (0x831c70022077) (0x9a1c7414c1f3)) (S1.mk (0x819c7807042d) (0x6c8d202d2116))) (S2.mk (S1.mk (0x951c7c74e380) (0x9a8f74258345)) (S1.mk (0x7d9c800b4249) (0x5108dc4149fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x481c893f6721) (0x4a93e13f6723)) (S1.mk (0x859c9013c380) (0x8c06a40124c7))) (S2.mk (S1.mk (0x6f1c9413c42d) (0x591c9d3f6726)) (S1.mk (0x7c089c0424e3) (0x7117dc23e087)))) (S3.mk (S2.mk (S1.mk (0x8613f05803ea) (0x6b9ca0110228)) (S1.mk (0x6d9ca813c729) (0x521cb13f672b))) (S2.mk (S1.mk (0x5e1cb93f672d) (0x519cbcd469fb)) (S1.mk (0x501cc53f6730) (0x489cc823e07a))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4e12d53f6733) (0x611cd53f6734)) (S1.mk (0x5e1cd83445f3) (0x5d1cdcbea13e))) (S2.mk (S1.mk (0x641ce423e738) (0x4a1ced3f673a)) (S1.mk (0x4d9cf04ce6d3) (0x611cf81b873d)))) (S3.mk (S2.mk (S1.mk (0x781cfc29e38d) (0x691c9413c601)) (S1.mk (0x711d0004e058) (0x6b0a3c5fe050))) (S2.mk (S1.mk (0x739d040422e0) (0x711d0863c228)) (S1.mk (0x781d0c580335) (0x5b1d101226d6))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7c1d1813c745) (0x719d1c18236c)) (S1.mk (0x599d200fe0c3) (0x611d2418c6d3))) (S2.mk (S1.mk (0x531d2803806d) (0x9703481b8394)) (S1.mk (0x4d9d2c2d217d) (0x4d050816e147)))) (S3.mk (S2.mk (S1.mk (0x7e9d302fe416) (0x939d3809474d)) (S1.mk (0x6c9d3c45e060) (0x6d9d40018058))) (S2.mk (S1.mk (0x7218105fe083) (0x8986e813c116)) (S1.mk (0x6b0a3c07016b) (0x631d44094325)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x7614841b8691) (0x4e1d4816e0a3)) (S1.mk (0x781d4c14c368) (0x471d54ea89fb))) (S2.mk (S1.mk (0x649d5d3f6756) (0x4f9d60e069fb)) (S1.mk (0x860e042fe380) (0x731d6438e42d)))) (S3.mk (S2.mk (S1.mk (0x92045c0b4345) (0x449d680b49fb)) (S1.mk (0x6a9d6c1b826d) (0x659d7016e22a))) (S2.mk (S1.mk (0x4e038013c16b) (0x7293b863c116)) (S1.mk (0x649d7413c077) (0x769d78122292))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4f1d7d3f6745) (0x931d8018c0bf)) (S1.mk (0x8e9b2c14c1be) (0x749d853f6288))) (S2.mk (S1.mk (0x830598258762) (0x7499b413c246)) (S1.mk (0x951b180222cd) (0x8b8f880fa1be)))) (S3.mk (S2.mk (S1.mk (0x949d8c1102e7) (0x599d9055a083)) (S1.mk (0x720e5d3f64be) (0x441d9499e083))) (S2.mk (S1.mk (0x571d980b416a) (0x6e18e40fe33d)) (S1.mk (0x3f9d9c16e1bb) (0x6a9da011022a)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x54838013c085) (0x571da414c192)) (S1.mk (0x511da80f6085) (0x401dac110203))) (S2.mk (S1.mk (0x571db53f676c) (0x529db808a085)) (S1.mk (0x429dac11018c) (0x4b1dbc0da192)))) (S3.mk (S2.mk (S1.mk (0x5a9dc004e2a8) (0x429dc454c050)) (S1.mk (0x471dc82d24c7) (0x8106c499e394))) (S2.mk (S1.mk (0x579dcc04e11d) (0x3d9dd023e050)) (S1.mk (0x5a061c13c13e) (0x5d8fe404e4c2))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x8499b413c228) (0x6e1dd42782e3)) (S1.mk (0x881dd80fe0bd) (0x569de13f6777))) (S2.mk (S1.mk (0x709de93f6779) (0x5c1dec23e508)) (S1.mk (0x7c19a013c124) (0x5f9df4ef89fb)))) (S3.mk (S2.mk (S1.mk (0x5a9dfd3f677e) (0x6e9e053f6780)) (S1.mk (0x7f147804e2cd) (0x899a400fe054))) (S2.mk (S1.mk (0x849e08110335) (0xc880480220a5)) (S1.mk (0xb007082580aa) (0x4d9a9063c050)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x561e0c328325) (0x4c15f01b818c)) (S1.mk (0x631e1013c6d9) (0x4a9e1458e9fb))) (S2.mk (S1.mk (0x521e193f644b) (0x499e1c0382aa)) (S1.mk (0x4b1d9055a1bb) (0x409e200da1f6)))) (S3.mk (S2.mk (S1.mk (0x599bb40fe5af) (0x410ffc11006d)) (S1.mk (0x481e2463c085) (0x401e286fa6d6))) (S2.mk (S1.mk (0x511e2c1f406d) (0x4f1cdc1b80f3)) (S1.mk (0x289e302009fb) (0x568ed013c78d))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x239e386fa9fb) (0x528af02fe18c)) (S1.mk (0x5b1e3c0382e3) (0x8108b01be44d))) (S2.mk (S1.mk (0x2d9e402a69fb) (0x671e48328791)) (S1.mk (0x379e50f269fb) (0x2f9e593f6795)))) (S3.mk (S2.mk (S1.mk (0x4b9e5c7aa9fb) (0x5e9e602d26fb)) (S1.mk (0x729e693f6799) (0x6a1e6c2d2701))) (S2.mk (S1.mk (0x571c10e0616a) (0x601e7016e705)) (S1.mk (0x491e793f679d) (0x559e7c6fa708))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x751e8063c64a) (0x689e8423e112)) (S1.mk (0x5c1e8863c246) (0x299e8c55a9fb))) (S2.mk (S1.mk (0x369e905809fb) (0x2e9e993f67a5)) (S1.mk (0x81144063c314) (0x689e9c74e050)))) (S3.mk (S2.mk (S1.mk (0x401ea13f6661) (0x9b0f88cc61be)) (S1.mk (0x759ea423e3ea) (0xa01ea80b402a))) (S2.mk (S1.mk (0x9c9eac0b409a) (0x769eb04fe292)) (S1.mk (0x9487400225f6) (0x791eb44ce0bf))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7d1eb818c323) (0x809ec13f67af)) (S1.mk (0x889ec413c087) (0x3d91653f6468))) (S2.mk (S1.mk (0x419ec88d29fb) (0x351ecd3f646c)) (S1.mk (0x3c9ed13f6147) (0x3c9ed42929fb)))) (S3.mk (S2.mk (S1.mk (0x3e1ed93f6498) (0x4f9edc3442e3)) (S1.mk (0x581ee53f67b8) (0x329eed3f67ba))) (S2.mk (S1.mk (0x4795953f64a0) (0x391ef01f4390)) (S1.mk (0x4f03d07240f3) (0x4e1ef4038085)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6c9efc1107be) (0x569f053f67c0)) (S1.mk (0x1e9f086ee9fb) (0x1e97ad3f6379))) (S2.mk (S1.mk (0xa41f0c0223c6) (0x781f10200395)) (S1.mk (0x541f153f656a) (0x8a1f18122282)))) (S3.mk (S2.mk (S1.mk (0x8f9f1c18c3c6) (0x569f202a615b)) (S1.mk (0x7f9f240223cf) (0x589f2d3f67ca))) (S2.mk (S1.mk (0x821f300c8112) (0x6b1f3455a16e)) (S1.mk (0x8d91540222bf) (0x851f38292292))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x791f400fe7cf) (0x7a9f4413c395)) (S1.mk (0x409f493f6657) (0x551f4c1100e4))) (S2.mk (S1.mk (0x731f5413c7d4) (0x679f5804e07a)) (S1.mk (0x7e1f5c0fa3e6) (0x7a9f600180d0)))) (S3.mk (S2.mk (S1.mk (0x7b0818070083) (0x4f894c13c16b)) (S1.mk (0x471f653f61a8) (0x579f683441ae))) (S2.mk (S1.mk (0x8886c43607db) (0x811f701b83a6)) (S1.mk (0x5d9f753f653c) (0x4c15953f6542))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x411f781f44c3) (0x739f7c16e131)) (S1.mk (0x979f800c8308) (0x479f88fc29fb))) (S2.mk (S1.mk (0x679f913f67e3) (0x641f953f6208)) (S1.mk (0x98882c414573) (0x481f993f6214)))) (S3.mk (S2.mk (S1.mk (0x549f9c344147) (0x869fa42927e8)) (S1.mk (0x469facfd49fb) (0x519fb53f67ec))) (S2.mk (S1.mk (0x4a1fb93f621b) (0x491fbc43a9fb)) (S1.mk (0x7b1fc013c508) (0x9d95e85fe3a6))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x769d0004e1f0) (0x730184334050)) (S1.mk (0x729fc45ac22a) (0x6f814c13c10e))) (S2.mk (S1.mk (0x591fc81b842d) (0x859fcc038037)) (S1.mk (0x7303000701bb) (0x9c8e5c13c0aa)))) (S3.mk (S2.mk (S1.mk (0x8e9fd00b4257) (0x959fd43280aa)) (S1.mk (0x679fd816e0da) (0x6003d80fe17d))) (S2.mk (S1.mk (0x7589640fe239) (0x9512c40223e6)) (S1.mk (0x8a8b3c2d2394) (0x7f91481be380)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x9417f0070579) (0x569fdc038192)) (S1.mk (0x5511383281bb) (0x541fe06c806d))) (S2.mk (S1.mk (0x8186e81be116) (0x6c0d202d2345)) (S1.mk (0x689fe4278192) (0x6684403281ed)))) (S3.mk (S2.mk (S1.mk (0x6e1fe863c282) (0x449fec018390)) (S1.mk (0x60014c72417a) (0x619ff00942a8))) (S2.mk (S1.mk (0x489ff454c060) (0x6b9ff80da131)) (S1.mk (0x688a380c81bb) (0x639ffd3f659a))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x62a0000f6468) (0x52a0048d2203)) (S1.mk (0x4fa00811046c) (0x5b200c0da147))) (S2.mk (S1.mk (0x7020100f61da) (0x54a0143b8203)) (S1.mk (0x6b201858033d) (0x5a05d53f6807)))) (S3.mk (S2.mk (S1.mk (0x67a02016e36c) (0x599bb40fe46c)) (S1.mk (0x572024110147) (0x4c2028292085))) (S2.mk (S1.mk (0x5a202c8d26d6) (0x5b20300382e3)) (S1.mk (0x7288b01be328) (0x7c203863c80d))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8aa03c14c054) (0x88989813c338)) (S1.mk (0x761c7c63c380) (0x751f24022791))) (S2.mk (S1.mk (0x7020402926fb) (0x5da0440182e3)) (S1.mk (0x8186e81be345) (0x8b20480c8705)))) (S3.mk (S2.mk (S1.mk (0x5620513f6813) (0x7120548d2708)) (S1.mk (0x5c10653f67cf) (0x5fa05832843a))) (S2.mk (S1.mk (0x9686c4360817) (0x73a060038131)) (S1.mk (0xb184cc0c85c3) (0x6820693f6819))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7fa06c14c2a2) (0x73a070328292)) (S1.mk (0x4f207423e176) (0x7c19a013c81e))) (S2.mk (S1.mk (0x58a07c42c9fb) (0x569dfd3f6820)) (S1.mk (0x73a08416e170) (0x5485c802216b)))) (S3.mk (S2.mk (S1.mk (0x60a08d3f6822) (0x8820902d22a0)) (S1.mk (0x5520953f6579) (0x66a0981b8762))) (S2.mk (S1.mk (0x5b209c13c231) (0x7319b40fe2cd)) (S1.mk (0x8a905c0706fb) (0x60014c1be083)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8e8560012708) (0x7301840121a2)) (S1.mk (0x65a0a01b822a) (0x81a0a40222f0))) (S2.mk (S1.mk (0x3e19ed3f682a) (0x41a0ad3f6729)) (S1.mk (0x6098893f65fb) (0x3920b13f6601)))) (S3.mk (S2.mk (S1.mk (0x6ba0b413c325) (0x6320b814c34f)) (S1.mk (0x5e20c13f682f) (0x43a0c93f6831))) (S2.mk (S1.mk (0x6520cc1f422a) (0x62814c13c0f3)) (S1.mk (0x5f20d13f650e) (0x5720d414c15b))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6520dd3f6836) (0x4d8c913f6838)) (S1.mk (0x4fa0e44fe13f) (0x6520ed3f683a))) (S2.mk (S1.mk (0x49a0f53f683c) (0x78a0f80fe335)) (S1.mk (0x7920fc292228) (0x67042809406d)))) (S3.mk (S2.mk (S1.mk (0x5293741b8060) (0x82a100038062)) (S1.mk (0x6884300c81bb) (0x5f21040fa1ce))) (S2.mk (S1.mk (0x5221081989fb) (0x6f97b53f6843)) (S1.mk (0x68a1101401da) (0x65892c3b8083)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x822114278147) (0x6d83002fe032)) (S1.mk (0x81a0a4022325) (0x67211832826d))) (S2.mk (S1.mk (0x71814c1be17a) (0x5394893f6847)) (S1.mk (0x5d83801be050) (0x44a12020018b)))) (S3.mk (S2.mk (S1.mk (0x49a12411015b) (0x4d212d3f684a)) (S1.mk (0x5121302925c8) (0x55a1353f65d0))) (S2.mk (S1.mk (0x3121393f64c7) (0x30213c3444cd)) (S1.mk (0x2821413f65c8) (0x56a1440fe18b))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x37a1493f64e8) (0x4c960834406d)) (S1.mk (0x6c215063c853) (0x442154fd49fb))) (S2.mk (S1.mk (0x38a15d3f6856) (0x3521613f64f2)) (S1.mk (0x3b96b49e89fb) (0x5a21653f64f5)))) (S3.mk (S2.mk (S1.mk (0x6f10a836085a) (0x85878c09447b)) (S1.mk (0x689374414060) (0x66216c0c843a))) (S2.mk (S1.mk (0x6b10b8414231) (0x5421706c806d)) (S1.mk (0x50a1741b8430) (0x67a17c29285e)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x83a1805fe745) (0x660e8c13c5af)) (S1.mk (0x61218463c745) (0x30a1893f678d))) (S2.mk (S1.mk (0x42a18d3f6791) (0x2e0c941f49fb)) (S1.mk (0x3783d13f60f3) (0x5d11493f6691)))) (S3.mk (S2.mk (S1.mk (0x40219014c16b) (0x6c8e8c13c1ce)) (S1.mk (0xa79a780b40aa) (0x9c9fd413c0aa))) (S2.mk (S1.mk (0x83a1800706d9) (0x8a85600126d6)) (S1.mk (0x798c70328157) (0x9b21947aa037))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x82030007010e) (0x7819b40fe228)) (S1.mk (0x51a19d3f6866) (0x3015dc55a16b))) (S2.mk (S1.mk (0x4621a01101bb) (0x4721a93f6869)) (S1.mk (0x45a1ac63c16a) (0x51a1b00fe1f6)))) (S3.mk (S2.mk (S1.mk (0x6421b44ec17b) (0x5116780fe1a2)) (S1.mk (0x3c21b8110390) (0x3796e0724085))) (S2.mk (S1.mk (0x3d21bc6fa192) (0x4da1c13f6508)) (S1.mk (0x5ca1c408a2e0) (0x670d000fe2f0))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x67a1c8110058) (0x6521cc5fe085)) (S1.mk (0x1d1ac13f6390) (0x8821d00fe02a))) (S2.mk (S1.mk (0x7da1d40c84c7) (0x55173499e032)) (S1.mk (0x8a8c58328105) (0x7ea1d80fe157)))) (S3.mk (S2.mk (S1.mk (0x60a1dc04e4e8) (0x81144063c50f)) (S1.mk (0x6721e004e4f2) (0x55894c9e8050))) (S2.mk (S1.mk (0x8b18ac13c59b) (0x6294a81b882a)) (S1.mk (0x9d95e8070869) (0x6991f404e6df))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7a1b1829e228) (0x8b15640c82cd)) (S1.mk (0x51a1e42fe16b) (0x5821e82fe325))) (S2.mk (S1.mk (0x5321ec03806d) (0x5d08181b817a)) (S1.mk (0x76a1f0110368) (0x9521f40b4822)))) (S3.mk (S2.mk (S1.mk (0x8a976013c2a2) (0x46a1f84fe16a)) (S1.mk (0x62a2000fe87f) (0x6fa2041b80d0))) (S2.mk (S1.mk (0x8c0598258328) (0x5716780fe06d)) (S1.mk (0x5122084ce192) (0x5b209c13c234)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x9a879c07059b) (0x50a2111069fb)) (S1.mk (0x5690d93f6885) (0x7a2218278147))) (S2.mk (S1.mk (0x68221c2fe1ed) (0x72a220042083)) (S1.mk (0x4aa22412216b) (0x582228110685)))) (S3.mk (S2.mk (S1.mk (0x87222c1b8037) (0x910ea074e88c)) (S1.mk (0x4a9a4c20e9fb) (0x55a1653f688d))) (S2.mk (S1.mk (0x648e6818206d) (0x5122381b80c3)) (S1.mk (0x5a0e7018c1bb) (0x59a2413f688f))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x7315640fa228) (0x85224413c3e3)) (S1.mk (0x68a2482d2328) (0x99a24c0226f5))) (S2.mk (S1.mk (0x9e95e80705fb) (0x9b0f74258116)) (S1.mk (0x672250022231) (0x50225414c18b)))) (S3.mk (S2.mk (S1.mk (0x6022593f6478) (0x7d225c14c395)) (S1.mk (0x7f9c90328380) (0x5122606fa10d))) (S2.mk (S1.mk (0x70a2693f6899) (0x561c9d3f689b)) (S1.mk (0x709a6813c4e3) (0x670cfc258050)))))))))))) (S11.mk (S10.mk (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x71227023e3c6) (0x6322793f689d)) (S1.mk (0x4da27c55a17d) (0x64a2801100ca))) (S2.mk (S1.mk (0x7fa28458082f) (0x55a28d3f68a2)) (S1.mk (0x5da2901103cf) (0x65a29414022a)))) (S3.mk (S2.mk (S1.mk (0x62a2980c8231) (0x67a29c1102bf)) (S1.mk (0x5c22a53f68a8) (0x6ca2a8292866))) (S2.mk (S1.mk (0x5da2b00fe8ab) (0x7122b4168058)) (S1.mk (0x8e22bc5fe8ae) (0x8319a013c3e6))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x8422c43608b0) (0x70a2c80fe10d)) (S1.mk (0x8511a841459b) (0x69a2cc27806d))) (S2.mk (S1.mk (0x56a2d01b81ed) (0x75a2d82928b5)) (S1.mk (0x7109881b8654) (0x7e22dc04e0d0)))) (S3.mk (S2.mk (S1.mk (0x6210d013c423) (0x7da2e0278058)) (S1.mk (0x7683005fe1ed) (0x8e22e40943e6))) (S2.mk (S1.mk (0x85195407026d) (0x480c082d21ce)) (S1.mk (0x60a2e816e058) (0x66a2f13f68bb)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5ba2f40da1da) (0x6ea2f813c176)) (S1.mk (0x6e0ea404e147) (0x5f22fc2fe050))) (S2.mk (S1.mk (0x7d230074e261) (0x64881825813e)) (S1.mk (0x77118c13c47b) (0x6899b42d22cd)))) (S3.mk (S2.mk (S1.mk (0x71a30413c2e0) (0x94230832850f)) (S1.mk (0x49230c0184cd) (0x53856c724083))) (S2.mk (S1.mk (0x3ca3102d216a) (0x7e19b43282cd)) (S1.mk (0x7523140b434f) (0x70231808a17b))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5596780fe18c) (0x50a31c110192)) (S1.mk (0x4a2320328085) (0x67a32413c192))) (S2.mk (S1.mk (0x5583640fe18c) (0x65a32804e34f)) (S1.mk (0x74232c33e09c) (0x5c094c13c4c2)))) (S3.mk (S2.mk (S1.mk (0x58233004e4c3) (0x5ca3341b86d9)) (S1.mk (0x77a3380f609c) (0x5d894c13c203))) (S2.mk (S1.mk (0x55a33c04e2aa) (0x48234055a050)) (S1.mk (0x869b18022246) (0x89101463c0aa))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x710ca8042423) (0x63234455a3aa)) (S1.mk (0x5ea34d3f68d2) (0x7f16380f6524))) (S2.mk (S1.mk (0x7b2350580525) (0x9923541101f3)) (S1.mk (0x7123581b8853) (0x50235c110222)))) (S3.mk (S2.mk (S1.mk (0x51a3600fa4c7) (0x5ca36404e325)) (S1.mk (0x60236808a2e3) (0x5783801be18c))) (S2.mk (S1.mk (0x5ea36c63c869) (0x52a37014c050)) (S1.mk (0x3723744fe9fb) (0x3ca3793f687f))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x2e237c63c9fb) (0x6723800fa246)) (S1.mk (0x3ea3841229fb) (0x5f23880ec06d))) (S2.mk (S1.mk (0x6d94841b88e3) (0x5599953f68e4)) (S1.mk (0x4523941829fb) (0x2ea3993f60c3)))) (S3.mk (S2.mk (S1.mk (0x3e239c18c9fb) (0x5314e845e9fb)) (S1.mk (0x5108dc1b806d) (0x6e95441b859b))) (S2.mk (S1.mk (0x5923a13f6555) (0x5ba3a93f68e9)) (S1.mk (0x4c90f81b806d) (0x75a3ac63c88c)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x9a852c1be394) (0x6e11481be44b)) (S1.mk (0x3923b099e13e) (0x3fa3b463c13e))) (S2.mk (S1.mk (0x4fa3b93f681e) (0xbc23c00228ef)) (S1.mk (0x5e85c53f60d0) (0x511e9c74e9fb)))) (S3.mk (S2.mk (S1.mk (0x3d94d53f62f0) (0x50a3c53f612a)) (S1.mk (0x558cfc2589fb) (0x4e23c93f66b2))) (S2.mk (S1.mk (0x5da3cc110246) (0x6723d00421f5)) (S1.mk (0x41a3d46fa325) (0x4923d814c5c8))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4e0a940fa18c) (0x64a3dc13c077)) (S1.mk (0x7023e014c323) (0x73a3e93f68f9))) (S2.mk (S1.mk (0x8e20fc0b4228) (0x9519984fe780)) (S1.mk (0x6da3ec292246) (0x6c23f0122112)))) (S3.mk (S2.mk (S1.mk (0x75a3f418c112) (0x5ea3fd3f68fe)) (S1.mk (0x68a400328249) (0x5824053f66f5))) (S2.mk (S1.mk (0x6c943413c17d) (0x9224082fe3a6)) (S1.mk (0x4f1d7d3f673d) (0x49240c4ec085)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x65241011038d) (0x80a41413c328)) (S1.mk (0x55241814c6d6) (0x5f04b920e9fb))) (S2.mk (S1.mk (0x5f24253f6908) (0x5da4280da222)) (S1.mk (0x92242c1102d4) (0x72a4353f690c)))) (S3.mk (S2.mk (S1.mk (0x5b18993f6402) (0x57a4393f6416)) (S1.mk (0x5aa43c1102f0) (0x8f2440022561))) (S2.mk (S1.mk (0x64a4440da12a) (0x649cb93f674d)) (S1.mk (0x5c244d3f6912) (0x6724501f4058))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6a24545fe0f3) (0x9488a41602cd)) (S1.mk (0x781f5413c261) (0x8b8f880fa02a))) (S2.mk (S1.mk (0x6f09642d2239) (0x5ba4580fa34f)) (S1.mk (0x5f9118b2a050) (0x8a245c0c834f)))) (S3.mk (S2.mk (S1.mk (0x5e24600945c8) (0x869b3833e037)) (S1.mk (0x6b0a3c0704c2) (0x6424642784c3))) (S2.mk (S1.mk (0x6824680fe3a2) (0x71a46c1100d0)) (S1.mk (0x5f9e9c74e085) (0x568ed03283b3)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6f247004e2f0) (0x781b080fe3cf)) (S1.mk (0x5c24746c8192) (0x6b2478328366))) (S2.mk (S1.mk (0x64247c63c323) (0x7aa48013c34c)) (S1.mk (0x6f18ac2d259b) (0x5e24843282f0)))) (S3.mk (S2.mk (S1.mk (0x71a48808a12a) (0x608cfc25818c)) (S1.mk (0x7e963474e869) (0x3e1ed13f66df))) (S2.mk (S1.mk (0x6da48c29e246) (0x87a49014c710)) (S1.mk (0x6e24942782e3) (0x9a052c1be926))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6b249c1b812a) (0x888a3025828b)) (S1.mk (0x7f24a0094246) (0x7ca4a53f62d4))) (S2.mk (S1.mk (0x5f24ad3f692a) (0x6d24b01b80d0)) (S1.mk (0x87163474e88c) (0x8e1a4013c054)))) (S3.mk (S2.mk (S1.mk (0x9224b414c2d4) (0xa724b80b40b2)) (S1.mk (0x60a4bc14c176) (0x7624c00f60d0))) (S2.mk (S1.mk (0x678cfc070203) (0x6da4c45800ca)) (S1.mk (0x6c99b42d2228) (0x6b24c93f6817))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8b07081b84be) (0x84894413c2cd)) (S1.mk (0x9a94645fe116) (0x5524d13f6933))) (S2.mk (S1.mk (0x4924d53f67d4) (0x86a4d80b4579)) (S1.mk (0x7324dc042077) (0x4e24e014c325)))) (S3.mk (S2.mk (S1.mk (0x54a4e93f6939) (0x76a4ec14c2cd)) (S1.mk (0x6ea4f00b4112) (0x789894022271))) (S2.mk (S1.mk (0x68a4f44ce112) (0x6e88b01be762)) (S1.mk (0x82a4f80222e3) (0x6524fc200112))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x529f153f6940) (0x6625042fe3b3)) (S1.mk (0x7125080943c2) (0x599d3c29e060))) (S2.mk (S1.mk (0x7ca50c38e3cf) (0x82a0a40220f5)) (S1.mk (0x7805981b8944) (0x60251416e323)))) (S3.mk (S2.mk (S1.mk (0x5925184fe0e4) (0x6ba51c328112)) (S1.mk (0x5da5200fe077) (0x6d1acc258431))) (S2.mk (S1.mk (0x6025293f6949) (0x44a52d3f66d9)) (S1.mk (0x3a9dac1101a2) (0x3e81ed3f6431)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x77a53463c94c) (0x4c25393f66fb)) (S1.mk (0x6b25413f694f) (0x67a5440802e3))) (S2.mk (S1.mk (0x64a5493f6701) (0x50a54d3f6705)) (S1.mk (0x3025553f6954) (0x4925593f6708)))) (S3.mk (S2.mk (S1.mk (0x5d1a64cc6050) (0x6e25612ae22a)) (S1.mk (0x64038013c0c3) (0x87948425844b))) (S2.mk (S1.mk (0x41a0ad3f6959) (0x4f1d7d3f695a)) (S1.mk (0x4d9d980b416b) (0x8d256c04e616))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x9c0b7c45e02a) (0x54861c0fe083)) (S1.mk (0x55014c1be1bb) (0x5fa57063c0f5))) (S2.mk (S1.mk (0x7318980fe338) (0x53a5743285c8)) (S1.mk (0x58257863c34f) (0x6304400fe17a)))) (S3.mk (S2.mk (S1.mk (0x7e19a03283e6) (0x88257c7aa0d0)) (S1.mk (0x82081807010e) (0x7c23ac63c3a6))) (S2.mk (S1.mk (0x76a58013c6fb) (0x730c7013c708)) (S1.mk (0x6da58416e0d0) (0x580cfc07016b))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x79a58807026d) (0x529d600fa050)) (S1.mk (0xa58348258817) (0x4f258d3f67be))) (S2.mk (S1.mk (0x67a59463c964) (0x84894413c228)) (S1.mk (0x65259829234f) (0x4d8be41ce9fb)))) (S3.mk (S2.mk (S1.mk (0x6da59c2d20ea) (0x6683b001216a)) (S1.mk (0x5da5a016e0e9) (0x81a5a40c80f5))) (S2.mk (S1.mk (0x85a5a80940d0) (0x718cfc070060)) (S1.mk (0x6a9734360083) (0x5da5ac328831))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x998bd413c02a) (0x7490040fe0e9)) (S1.mk (0x6aa5b06c822a) (0x66814c13c430))) (S2.mk (S1.mk (0x7825b414c5d0) (0x6b1be13f696e)) (S1.mk (0x70a5bc0b40e4) (0xa394000b4780)))) (S3.mk (S2.mk (S1.mk (0x6ca5c063c292) (0x7425c44ce395)) (S1.mk (0x6625c855a246) (0x75181c13c2bf))) (S2.mk (S1.mk (0x8525cc3282ac) (0x6125d414c974)) (S1.mk (0x56a4e93f6976) (0x6d1d18328745)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x89a5dc38e2cd) (0x6da5e0328723)) (S1.mk (0x819ec40fe087) (0x7c25e463c65b))) (S2.mk (S1.mk (0x9b04943343e6) (0x72a5e80fe395)) (S1.mk (0x8ba5ec5ac0d0) (0x7c24140fe328)))) (S3.mk (S2.mk (S1.mk (0x89a5f063c11b) (0x699a640c8050)) (S1.mk (0x7125f409422a) (0x6a038013c060))) (S2.mk (S1.mk (0x7c241413c561) (0x8ea45c0c83e6)) (S1.mk (0xa495e80703a6) (0x62a5f82d2124))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x8894f413c3c6) (0x7c950c04e3cf)) (S1.mk (0x6b8cfc070050) (0x62a5fc4ec044))) (S2.mk (S1.mk (0x6406340941a2) (0x4ba6001b81bb)) (S1.mk (0xa10708258981) (0x730ce40fe338)))) (S3.mk (S2.mk (S1.mk (0x5da60832834f) (0x69260c7aa06d)) (S1.mk (0x56a6101b810e) (0x81261463c02a))) (S2.mk (S1.mk (0x8218b413c579) (0x6b8c7013c6d6)) (S1.mk (0x8421d00fe1be) (0x6fa61813c4c7))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5ea61c2784cd) (0x73262099e817)) (S1.mk (0x89a62416e5c3) (0x8e262863c2a0))) (S2.mk (S1.mk (0x73262c08022a) (0x629c9432842d)) (S1.mk (0x6c26302fe6d9) (0x6ca5e013c26d)))) (S3.mk (S2.mk (S1.mk (0x6e99b40fe246) (0x6d965004e058)) (S1.mk (0x5f19e80b4050) (0x54014c1be13e))) (S2.mk (S1.mk (0x66a634018147) (0x78a6382fe44b)) (S1.mk (0x5e173436013e) (0x80963004e170))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6e05c8022050) (0x83a63c0fe081)) (S1.mk (0x5492000c816b) (0x5f17384149fb))) (S2.mk (S1.mk (0x3726406c89fb) (0x39a6453f6430)) (S1.mk (0x4e264829213e) (0x52024003c9fb)))) (S3.mk (S2.mk (S1.mk (0x7da65013c993) (0x3e26540da390)) (S1.mk (0x50a6580da2e3) (0xa9265c0223ea))) (S2.mk (S1.mk (0x6e266032844b) (0x65a66463c26d)) (S1.mk (0x6a26680b4431) (0x9da66c13c8ef)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8b90a8360345) (0x7922f813c1f9)) (S1.mk (0x7805981b844d) (0x5585cc0fe18c))) (S2.mk (S1.mk (0x5ea670168192) (0x7fa6743288ae)) (S1.mk (0x7926780b4869) (0x7b267c13c16e)))) (S3.mk (S2.mk (S1.mk (0x66a68004e42d) (0x942684328780)) (S1.mk (0x9c268813c0b2) (0x6da5e0328654))) (S2.mk (S1.mk (0x72268c13c6c8) (0x80269014c3e6)) (S1.mk (0x76a6941400d0) (0x8126982fe579))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x83a180070431) (0x79a69c0c86d6)) (S1.mk (0x52a6a063c82a) (0x7325e013c654))) (S2.mk (S1.mk (0x4891713f6593) (0x72a6a4b2a34f)) (S1.mk (0x6c26a85ac06d) (0x9b26ac63c59c)))) (S3.mk (S2.mk (S1.mk (0x780f741b8345) (0x86a6385fe44b)) (S1.mk (0x7c15640c8246) (0xa526b413c9ac))) (S2.mk (S1.mk (0x8d8e0407044b) (0x8826b813c292)) (S1.mk (0x6da6bc0b432d) (0x6ea6c0110371)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5826c93f69b1) (0x7926cc0ec12a)) (S1.mk (0x6ea6d00b426d) (0x78a6d53f68ef))) (S2.mk (S1.mk (0x6226dd3f69b6) (0x8e26e00b4380)) (S1.mk (0x8393b84fe345) (0x6d26e93f69b9)))) (S3.mk (S2.mk (S1.mk (0x73a6ec070729) (0x799c78070601)) (S1.mk (0x8126f074e745) (0x8f26f413c081))) (S2.mk (S1.mk (0x80052c1be7db) (0x7c26f81102a2)) (S1.mk (0x8fa6fc1be6f7) (0x919478012246))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x38a7013f66c8) (0x39a15d3f69c1)) (S1.mk (0x6098893f688c) (0x6414093f69c2))) (S2.mk (S1.mk (0x8d270c4142cd) (0x4a27106fa15b)) (S1.mk (0x6527140fe15b) (0x8b896413c282)))) (S3.mk (S2.mk (S1.mk (0x781f541be261) (0x5d271c1b89c6)) (S1.mk (0x77a7201be579) (0x839b1845e228))) (S2.mk (S1.mk (0x67a72414c13a) (0x7806e81be976)) (S1.mk (0x8f17f0258579) (0x7a27281b8228)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x78272c2d2054) (0x8794642fe116)) (S1.mk (0x9ca70c070228) (0x849564cc62cd))) (S2.mk (S1.mk (0x90a7300b4949) (0x89273413c119)) (S1.mk (0x9783482587db) (0x8e9400292780)))) (S3.mk (S2.mk (S1.mk (0x5aa73899e44b) (0x8527400b49cf)) (S1.mk (0x7b8bb13f69ac) (0x9526e074e380))) (S2.mk (S1.mk (0x8f274404e501) (0x9608a4160228)) (S1.mk (0x9c270c0702cd) (0x7c1f701b85fb))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6d0d000fe0f5) (0x65a7480fa22a)) (S1.mk (0x54038013c16a) (0x8d274c0fe94f))) (S2.mk (S1.mk (0x7ea7501b8981) (0x6614e845e050)) (S1.mk (0x6ca75416822a) (0x71814c13c366)))) (S3.mk (S2.mk (S1.mk (0x968e5c1be0aa) (0x8127584ec2dd)) (S1.mk (0x6211180221a2) (0x7208b072444d))) (S2.mk (S1.mk (0x958e5c1be4be) (0xa194780122cd)) (S1.mk (0x7d275c0940f5) (0x88081807017a))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x3e2760cc69fb) (0x4527652ae9fb)) (S1.mk (0x6da7680da170) (0x89a76c63c071))) (S2.mk (S1.mk (0x56277004e5c8) (0x73277404e246)) (S1.mk (0x5a27781b82e3) (0x6f118c1be47b)))) (S3.mk (S2.mk (S1.mk (0x81881825817a) (0x7e277c33434f)) (S1.mk (0x76278063c165) (0x7825e013c261))) (S2.mk (S1.mk (0x910ea00b43a6) (0x8ba5dc38e228)) (S1.mk (0x629ca81be729) (0x5fa784344058))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa0a7885fe981) (0xa9265c022054)) (S1.mk (0x75278c13c0e4) (0x959ca0022228))) (S2.mk (S1.mk (0x970598258944) (0x86a79013c13a)) (S1.mk (0x8a129c0227be) (0x9527943280b2)))) (S3.mk (S2.mk (S1.mk (0x49279d3f69e6) (0x50a7a13f6993)) (S1.mk (0x74900413c0ca) (0x9c9484070380))) (S2.mk (S1.mk (0x6527a463c112) (0x7827a863c0ee)) (S1.mk (0x6527ac0fe2e0) (0x8da7b00b42db)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x85914813c380) (0x6a27b414c33d)) (S1.mk (0xa983482589ee) (0x84a70c2fe2cd))) (S2.mk (S1.mk (0x9a88a43342cd) (0x8a1954070261)) (S1.mk (0x54a7bc344147) (0x53a7c02fe13e)))) (S3.mk (S2.mk (S1.mk (0x5f22fc4149fb) (0x6d1d1813c431)) (S1.mk (0x749c9013c44b) (0x74894413c246))) (S2.mk (S1.mk (0xa782ac070981) (0x8027c41103e6)) (S1.mk (0x8927c80800d0) (0x5ca7cc11033d))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6b1be13f69f4) (0x82a7d40b4323)) (S1.mk (0x92a7dc13c9f6) (0x67a7e01100f5))) (S2.mk (S1.mk (0x6fa7e40da0d0) (0x8218b43283a6)) (S1.mk (0x8322dc04e0ea) (0xa19478012228)))) (S3.mk (S2.mk (S1.mk (0x7627e8328323) (0x7b100413c0e9)) (S1.mk (0x7325e0328261) (n0))) (z2)))))))) (z9)) (z10))
def msTree : S12 := S12.mk (S11.mk (S10.mk (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xffffffffffffffff) (0xd9c958c9994858c9)) (S1.mk (0xaa2aa22aaa22a22a) (0xf7d7f5d77795f5d7))) (S2.mk (S1.mk (0x849184901481849) (0x2220022222020222)) (S1.mk (0x1596259713852597) (0xa82aa22aa822a22a)))) (S3.mk (S2.mk (S1.mk (0x5415511554115115) (0x22a822a0822822a)) (S1.mk (0xe7d7e5d76695e5d7) (0x849184101481801))) (S2.mk (S1.mk (0x2220022022000220) (0x1596259213842512)) (S1.mk (0xa828a0288820a028) (0x5404501444105014))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xd98158c1994058c1) (0x22a822808228228)) (S1.mk (0xe757e5d66691e5c6) (0xa82aa22aa822222a))) (S2.mk (S1.mk (0x5415511554111115) (0x51c958c9914848c9)) (S1.mk (0xa2c6a4c6628484c6) (0xa82aa22aa822a228)))) (S3.mk (S2.mk (S1.mk (0x5415511554115114) (0xd9c9588999485889)) (S1.mk (0xe7d7e5576695e557) (0x849104101481001))) (S2.mk (S1.mk (0x2220020022000200) (0x1586218213842102)) (S1.mk (0xa008a0288020a028) (0x5000501040105010)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xd80058c0984058c0) (0x22a802808228008)) (S1.mk (0xe515e4946491e484) (0x2022222220222222))) (S2.mk (S1.mk (0x1011111110111111) (0x40c848c8804848c8)) (S1.mk (0x80c484c4408484c4) (0x202020202020202)))) (S3.mk (S2.mk (S1.mk (0x586258703852587) (0x5411511154115110)) (S1.mk (0xd9c8188899481888) (0xa7d5655566956555))) (S2.mk (S1.mk (0xa828a22aa820222a) (0x5414511554101115)) (S1.mk (0x51c158c9914048c9) (0xa2c2a4c6628084c6))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x809184901081849) (0x1516259713052597)) (S1.mk (0x8888088888080888) (0x4545455544054555))) (S2.mk (S1.mk (0x5415511154111111) (0x51c958c8914848c8)) (S1.mk (0xa2c6a4c4628484c4) (0x49104901481049)))) (S3.mk (S2.mk (S1.mk (0x2a802a0822802a) (0xe6d7e4576695e457)) (S1.mk (0x2020220020202200) (0x1486208212842102))) (S2.mk (S1.mk (0x8000802080208020) (0x4000401040104010)) (S1.mk (0x9000104090001840) (0x6515649464116484))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2022202220222022) (0x1011101110111011)) (S1.mk (0x4048404800484048) (0x8084848400848484))) (S2.mk (S1.mk (0x848084800480848) (0x200020202000202)) (S1.mk (0x584058501840585) (0x2822022228228220)))) (S3.mk (S2.mk (S1.mk (0x1411011114114110) (0x49c8088889481888)) (S1.mk (0x222022202220222) (0x87d5055546952555))) (S2.mk (S1.mk (0xa828a02888202028) (0x5414501454101014)) (S1.mk (0x5141504111404041) (0xa282a0822280a082))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x808080808080808) (0x1514051511050515)) (S1.mk (0x4541054544050545) (0x4444444444044444))) (S2.mk (S1.mk (0x9981188199001881) (0x6757655666116546)) (S1.mk (0x5149584811484848) (0xa286a48422848484)))) (S3.mk (S2.mk (S1.mk (0x48104800481048) (0x1194219111852195)) (S1.mk (0x22802000228022) (0xe6d7e4566695e457))) (S2.mk (S1.mk (0xa028a22aa020222a) (0x50c158c9904048c9)) (S1.mk (0xa0c2a4c6608084c6) (0x516259703052597)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x888088808080888) (0x555455504154555)) (S1.mk (0x841184101401801) (0x1592259213802512))) (S2.mk (S1.mk (0x228822808208228) (0xe756e5d66690e5c6)) (S1.mk (0x1110011111010111) (0xe6c6e4466684e446)))) (S3.mk (S2.mk (S1.mk (0x5141584991404849) (0xa282a48662808486)) (S1.mk (0x808184801081848) (0x1514259513052595))) (S2.mk (S1.mk (0x202822208028222) (0x2028202820282028)) (S1.mk (0x1496249212842412) (0x282a222a28222228))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1415111514111114) (0xc9c9488989484889)) (S1.mk (0xc6d7c4574695c457) (0x8020802080200020))) (S2.mk (S1.mk (0x4010401040100010) (0x9000004090000840)) (S1.mk (0x2022200220222002) (0x1011100110111001)))) (S3.mk (S2.mk (S1.mk (0x4048400800484008) (0x8484840404848404)) (S1.mk (0x840084008400840) (0x200020202000002))) (S2.mk (S1.mk (0x580048101800481) (0x220022002200220)) (S1.mk (0x87d4055446942554) (0x2828202808202028)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x1414141414141414) (0x4141404101404041)) (S1.mk (0x8282808202808082) (0x8880888088808880))) (S2.mk (S1.mk (0x4541054144010141) (0x808080008080800)) (S1.mk (0x1514051011040514) (0x9881188198001881)))) (S3.mk (S2.mk (S1.mk (0x202020002020200) (0x6543254264012542)) (S1.mk (0xa82aa22088222220) (0x5415511044111110))) (S2.mk (S1.mk (0x5149584011484840) (0xa286a48022848480)) (S1.mk (0x48100000481008) (0x1194211111852115))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x5414500444105004) (0x22800000228002)) (S1.mk (0xe6d3e4466695e447) (0x2028222a2020222a))) (S2.mk (S1.mk (0x1010111110101111) (0xe0c0ecc8e0c0ecc8)) (S1.mk (0x80c084c4408084c4) (0x406248602042486)))) (S3.mk (S2.mk (S1.mk (0x1110011011000110) (0xe642a4c26680a4c2)) (S1.mk (0x9989188999081889) (0x6646644666046446))) (S2.mk (S1.mk (0x41104101401041) (0x182218303812183)) (S1.mk (0x28802808208028) (0xa6d4645466946454)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2220022022000020) (0x1514259413042494)) (S1.mk (0x4541455144014151) (0x848084000480800))) (S2.mk (S1.mk (0x1494049010840410) (0xd90158c1994058c1)) (S1.mk (0x222022000220200) (0xe313a1d26291a1c2)))) (S3.mk (S2.mk (S1.mk (0x2822200a08222008) (0x1411100504111004)) (S1.mk (0xc9c8488989484889) (0xc6d5c4574695c457))) (S2.mk (S1.mk (0xa028a02aa020202a) (0x5414501554101015)) (S1.mk (0x809084901080849) (0x516059703050597))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x22a022a0822022a) (0x545055504050555)) (S1.mk (0xd9c1588199405881) (0xe756e5566690e546))) (S2.mk (S1.mk (0x2220022022020220) (0x1110011011010110)) (S1.mk (0xd9c9588999485881) (0x200020002000200)))) (S3.mk (S2.mk (S1.mk (0x586218203842102) (0x5800584018405840)) (S1.mk (0xa515e4942491e484) (0xa022a222a022a220))) (S2.mk (S1.mk (0x5011511150115110) (0x58c8188898481888)) (S1.mk (0xa5d5655564956555) (0x5101504111405041))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4455445544154455) (0x220022202000022)) (S1.mk (0x516259703042497) (0x2880288828800888))) (S2.mk (S1.mk (0x840184000401800) (0x1590259011802510)) (S1.mk (0x220822000208200) (0xe752e5d26690e5c2)))) (S3.mk (S2.mk (S1.mk (0x5405510544015104) (0x1010101010101010)) (S1.mk (0xc80048c0884048c0) (0xc515c4944491c484))) (S2.mk (S1.mk (0xa828a228a8202228) (0x5414511054101110)) (S1.mk (0x51c158c0914048c0) (0xa2c2a4c0628084c0))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x9100901081009) (0x1116211713052117)) (S1.mk (0xc6c7c4474685c447) (0x2020200200202002))) (S2.mk (S1.mk (0x1010100100101001) (0x4040400800404008)) (S1.mk (0x8080800400808004) (0xc000cc000000cc0)))) (S3.mk (S2.mk (S1.mk (0x500048101000481) (0x414041404140414)) (S1.mk (0x141004101400041) (0x282008202800082))) (S2.mk (S1.mk (0x2000200020002) (0x4441444144414441)) (S1.mk (0x504050001040500) (0x2008a0280020a028)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x444444404044444) (0x801180108001801)) (S1.mk (0x503250204012502) (0xa0a0a000a0a0a000))) (S2.mk (S1.mk (0x5050500050505000) (0xd8c8588898485888)) (S1.mk (0xe4d1e4446495e445) (0x2028222820202228)))) (S3.mk (S2.mk (S1.mk (0x1010111010101110) (0xccc0ccc0ccc0ccc0)) (S1.mk (0x809180901081809) (0x406240602042406))) (S2.mk (S1.mk (0x545454504054545) (0x101010101010101)) (S1.mk (0x1901180919081809) (0x2602240622042406))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1100010011000100) (0xe400a4c06480a4c0)) (S1.mk (0x182018303810183) (0x8880880088008000))) (S2.mk (S1.mk (0x4440440044004000) (0x1908180819081808)) (S1.mk (0x2614241426142414) (0x5410511154101111)))) (S3.mk (S2.mk (S1.mk (0x5140584891404848) (0xa280a48462808484)) (S1.mk (0x2220220022002000) (0x1504258413042484))) (S2.mk (S1.mk (0x8800880088000000) (0x4501451144014111)) (S1.mk (0x48004000480000) (0x1084009010840010))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x22002000220000) (0xe213a0d26291a0c2)) (S1.mk (0xc808c8804808c8) (0xc404c4408404c4))) (S2.mk (S1.mk (0x411000504110004) (0x89c8088989480889)) (S1.mk (0x46d5445746954457) (0xa028a028a0202028)))) (S3.mk (S2.mk (S1.mk (0x5041504110404041) (0xa082a0822080a082)) (S1.mk (0x515051505150515) (0x545054504050545))) (S2.mk (S1.mk (0x4554455444104544) (0x5000504010405040)) (S1.mk (0xa880a888a880a888) (0x1192219313812193))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4454445444144454) (0x486248202842402)) (S1.mk (0x1101100111001001) (0x2717651626116506))) (S2.mk (S1.mk (0x2022222220222220) (0x1011111110111110)) (S1.mk (0xc8c8488888484888) (0xc4d5c4544495c455)))) (S3.mk (S2.mk (S1.mk (0x1000501000105010) (0xc88058c0884058c0)) (S1.mk (0xc550e5d04490e5c0) (0x5949580919485809))) (S2.mk (S1.mk (0xa606a4062204a406) (0x808000008080000)) (S1.mk (0x1504010011040100) (0x202000000020000)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xc501848044818480) (0x586258703842587)) (S1.mk (0xa820800088208000) (0x5410400044104000))) (S2.mk (S1.mk (0x5940180819401808) (0xa795651526956515)) (S1.mk (0x828022008200220) (0x414011004100110)))) (S3.mk (S2.mk (S1.mk (0x1c108c0014008c0) (0x2c204c0028004c0)) (S1.mk (0x9100900081009) (0x1116211711052117))) (S2.mk (S1.mk (0xa800a0002800a) (0x2028202a2020202a)) (S1.mk (0x1414101514101015) (0x40c148c9804048c9))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x80c284c6408084c6) (0x801180101001801)) (S1.mk (0x1512251213002512) (0xe746e5466680e546))) (S2.mk (S1.mk (0xa828a228a820a228) (0x5414511454105114)) (S1.mk (0xd981588199085881) (0xe642a4426604a442)))) (S3.mk (S2.mk (S1.mk (0xa4d5645564956455) (0x5400501044105010)) (S1.mk (0x5100504011405040) (0xa200a0802280a080))) (S2.mk (S1.mk (0x2220020222020202) (0x1196218713852187)) (S1.mk (0x8080800080808000) (0x4040400040404000))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x9000100090001800) (0x6515641464116404)) (S1.mk (0x584058401840584) (0x49c8088889481880))) (S2.mk (S1.mk (0xa82aa02288222022) (0x5415501144111011)) (S1.mk (0x5149504811484048) (0x48004800480048)))) (S3.mk (S2.mk (S1.mk (0x1194019111850195) (0x22002000220022)) (S1.mk (0x486248602842486) (0xc6c6c4464684c446))) (S2.mk (S1.mk (0x1004500400105004) (0xc881588188405881)) (S1.mk (0xc556e5564490e546) (0x222022002220220))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x111011001010110) (0x848004000480000)) (S1.mk (0x584018001840100) (0x222002000220000))) (S2.mk (S1.mk (0xa511a4902491a480) (0xa022800280228000)) (S1.mk (0x5011400140114000) (0x5848180818481808)))) (S3.mk (S2.mk (S1.mk (0xa595651524956515) (0x11c918c8914808c8)) (S1.mk (0x22c624c4628404c4) (0x4440444044404440))) (S2.mk (S1.mk (0x504050501040505) (0x87c5054546852545)) (S1.mk (0x5010511150101111) (0x5040584890404848)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xa080a48460808484) (0x504258503052585)) (S1.mk (0x41104101401001) (0x1092209212802012))) (S2.mk (S1.mk (0xe256e0d66690e0c6) (0x8989088989080889)) (S1.mk (0x4647444746054447) (0x41004100410041)))) (S3.mk (S2.mk (S1.mk (0x82008200800082) (0x28002800280020)) (S1.mk (0x880088008800880) (0x800088008000880))) (S2.mk (S1.mk (0x500050005000500) (0x502250204002502)) (S1.mk (0xc8c0488088404880) (0xc4c0844044808440))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x809180101081801) (0x406240202042406)) (S1.mk (0x505450404054504) (0x404040404040404))) (S2.mk (S1.mk (0x909080909080809) (0x606040606040406)) (S1.mk (0x9800188098001880) (0x6400240064002400)))) (S3.mk (S2.mk (S1.mk (0x2022202220222020) (0x1011101110111010)) (S1.mk (0x8888088888080880) (0x41004101400001))) (S2.mk (S1.mk (0x182018203800102) (0x1900180019001800)) (S1.mk (0x2614241426142404) (0x22002200220022)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x11001100110011) (0x484048400840484)) (S1.mk (0x1194019511850195) (0x5010501050101010))) (S2.mk (S1.mk (0x5040504010404040) (0x505050505050505)) (S1.mk (0x1192219213802112) (0x4454445444104444)))) (S3.mk (S2.mk (S1.mk (0x9989188999081881) (0x2202200222002002)) (S1.mk (0x1192219213802192) (0x1410144010001440))) (S2.mk (S1.mk (0x2800288828002888) (0x511051504110515)) (S1.mk (0x2307610626016106) (0x2020200020202))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1010100010101) (0x8080800080808)) (S1.mk (0x40104000401040) (0x1190219011802190))) (S2.mk (S1.mk (0x20802000208020) (0xc4d0c4504490c450)) (S1.mk (0x5041584910404849) (0xa082a48620808486)))) (S3.mk (S2.mk (S1.mk (0x808184800081848) (0x514259501042495)) (S1.mk (0x222822200228222) (0x541455504014155))) (S2.mk (S1.mk (0x10401000104010) (0x888018c0880018c0)) (S1.mk (0x455065d0441065c0) (0x20200000202)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x10100000101) (0x5109580911085809)) (S1.mk (0x2020200820202008) (0x1404000010040000))) (S2.mk (S1.mk (0xc000404080004040) (0xc101808040018080)) (S1.mk (0x2820000008200000) (0x1410000004100000)))) (S3.mk (S2.mk (S1.mk (0x4940080801400808) (0x8795451506914515)) (S1.mk (0x1514051111050515) (0x4545454444054544))) (S2.mk (S1.mk (0x1c1088001400880) (0x2c2044002800440)) (S1.mk (0x9100100081001) (0x1116211311052113))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa800800028008) (0xc6c7c4464685c446)) (S1.mk (0x1010101110101011) (0x406048602040486))) (S2.mk (S1.mk (0xe6c2a4426680a442) (0x9981188199081881)) (S1.mk (0x6642244266042442) (0xa4c4244464842444)))) (S3.mk (S2.mk (S1.mk (0x111011101110111) (0xa317e1962691e186)) (S1.mk (0xc4c4c4444484c444) (0x8800088088000880))) (S2.mk (S1.mk (0x4515441444114404) (0x82208202802082)) (S1.mk (0x59c8188899481880) (0x5414501044101010))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x5141504011404040) (0xa282a08022808080)) (S1.mk (0xc6c5c4474685c447) (0x4048404800484040))) (S2.mk (S1.mk (0x8084808400848080) (0x848084800480808)) (S1.mk (0x584058501850505) (0x222022200220202)))) (S3.mk (S2.mk (S1.mk (0xa595251524952505) (0x1196219613842196)) (S1.mk (0x1000010010000100) (0x6000208060002480))) (S2.mk (S1.mk (0x880000008808080) (0x440000004404040)) (S1.mk (0x900080809001808) (0x701050506012505))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6557655664116546) (0x22020200220222)) (S1.mk (0x11010100110111) (0x48080800480848))) (S2.mk (S1.mk (0x84040400840484) (0x194219001842194)) (S1.mk (0xa020a200a0202200) (0x5010510050101100)))) (S3.mk (S2.mk (S1.mk (0x5040580090404800) (0xa080a40060808400)) (S1.mk (0x808180001081800) (0x504250003052500))) (S2.mk (S1.mk (0x202820008028200) (0x501450004054500)) (S1.mk (0x1092009212800012) (0x282a202a28222028)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x415001514010014) (0x40c148c1804048c1)) (S1.mk (0x80c284c2408084c2) (0x516051703050517))) (S2.mk (S1.mk (0x182218203802102) (0xa414e4942490e484)) (S1.mk (0x9888188898081888) (0x2455645564156455)))) (S3.mk (S2.mk (S1.mk (0xa022a222a0222222) (0x5011511150111111)) (S1.mk (0x50c858c8904848c8) (0xa0c4a4c4608484c4))) (S2.mk (S1.mk (0x1186218713852187) (0x8800080888080808)) (S1.mk (0xc6d7845646958457) (0x4048484800484848))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x848184800481848) (0x484248400842484)) (S1.mk (0x111411100114111) (0x918110c1914010c1))) (S2.mk (S1.mk (0x635761d6669161c6) (0x1000100010001)) (S1.mk (0x440044004400440) (0x180008101800081)))) (S3.mk (S2.mk (S1.mk (0x86d4045446942454) (0x9880188098001880)) (S1.mk (0x6541254064012540) (0x1194210111852105))) (S2.mk (S1.mk (0x2828222a2820222a) (0x1414111514101115)) (S1.mk (0x4141484981404849) (0x8282848642808486)))))))))) (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x1414249412042494) (0x1414041010040414)) (S1.mk (0xe303a1c26281a1c2) (0x2820280808202008))) (S2.mk (S1.mk (0x1410100404101004) (0x4555455444114544)) (S1.mk (0x4445444544054445) (0xc800c8804800c0)))) (S3.mk (S2.mk (S1.mk (0x49004901480009) (0x186018703850107)) (S1.mk (0x2a002a0822002a) (0xa4d5245564952445))) (S2.mk (S1.mk (0xa820a0008820a000) (0x5410500044105000)) (S1.mk (0x5100500011405000) (0xa200a0002280a000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1404000010040100) (0x6101200060012400)) (S1.mk (0x2820000008208000) (0x1410000004104000))) (S2.mk (S1.mk (0x4940080009401800) (0x8791051106912511)) (S1.mk (0x82a002208220022) (0x415000104110011)))) (S3.mk (S2.mk (S1.mk (0x149000801480048) (0x286000402840084)) (S1.mk (0x1194019011840194) (0x808184001081840))) (S2.mk (S1.mk (0x1514259113052591) (0x202822008028220)) (S1.mk (0x4541455444054554) (0x6442244264002442)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x6653644666156447) (0x5041504910404049)) (S1.mk (0x808084800080848) (0x514059501040495))) (S2.mk (S1.mk (0x541055504010155) (0x6752655266106542)) (S1.mk (0x486208202842002) (0x8515c4940491c484)))) (S3.mk (S2.mk (S1.mk (0xc8c8088888480888) (0x85d5455544954555)) (S1.mk (0x1100101001001) (0x1112211313012113))) (S2.mk (S1.mk (0x4646444646044446) (0x909080101080801)) (S1.mk (0x606040202040406) (0x22a022808220228))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x505050405050504) (0x1010100010101000)) (S1.mk (0x101010001010100) (0x100010001000100))) (S2.mk (S1.mk (0x1800180018001800) (0x2400240024002400)) (S1.mk (0x2414241424142404) (0x405040504050405)))) (S3.mk (S2.mk (S1.mk (0x1182218213802102) (0x9988188899081880)) (S1.mk (0x6644244466042444) (0x1112211213002112))) (S2.mk (S1.mk (0x180018101800181) (0x410041404100414)) (S1.mk (0x1414101014141010) (0x4141404001404040))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8282808002808080) (0x1110010111010101)) (S1.mk (0x809100101081001) (0x406200202042002))) (S2.mk (S1.mk (0x2105600424016004) (0x180218001802180)) (S1.mk (0xc8c0088088400880) (0xc4d0445044904450)))) (S3.mk (S2.mk (S1.mk (0x1414140414141404) (0x4141400101404001)) (S1.mk (0x8282800202808002) (0x4541454044014540))) (S2.mk (S1.mk (0xe343a1c26281a1c2) (0x6440644864406448)) (S1.mk (0x8080808400808084) (0x404048400040484))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6642244266002442) (0x84c4444444844444)) (S1.mk (0x1192218313812183) (0x454445404144454))) (S2.mk (S1.mk (0xa115e1942491e184) (0x480048004800480)) (S1.mk (0x110011001100110) (0x59c1588119405881)))) (S3.mk (S2.mk (S1.mk (0xa6c2a4422680a442) (0x2654645466146454)) (S1.mk (0x4404440444040404) (0x1101100111000001))) (S2.mk (S1.mk (0x1110011011000010) (0x484048000840400)) (S1.mk (0xa111a1902091a180) (0x2022200200222000)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x1011100100111000) (0x4848480808484808)) (S1.mk (0x8485840504858405) (0x220022002000020))) (S2.mk (S1.mk (0x516059603040496) (0x840084000400800)) (S1.mk (0x1590059011800510) (0x220022000200200)))) (S3.mk (S2.mk (S1.mk (0xc552a5524490a542) (0xa82aa00a8822a008)) (S1.mk (0x5415500544115004) (0x5989588911085881))) (S2.mk (S1.mk (0xa646a4462204a442) (0x4048400800484000)) (S1.mk (0x8084800400848000) (0x580058101810501))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa594251424942504) (0x1001100110000001)) (S1.mk (0x1196219613842096) (0x10001000100010))) (S2.mk (S1.mk (0x8000004080000840) (0x4000008040000480)) (S1.mk (0x200000002) (0x404040500040405)))) (S3.mk (S2.mk (S1.mk (0x100000801001008) (0x20020000200220)) (S1.mk (0x10010000100110) (0x40080000400840))) (S2.mk (S1.mk (0x80040000800480) (0x8100000081008)) (S1.mk (0x114211001042114) (0x2800000028002)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xe6c7e4466685e447) (0xe602a4c26680a4c2)) (S1.mk (0x9988188899081888) (0x8100001081000))) (S2.mk (S1.mk (0x104210003052100) (0x2800008028000)) (S1.mk (0x401440004054400) (0x1082008212800002)))) (S3.mk (S2.mk (S1.mk (0xd101504191405041) (0xe216a0966690a086)) (S1.mk (0x411001114010010) (0x8988088889080888))) (S2.mk (S1.mk (0x4645444546054445) (0x8082808200808082)) (S1.mk (0x4544454444004544) (0x455445504154455))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1182218313812183) (0x4455445444154455)) (S1.mk (0x5141500111405001) (0xa282a0022280a002))) (S2.mk (S1.mk (0x100010101000101) (0x86c4044446842444)) (S1.mk (0x515451404114504) (0x1194218111852185)))) (S3.mk (S2.mk (S1.mk (0x4040484880404848) (0x8080848440808484)) (S1.mk (0x404248402042484) (0x101411104014111))) (S2.mk (S1.mk (0x4141010140010101) (0x1514011011040110)) (S1.mk (0x6743244266012442) (0x5414400444104004)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xd9c1188199401881) (0xe6d3245266912453)) (S1.mk (0xd08050c0904050c0) (0xe155e1d46491e1c4))) (S2.mk (S1.mk (0x1000104010000040) (0x510051404100514)) (S1.mk (0x2020000020200) (0x1010000010100)))) (S3.mk (S2.mk (S1.mk (0x8080000080800) (0x4040000040400)) (S1.mk (0x40100000401000) (0x190211001802110))) (S2.mk (S1.mk (0x1981188119001881) (0x20800000208000)) (S1.mk (0x2652644226106442) (0x4414500444101004))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1141500111404001) (0x2282a00222808002)) (S1.mk (0x1114051011040410) (0x4441454044014140))) (S2.mk (S1.mk (0xd000508090405080) (0xe111a1506091a140)) (S1.mk (0x8020802280200022) (0x4010401140100011)))) (S3.mk (S2.mk (S1.mk (0x1040104810400048) (0x2080208420800084)) (S1.mk (0x8004800080048) (0x504058501040485))) (S2.mk (S1.mk (0x411041504110415) (0x40104000401000)) (S1.mk (0x1180218011802100) (0x9900188099001880))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x20802000208000) (0x6610641066106400)) (S1.mk (0x8802820288028200) (0x4401410144014100))) (S2.mk (S1.mk (0x9908180899081800) (0x6604240466042400)) (S1.mk (0x8105c0840481c084) (0x2828222828202228)))) (S3.mk (S2.mk (S1.mk (0x1414111014101110) (0x418148c0814048c0)) (S1.mk (0x824284c0428084c0) (0x506050703050507))) (S2.mk (S1.mk (0x2115601424116004) (0x48c8088888480880)) (S1.mk (0x1190019111810191) (0xc6d6845646948456))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa828a02a8820202a) (0x5141504911404049)) (S1.mk (0xa282a08622808086) (0x1514059511050595))) (S2.mk (S1.mk (0x918110c1910010c1) (0x635761d6661161c6)) (S1.mk (0x2220022222000222) (0x1110011111000111)))) (S3.mk (S2.mk (S1.mk (0x1514051411040414) (0x1594059011840510)) (S1.mk (0x4551055044110540) (0x5149500911485001))) (S2.mk (S1.mk (0xa286a0062284a002) (0x849184101481841)) (S1.mk (0x586258303852587) (0xa7d5655466956554)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x101000101000001) (0x202000202000002)) (S1.mk (0x404040004040404) (0x1100100001001))) (S2.mk (S1.mk (0x103210200012102) (0xc4d1c4444495c445)) (S1.mk (0x180018101810181) (0x990118c1994018c1)))) (S3.mk (S2.mk (S1.mk (0x621320d2629120c2) (0xa028a228a0202228)) (S1.mk (0x5414511454101114) (0x50c158c1904048c1))) (S2.mk (S1.mk (0xe0c2a4c26080a4c2) (0x516251703042417)) (S1.mk (0xc550c5d04490c5c0) (0xc40084c0448084c0))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1900180819001808) (0x2715651526156515)) (S1.mk (0x20022000200220) (0x10011000100110))) (S2.mk (S1.mk (0xc00cc000c00cc0) (0xa6c4644466846444)) (S1.mk (0x1514050111050505) (0x1416201212042012)))) (S3.mk (S2.mk (S1.mk (0x6347604666016046) (0x1414111414101114)) (S1.mk (0xc9c1088989480889) (0xc6d3045646950457))) (S2.mk (S1.mk (0x22022200220222) (0x11011100110111)) (S1.mk (0x48084800480848) (0x22802200228022))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x11401100114011) (0x900000809001008)) (S1.mk (0x610041406102414) (0x22020000220220))) (S2.mk (S1.mk (0x11010000110110) (0x48080000480840)) (S1.mk (0x84040000840480) (0x184210001842104)))) (S3.mk (S2.mk (S1.mk (0x5941580119405801) (0xa693e4022691e403)) (S1.mk (0x1414110414101104) (0x141480181404801))) (S2.mk (S1.mk (0x282840242808402) (0x8180001081800)) (S1.mk (0x1014241012042410) (0x2820008028200))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xe101a1c06081a1c0) (0x1580258011802500)) (S1.mk (0xa802a2028802a200) (0x5401510144015100))) (S2.mk (S1.mk (0xd9c8588899485888) (0xe6c4a4446684a444)) (S1.mk (0x46d4445646944456) (0x416049602040496)))) (S3.mk (S2.mk (S1.mk (0x1510051011000510) (0xc542a5424480a542)) (S1.mk (0x5981588111085881) (0xa642a4422204a442))) (S2.mk (S1.mk (0xa494641424946414) (0x8000080080000800)) (S1.mk (0x2000000020002) (0x82208202802002)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xa216e0962690e086) (0x1102210213002102)) (S1.mk (0x5410511054105110) (0x9980188099001880))) (S2.mk (S1.mk (0x6640244066002440) (0x1110110011001000)) (S1.mk (0x180018001800180) (0x410041004100410)))) (S3.mk (S2.mk (S1.mk (0x8981088189000881) (0x4642044246000442)) (S1.mk (0x2515649424116484) (0x1190218111812181))) (S2.mk (S1.mk (0x2103210220012102) (0x48c0488008404880)) (S1.mk (0x84c0844004808440) (0xc040484080404840))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xc080848040808480) (0x808180801081808)) (S1.mk (0x404240402042404) (0x202820208028202))) (S2.mk (S1.mk (0x501450104014101) (0x1101104111401041)) (S1.mk (0x2282208222802082) (0x1082208212802102)))) (S3.mk (S2.mk (S1.mk (0x188088881081880) (0x654445446146454)) (S1.mk (0x2111211020112100) (0x504050101050505))) (S2.mk (S1.mk (0x8485840404858405) (0x88c008c0884008c0)) (S1.mk (0x44c004c0448004c0) (0x445444504054445))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2604240426042404) (0x141014100010141)) (S1.mk (0x4540054044000540) (0x4445044444050445))) (S2.mk (S1.mk (0x2317619626916186) (0xc8c8488888484880)) (S1.mk (0x501050004010500) (0x186218603852186)))) (S3.mk (S2.mk (S1.mk (0xc4d4c4544494c454) (0x4440444444004444)) (S1.mk (0x1104101001041) (0x2208202002082))) (S2.mk (S1.mk (0x4000504000405040) (0x8000a0800080a080)) (S1.mk (0x4501040044010400) (0x5140100011401000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa391211122912111) (0x828002008200020)) (S1.mk (0x414001004140010) (0x141004001400040))) (S2.mk (S1.mk (0x282008002800080) (0x1114011411040114)) (S1.mk (0x4643044346010443) (0x2080a00020a0a000)))) (S3.mk (S2.mk (S1.mk (0x1000500000105000) (0xc880588088405880)) (S1.mk (0xc544e5444480e544) (0x504010001040100))) (S2.mk (S1.mk (0xa501a4802481a480) (0xa020800080208000)) (S1.mk (0x5010400040104000) (0xa495241524952405)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x82a022228220222) (0x415011114110111)) (S1.mk (0x1c908c8814808c8) (0x2c604c4428404c4))) (S2.mk (S1.mk (0x2220020022020200) (0x1196218613852186)) (S1.mk (0x8880088088080880) (0x4041400140414001)))) (S3.mk (S2.mk (S1.mk (0x1901180119001801) (0x2703240226012402)) (S1.mk (0xd8c0188098401880) (0xe4d1245064912451))) (S2.mk (S1.mk (0x1004101000041) (0x2008202000082)) (S1.mk (0xc155e1d44491e1c4) (0x500040101000401))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x500010404000104) (0x8881088188000881)) (S1.mk (0x4442044244000442) (0x90201000802010))) (S2.mk (S1.mk (0x8020a00080202000) (0x4010500040101000)) (S1.mk (0x1040500010404000) (0x200020002000000)))) (S3.mk (S2.mk (S1.mk (0x104050001040400) (0x800080008000000)) (S1.mk (0x401050004010100) (0x40004000400000))) (S2.mk (S1.mk (0x1080009010800010) (0x20002000200000)) (S1.mk (0xe010a0506090a040) (0x401040504010004)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8988088989080889) (0x4655445746154457)) (S1.mk (0x1190219111812191) (0x1080208010802000))) (S2.mk (S1.mk (0x9100100091001000) (0x6210601062106000)) (S1.mk (0x802020208020200) (0x401010104010100)))) (S3.mk (S2.mk (S1.mk (0x8908080889080800) (0x4604040446040400)) (S1.mk (0x400044004000440) (0x105408404014084))) (S2.mk (S1.mk (0x486248702842487) (0x40c0088880400888)) (S1.mk (0x4101484001404840) (0x8202848002808480))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x10100000101000) (0x1110211111012111)) (S1.mk (0x80800000808000) (0x2444244464042444))) (S2.mk (S1.mk (0xc9c9488989484881) (0x1101104111001041)) (S1.mk (0x2317619626116186) (0xc6c4c4464684c446)))) (S3.mk (S2.mk (S1.mk (0x4451444444154445) (0x631321d2629121c2)) (S1.mk (0x514051501040415) (0x541054504010145))) (S2.mk (S1.mk (0x4550455044104540) (0x5109580911085801)) (S1.mk (0xa206a4062204a402) (0x1101100911081009)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xd000504090405840) (0xe080a4806080a480)) (S1.mk (0x900080809081808) (0x614441406146414))) (S2.mk (S1.mk (0xc80888804808c8) (0xc40444408404c4)) (S1.mk (0x4948480909484809) (0x2a80280822802a)))) (S3.mk (S2.mk (S1.mk (0x8695c4160695c417) (0x584058501850585)) (S1.mk (0x58c0588018405880) (0xa4c0a4402480a440))) (S2.mk (S1.mk (0x4400440044000000) (0x1100110011000000)) (S1.mk (0x84008000840000) (0xa011a0102091a000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x182218203812182) (0x22000200220000)) (S1.mk (0x11000100110000) (0x848080808480800))) (S2.mk (S1.mk (0x494441404944414) (0xc008c880400888)) (S1.mk (0xc004c440800444) (0x9104901081041)))) (S3.mk (S2.mk (S1.mk (0x6208602042082) (0xa802a08028028)) (S1.mk (0x5401504014014) (0xc800584088405040))) (S2.mk (S1.mk (0xc400a4804480a080) (0x1908180811080808)) (S1.mk (0xa691241522912415) (0x1014100500101005))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4041400900404009) (0x8082800600808006)) (S1.mk (0x808084000080840) (0x414049000040490))) (S2.mk (S1.mk (0x141015000010150) (0x1410041010000410)) (S1.mk (0x8881188188001881) (0x4542254244002542)))) (S3.mk (S2.mk (S1.mk (0x49c1488109404881) (0x86c2844206808442)) (S1.mk (0x484008000840000) (0x2111209020112080))) (S2.mk (S1.mk (0x180218101802181) (0x2022000200220000)) (S1.mk (0x1011000100110000) (0x4848080808480808))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x8494441404944414) (0x880a820288020202)) (S1.mk (0x4405410144010101) (0x1109180811080808))) (S2.mk (S1.mk (0x2206240422040404) (0x2220020222000202)) (S1.mk (0x1190218111802181) (0x4450441444104414)))) (S3.mk (S2.mk (S1.mk (0x345054542052541) (0x5010511050101110)) (S1.mk (0x5040584090404840) (0x504250503052505))) (S2.mk (S1.mk (0xa303a1822281a182) (0xc4c5c4454485c445)) (S1.mk (0x416249602042496) (0xe742a5c26680a5c2)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x841184101401841) (0x582258302812583)) (S1.mk (0xa7d4655466946554) (0x5001504110405041))) (S2.mk (S1.mk (0xc440a4c04480a4c0) (0xe501a4806481a480)) (S1.mk (0x5940180819481808) (0xa684240426842404)))) (S3.mk (S2.mk (S1.mk (0x1096208612842086) (0x1586258213842502)) (S1.mk (0x9901188199001881) (0xe6d5e4546695e455))) (S2.mk (S1.mk (0x2200202002002) (0x4400044044000440)) (S1.mk (0x82008202800002) (0x46c5044746850447))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x2303210222012102) (0x586258303842583)) (S1.mk (0x8795451406914514) (0x5010501150101011))) (S2.mk (S1.mk (0x50c058c8904048c8) (0xa0c0a4c4608084c4)) (S1.mk (0x506058703050587) (0xc456e4564490e446)))) (S3.mk (S2.mk (S1.mk (0xa585250524852505) (0x501050504010505)) (S1.mk (0x190219001802190) (0xe6d6e4566694e452))) (S2.mk (S1.mk (0xa020a00080202000) (0x5010500040101000)) (S1.mk (0x5040500010404000) (0x505050005050504))))))))))) (S10.mk (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x660224c2668024c2) (0xc454c4d44490c4c4)) (S1.mk (0x988088881081888) (0x50c058c0904048c0))) (S2.mk (S1.mk (0x1116211313052117) (0xc6c5c4464685c447)) (S1.mk (0x5414500444101004) (0x5141500111404001)))) (S3.mk (S2.mk (S1.mk (0x1514051011040414) (0x1415100504111004)) (S1.mk (0x4149400901484001) (0x8286800602848002))) (S2.mk (S1.mk (0x90211000802110) (0x84d0c4400490c440)) (S1.mk (0x8820a00088202000) (0x4410500044101000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1140500011404000) (0x2280a00022808000)) (S1.mk (0x1104050011040400) (0x4401050044010100))) (S2.mk (S1.mk (0x6011205060112040) (0x186218603842186)) (S1.mk (0x948080909480801) (0x695441706954417)))) (S3.mk (S2.mk (S1.mk (0x10c018c0904008c0) (0x60c024c0608024c0)) (S1.mk (0x9100901081001) (0x106210703042003))) (S2.mk (S1.mk (0x405440504014004) (0x1180218011802000)) (S1.mk (0xc800484088404040) (0xc410c4904490c080)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8802820288020200) (0x4401410144010100)) (S1.mk (0x2711251522112515) (0x1800184018001840))) (S2.mk (S1.mk (0x2511249024112480) (0x882a822288220222)) (S1.mk (0x4415411144110111) (0x1149184811480848)))) (S3.mk (S2.mk (S1.mk (0x2286248422840484) (0x1194219511852195)) (S1.mk (0xc4c5c4444485c444) (0xc544c5444480c544))) (S2.mk (S1.mk (0xa400a4802480a480) (0x1800180818081808)) (S1.mk (0x2415241524152405) (0x1186218613852186))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x8800080088080800) (0x100010101000001)) (S1.mk (0x400040404000404) (0x515441404114404))) (S2.mk (S1.mk (0x2414649424106484) (0x5048584810484848)) (S1.mk (0xa084a48420848484) (0x180218101812181)))) (S3.mk (S2.mk (S1.mk (0x80208000802080) (0x2101210020012100)) (S1.mk (0x4840480008404800) (0x8480840004808400))) (S2.mk (S1.mk (0x102210303012103) (0x2313219222912182)) (S1.mk (0x405040104050405) (0x504050501040405))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x1190219011802110) (0x4450445044104440)) (S1.mk (0x4405410544014104) (0x1109180911081801))) (S2.mk (S1.mk (0x2206240622042402) (0x486248202842486)) (S1.mk (0x515451404154514) (0x1190210111812101)))) (S3.mk (S2.mk (S1.mk (0xc4d4c4444494c444) (0xa290201022902010)) (S1.mk (0x6602244266002442) (0x8980088189000881))) (S2.mk (S1.mk (0x4641044346010443) (0x8989088989080881)) (S1.mk (0x4450445044104450) (0x1901180111081801))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x2602240222042402) (0x2400240424042404)) (S1.mk (0x4644444646044446) (0x1114010511050105))) (S2.mk (S1.mk (0x2600240026002400) (0x6355615466116144)) (S1.mk (0x444044404040444) (0x482248202802402)))) (S3.mk (S2.mk (S1.mk (0x114411404104104) (0x484048400840404)) (S1.mk (0x111011100110101) (0x600040406002404))) (S2.mk (S1.mk (0x484248000842484) (0xa293e0122291e013)) (S1.mk (0x1010110010101100) (0xc040480080404800)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xc080840040808400) (0x404240002042400)) (S1.mk (0x101410004014100) (0x606440606044406))) (S2.mk (S1.mk (0x22002200220020) (0x11001100110010)) (S1.mk (0x48004800480040) (0x84008400840080)))) (S3.mk (S2.mk (S1.mk (0x48004800480008) (0x22002200220002)) (S1.mk (0x2455245564152445) (0x6000200060002400))) (S2.mk (S1.mk (0x900080009001800) (0x711051106112511)) (S1.mk (0x22000200220022) (0x11000100110011))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x48000800480048) (0xc9c1088189400881)) (S1.mk (0xc6d3045246910453) (0x5141584191404841))) (S2.mk (S1.mk (0xa282a48262808482) (0x1514251113052511)) (S1.mk (0x8800802088208020) (0x4450441044104010)))) (S3.mk (S2.mk (S1.mk (0x918010c0914010c0) (0x635561d4669161c4)) (S1.mk (0x1100010111010101) (0x109000901080009))) (S2.mk (S1.mk (0x182218203802182) (0x584058101850585)) (S1.mk (0x8691841606958417) (0x402240202002402)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x504450404004504) (0xa7d5255562952545)) (S1.mk (0x402240204002402) (0x1080188010001880))) (S2.mk (S1.mk (0x2040244820402448) (0x102010303010103)) (S1.mk (0x8011801000918000) (0x20002200200002)))) (S3.mk (S2.mk (S1.mk (0x10001100100001) (0x40004800400008)) (S1.mk (0x80048400800404) (0x8004800080040))) (S2.mk (S1.mk (0x4008400040080) (0x40400000404000)) (S1.mk (0x8800180088001000) (0x4400240044002000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x20000000200) (0x10000000100)) (S1.mk (0x1100180011000800) (0x2200240022000400))) (S2.mk (S1.mk (0x404000004040000) (0x8101808000018080)) (S1.mk (0x2020000000200000) (0x1010000000100000)))) (S3.mk (S2.mk (S1.mk (0x4840080800400808) (0x8491041500910415)) (S1.mk (0x181088001000880) (0x242044002000440))) (S2.mk (S1.mk (0x1112211311012113) (0xa313a1922291a182)) (S1.mk (0x111009000110080) (0x80208100802081)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4048000800480008) (0x8808820088000200)) (S1.mk (0x4404410044000100) (0x1101180011000800))) (S2.mk (S1.mk (0x2202240022000400) (0x1110210111002101)) (S1.mk (0x344054442042540) (0x4557455644114546)))) (S3.mk (S2.mk (S1.mk (0x515051105050515) (0x504250403042404)) (S1.mk (0x80008000800000) (0xa212a0922290a082))) (S2.mk (S1.mk (0x2000200020000) (0x1000100010000)) (S1.mk (0x1116210713052107) (0x482248202802482))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x46c4044646840446) (0xa795651426956514)) (S1.mk (0xc442a4424480a442) (0x1981188111081881))) (S2.mk (S1.mk (0x2642244222042442) (0xa484240424842404)) (S1.mk (0x1196218613842086) (0x1092209212802092)))) (S3.mk (S2.mk (S1.mk (0x584048501840485) (0x1190211011802110)) (S1.mk (0x1114051111050511) (0x4441054444050544))) (S2.mk (S1.mk (0x1116211611042116) (0x1411111514111114)) (S1.mk (0xc9c8488989484881) (0x6743254266012542))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x184018401850184) (0x411041104150411)) (S1.mk (0x80800000808) (0x104000001040))) (S2.mk (S1.mk (0x208000002080) (0x8000800080000000)) (S1.mk (0x4101000040010000) (0x4140000001400000)))) (S3.mk (S2.mk (S1.mk (0x8291001102910011) (0x2315611426116104)) (S1.mk (0x414000004100000) (0x141000001400000))) (S2.mk (S1.mk (0x282000002800000) (0x8000000080000)) (S1.mk (0x1114010011040100) (0x2000000020000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x514011101050111) (0x541044404050444)) (S1.mk (0x1492248212802402) (0x1415111114011110))) (S2.mk (S1.mk (0x4189488881084880) (0x8246844442048440)) (S1.mk (0x484058500840505) (0x511051504110505)))) (S3.mk (S2.mk (S1.mk (0x1110219011002190) (0x86d3c4520691c453)) (S1.mk (0xc100c1804000c1) (0xc200c2408000c2))) (S2.mk (S1.mk (0x416041602040416) (0x445044504050445)) (S1.mk (0x1500050011000500) (0xc840480088404800)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xc500850044808500) (0x5900580011085800)) (S1.mk (0xa600a4002204a400) (0x4800484008404840))) (S2.mk (S1.mk (0x8400848004808480) (0x182018303810103)) (S1.mk (0x106210603052106) (0x4101000040010400)))) (S3.mk (S2.mk (S1.mk (0x4140000001401000) (0x8390011002902110)) (S1.mk (0x2113211220112102) (0x414000004100010))) (S2.mk (S1.mk (0x141000001400040) (0x282000002800080)) (S1.mk (0xc4c5c4444485c445) (0x4404410554000105))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1101180991000809) (0x2202240662000406)) (S1.mk (0x104001001040) (0x1110219013002090))) (S2.mk (S1.mk (0x802008008020) (0x1001104110401041)) (S1.mk (0x2113219220912182) (0x48c8488808484888)))) (S3.mk (S2.mk (S1.mk (0x84c4844404848444) (0x6652640666146406)) (S1.mk (0x5040504810404048) (0xa080a08420808084))) (S2.mk (S1.mk (0x6652645266106442) (0xc554c5544490c544)) (S1.mk (0x2515651524156515) (0x586258203842502))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xe4d5e4546495e455) (0x849084901480849)) (S1.mk (0x486048602840486) (0x511051504150505))) (S2.mk (S1.mk (0x711051506112515) (0x1194219011842194)) (S1.mk (0x4451445044114451) (0x415541d4449141c4)))) (S3.mk (S2.mk (S1.mk (0x9800184098001840) (0x182218303802183)) (S1.mk (0x414441404104404) (0x105400404014004))) (S2.mk (S1.mk (0x4647444646054446) (0x2614641426146414)) (S1.mk (0x9801180198001801) (0xd9c8588899485880))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xe6c5e4446685e445) (0x4041404900404049)) (S1.mk (0x8082808600808086) (0x514059501050595))) (S2.mk (S1.mk (0x6746654666006546) (0x84d5045544950445)) (S1.mk (0x6653245266112453) (0x2642244226002442)))) (S3.mk (S2.mk (S1.mk (0xa111a1102091a100) (0xc4d5c4154495c415)) (S1.mk (0x20002200200022) (0x10001100100011))) (S2.mk (S1.mk (0x80008400800084) (0x6600244066002440)) (S1.mk (0x85c5454544854545) (0x1190211111812111)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x504058501050585) (0x4645444746054447)) (S1.mk (0xa0c0acc8a0c08cc8) (0xc004c4408004c4))) (S2.mk (S1.mk (0x9104901081049) (0xc80058c0884058c0)) (S1.mk (0xc400a4c04480a4c0) (0x1c108c0814008c0)))) (S3.mk (S2.mk (S1.mk (0x2c204c0428004c0) (0x1016200612042006)) (S1.mk (0x485040504850405) (0x20022200200202))) (S2.mk (S1.mk (0x10011100100101) (0x40084800400808)) (S1.mk (0x8104800081040) (0x4208400042080))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x2802200028020) (0x1401100014010)) (S1.mk (0x8800184088001040) (0x4400248044002080))) (S2.mk (S1.mk (0x1100180811000808) (0x2600240426002404)) (S1.mk (0x8690041402900414) (0x6155615464116144)))) (S3.mk (S2.mk (S1.mk (0x1116210211042102) (0x504058101050581)) (S1.mk (0x515051404150514) (0x1092208212802002))) (S2.mk (S1.mk (0x8081100180001001) (0x4056605644106046)) (S1.mk (0x189088881080880) (0x246044442040440))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x111209000112080) (0x404050500040505)) (S1.mk (0x4048080800480808) (0x8585050504850505))) (S2.mk (S1.mk (0x8808820288000202) (0x4404410144000101)) (S1.mk (0x1101180811000808) (0x2202240422000404)))) (S3.mk (S2.mk (S1.mk (0xa6d2e4522690e452) (0x580058001800580)) (S1.mk (0x8790051006902510) (0x5414510554101105))) (S2.mk (S1.mk (0x5141580991404809) (0xa282a40662808406)) (S1.mk (0x1514259013042490) (0x4541455044014150))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xe353a1d26291a1c2) (0x2445244564052445)) (S1.mk (0x511051104110511) (0x1190019011800190))) (S2.mk (S1.mk (0xc6d2045246900452) (0x918010c0910010c0)) (S1.mk (0x635561d4661161c4) (0x1100010111000101)))) (S3.mk (S2.mk (S1.mk (0x2200200002002) (0x85d4455444944554)) (S1.mk (0x1514059411040494) (0x2313211222112102))) (S2.mk (S1.mk (0x111011000110100) (0x2210201022102010)) (S1.mk (0x504050401040504) (0x401040104010401)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2216601626106006) (0x8901088189000881)) (S1.mk (0x4602044246000442) (0x4442244244002442))) (S2.mk (S1.mk (0xa111a0902091a080) (0x8484040404840404)) (S1.mk (0x1189188891080888) (0x2246244462040444)))) (S3.mk (S2.mk (S1.mk (0x1192218213802082) (0x2213209222912082)) (S1.mk (0x88c8088888480888) (0x44c5044544850445))) (S2.mk (S1.mk (0x8091c0100091c011) (0x102210301012103)) (S1.mk (0x1112210313012103) (0x1182218213802182))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x624220c2628020c2) (0x450445004104450)) (S1.mk (0x4440044044040440) (0x50c8188890481880))) (S2.mk (S1.mk (0x4541044044010440) (0x5141100111401001)) (S1.mk (0xa282200222802002) (0x450444004104440)))) (S3.mk (S2.mk (S1.mk (0x4511055044110540) (0x4148400901484001)) (S1.mk (0x8695c4170695c417) (0x1040104010400040))) (S2.mk (S1.mk (0x401040504010405) (0x1108180811081800)) (S1.mk (0x2204240422042400) (0x1414100004101000)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4141400001404000) (0x8282800002808000)) (S1.mk (0x1414040010040404) (0x4141010040010100))) (S2.mk (S1.mk (0x1414000404100004) (0xc6d2045646940456)) (S1.mk (0x180210001802100) (0xa6d2e4422690e442)))) (S3.mk (S2.mk (S1.mk (0x414100404101004) (0x141400101404001)) (S1.mk (0x282800202808002) (0x1014041010040410))) (S2.mk (S1.mk (0x506250303052507) (0x8685c4060685c407)) (S1.mk (0x506258703042487) (0xe612e4926690e482))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x2022220200222202) (0x1011110100111101)) (S1.mk (0x4048480800484808) (0x848184000481840))) (S2.mk (S1.mk (0x584258101852585) (0x222822000228220)) (S1.mk (0x2202208222002082) (0x1012201212002012)))) (S3.mk (S2.mk (S1.mk (0x2115611424116104) (0x6703254266012542)) (S1.mk (0xc9c0488189404881) (0x1888188898081880))) (S2.mk (S1.mk (0xd9c1188999481889) (0xe6d3645666956457)) (S1.mk (0x414041404140404) (0x180018001810180)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x414041004140410) (0x2206600626006006)) (S1.mk (0x8281000102810001) (0x4041000100400001))) (S2.mk (S1.mk (0x8082000200800002) (0x541044004010040)) (S1.mk (0x4140010040000100) (0x4000400040000)))) (S3.mk (S2.mk (S1.mk (0x80018100800101) (0x10041400100404)) (S1.mk (0x4000400040000000) (0x1000100010000000))) (S2.mk (S1.mk (0x100218001002080) (0x400441004004010)) (S1.mk (0x4000040040000400) (0x100000001001000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x301010102012101) (0x20000000200020)) (S1.mk (0x10000000100010) (0x114011001040114))) (S2.mk (S1.mk (0x86c3844206818443) (0x100001001000)) (S1.mk (0x100210003012100) (0x800008008000)))) (S3.mk (S2.mk (S1.mk (0x400440004044400) (0xa216a0962690a086)) (S1.mk (0x8380010002802100) (0x113011200110102))) (S2.mk (S1.mk (0x80008202a0000202) (0x4000410150000101)) (S1.mk (0x1000180890000808) (0x2000240460000404))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x100218003002080) (0x2012209220902082)) (S1.mk (0x6450640464146404) (0xd901588199405881))) (S2.mk (S1.mk (0xe602a4426680a442) (0x8880188088001880)) (S1.mk (0x4450645044106440) (0x101000000010000)))) (S3.mk (S2.mk (S1.mk (0x4040000000400000) (0x8595451504954515)) (S1.mk (0x101000001000000) (0x202000002000000))) (S2.mk (S1.mk (0x625660d6669060c6) (0x4445444444054444)) (S1.mk (0x415041504150405) (0x1182218213812182))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x808010c0804010c0) (0x415561d4449161c4)) (S1.mk (0x8115c1940491c184) (0x4543254244012542))) (S2.mk (S1.mk (0xa011a0902091a080) (0xd901584199405041)) (S1.mk (0xe602a4826680a082) (0x9980188899080888)))) (S3.mk (S2.mk (S1.mk (0xe454e4d46490e4c4) (0x51c158c0114048c0)) (S1.mk (0xa2c2a4c0228084c0) (0x1116210711052107))) (S2.mk (S1.mk (0x6341214062012140) (0xc941480189404801)) (S1.mk (0xc682840246808402) (0x110011001000010)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x480048000800400) (0x110011000100100)) (S1.mk (0x100000001) (0x4200000042004))) (S2.mk (S1.mk (0x8283c0020281c003) (0x40080080400800)) (S1.mk (0x80040040800400) (0x4200002042000)))) (S3.mk (S2.mk (S1.mk (0x1400004014000) (0x9000104090401040)) (S1.mk (0x6000208060802080) (0x400040004000000))) (S2.mk (S1.mk (0xd101500191405801) (0xe282a4026280a402)) (S1.mk (0x8980088089081880) (0x4640044046042440))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x515449404914484) (0x5141584091404840)) (S1.mk (0xa282a48062808480) (0x8100801081008))) (S2.mk (S1.mk (0x1114210513052105) (0x2800208028002)) (S1.mk (0x9881188198000881) (0x6543244264012442)))) (S3.mk (S2.mk (S1.mk (0x59c1188119401881) (0xa6c2244226802442)) (S1.mk (0xa110a1902090a180) (0x4948480909484801))) (S2.mk (S1.mk (0x8685c4070685c407) (0x506050302050503)) (S1.mk (0x8981088189080881) (0x4642044246040442)))))))))) (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2400248024002480) (0x1800180818001808)) (S1.mk (0x2401240524012405) (0x1184218411842184))) (S2.mk (S1.mk (0x4451445144114451) (0x501050104010501)) (S1.mk (0x2307600626016006) (0x6254605466106044)))) (S3.mk (S2.mk (S1.mk (0x84200000842004) (0xa091e0002091e001)) (S1.mk (0xa294201426902014) (0x40480080404800))) (S2.mk (S1.mk (0x80840040808400) (0x4240002042400)) (S1.mk (0x1410004014100) (0x108118c9900008c9))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x204224c6600004c6) (0x112219303002093)) (S1.mk (0x480248000802400) (0x8110e1900090e180))) (S2.mk (S1.mk (0x2002220200022200) (0x1001110100011100)) (S1.mk (0x849084101480841) (0x486048202840482)))) (S3.mk (S2.mk (S1.mk (0xa395211426912114) (0x1114011411050114)) (S1.mk (0x4441044144050441) (0x44d4445444944454))) (S2.mk (S1.mk (0x414049400040494) (0x141015100010151)) (S1.mk (0xa4c5244564852445) (0x1516251213042512)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xe6c2244266802442) (0xe111a1d06091a1c0)) (S1.mk (0x8684840606848406) (0xa7c5254462852544))) (S2.mk (S1.mk (0x580058101800581) (0x2117611624116106)) (S1.mk (0x644444446046444) (0x4644444446044444)))) (S3.mk (S2.mk (S1.mk (0x182018303800183) (0x1194218511852185)) (S1.mk (0xe742a5426680a542) (0x2454645464146454))) (S2.mk (S1.mk (0xc6c3044646850447) (0x8694c4160694c416)) (S1.mk (0xa291201122912011) (0x8082800200808002))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x141014000010140) (0x410441404104414)) (S1.mk (0x6647244666052447) (0xa213a0922291a082))) (S2.mk (S1.mk (0x6742254266002542) (0x541054404050544)) (S1.mk (0x1492249212802412) (0x584058501840505)))) (S3.mk (S2.mk (S1.mk (0x504250103052501) (0x405440d4449040c4)) (S1.mk (0x4643044246010442) (0x5014400440100004))) (S2.mk (S1.mk (0x5041100110400001) (0xa082200220800002)) (S1.mk (0x514011001040010) (0x1490048010800400))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4150011040100100) (0x1405100104011000)) (S1.mk (0x4109400801084000) (0x8206800402048000))) (S2.mk (S1.mk (0x480058100800501) (0x110051400100504)) (S1.mk (0x110219001002090) (0x84c1c4400481c441)))) (S3.mk (S2.mk (S1.mk (0x6014209464902084) (0x6702250266002502)) (S1.mk (0xd9c0588099405880) (0xe6c0a4406680a440))) (S2.mk (S1.mk (0x82008302810003) (0x84d4045444940444)) (S1.mk (0x1110210113012101) (0x8390011002902100))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6643244266012443) (0x1001180990000809)) (S1.mk (0x2002240660000406) (0x110219003002090))) (S2.mk (S1.mk (0x4848480808484800) (0x8495c4150495c415)) (S1.mk (0x2501250024012500) (0x5840580018405800)))) (S3.mk (S2.mk (S1.mk (0xa491e4002491e401) (0x10c118c9904008c9)) (S1.mk (0x20c224c6608004c6) (0x5948580819485808))) (S2.mk (S1.mk (0xa604a4042204a404) (0x4652045646140456)) (S1.mk (0xa682a4022680a402) (0xa101a1802081a180)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8485c4040485c405) (0x840184000401840)) (S1.mk (0x580258100812581) (0x220822000208220))) (S2.mk (S1.mk (0x1001104110001041) (0x2002208220002082)) (S1.mk (0xe4c5e4446485e445) (0xc540a5c04480a5c0)))) (S3.mk (S2.mk (S1.mk (0xa694641426946414) (0xa280200022802000)) (S1.mk (0x8090c0100090c010) (0x901080109000801))) (S2.mk (S1.mk (0x602040206000402) (0x84d4445444944454)) (S1.mk (0x102210303002103) (0x8391011102912111))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4441044044010441) (0x1110219113012191)) (S1.mk (0x115619404916184) (0x1114011111050111))) (S2.mk (S1.mk (0x8285800702858003) (0x2216201626102006)) (S1.mk (0x2216609626906086) (0x2115619424116184)))) (S3.mk (S2.mk (S1.mk (0x1194018111850185) (0x600040406042404)) (S1.mk (0x415441404154415) (0x484040404840404))) (S2.mk (S1.mk (0xa680240426802404) (0x1016200610042006)) (S1.mk (0x404048000040480) (0x981088109000881)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x642044206000442) (0x1190218011802080)) (S1.mk (0x40084080400840) (0x80048040800480))) (S2.mk (S1.mk (0x1400104014001) (0x880008c0884008c0)) (S1.mk (0x440004c0448004c0) (0x1100100811081008)))) (S3.mk (S2.mk (S1.mk (0xc00880804008c0) (0xc00440408004c0)) (S1.mk (0x2011201020112000) (0x495441504954415))) (S2.mk (S1.mk (0xc008c080400880) (0xc004c040800440)) (S1.mk (0x6200602042002) (0xc400848044808080))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6656645666106446) (0x8988088989080881)) (S1.mk (0x4556655644106546) (0x4414401444100014))) (S2.mk (S1.mk (0x1141104111400041) (0x1584058011840500)) (S1.mk (0x6713255266112542) (0xa822a0028822a000)))) (S3.mk (S2.mk (S1.mk (0x5411500144115000) (0x514451404144514)) (S1.mk (0x8414c4940490c484) (0x106210701052107))) (S2.mk (S1.mk (0x1190018111810181) (0x1196219313852197)) (S1.mk (0xc6d5c4564695c457) (0xc4c0044044800440)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2301210022012100) (0xc480840044808400)) (S1.mk (0x203400202014003) (0xa00280802002a))) (S2.mk (S1.mk (0x405040404050405) (0x900080001081800)) (S1.mk (0x600040002042400) (0x1000100810081008)))) (S3.mk (S2.mk (S1.mk (0x2103200220010002) (0x48c0088008400080)) (S1.mk (0x84c0044004800040) (0x110211000102100))) (S2.mk (S1.mk (0x4008480800084800) (0x8004840400048400)) (S1.mk (0x80200000802000) (0x2212600222106002))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x20200000202000) (0xe000a0406080a040)) (S1.mk (0x900080109080801) (0x605440706054407))) (S2.mk (S1.mk (0x80208000802000) (0x2210601022106000)) (S1.mk (0x2020200020200) (0x1010100010100)))) (S3.mk (S2.mk (S1.mk (0x8808080888080800) (0x2011600020116001)) (S1.mk (0x4004401540000015) (0x1001104910000049))) (S2.mk (S1.mk (0x2002208620000086) (0x110019101000091)) (S1.mk (0x440045404000054) (0x110611000106100))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8195011404910114) (0x180018101810101)) (S1.mk (0x8494041404940404) (0x200000002002000))) (S2.mk (S1.mk (0x200002002000) (0x400004004000)) (S1.mk (0x85d5455444954554) (0xc6c2044246800442)))) (S3.mk (S2.mk (S1.mk (0x1100104011001040) (0x2315619426116184)) (S1.mk (0x584058100850501) (0xa7d5255462952544))) (S2.mk (S1.mk (0xa3c5254562852541) (0x8391011102910111)) (S1.mk (0x486258702842587) (0x1110219111012191))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x504258403052584) (0x501451104054511)) (S1.mk (0x106210703042107) (0x4000500000405000))) (S2.mk (S1.mk (0x8000a0000080a000) (0x501040004010400)) (S1.mk (0x5040100010401000) (0xa080200020802000)))) (S3.mk (S2.mk (S1.mk (0x4010005040100040) (0x108000901080001)) (S1.mk (0x104010101040001) (0x401040404010004))) (S2.mk (S1.mk (0x4010401040104000) (0x108080801080800)) (S1.mk (0x204040402040400) (0x848084000480840)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x484048100840481) (0x111011400110114)) (S1.mk (0x80000000800) (0x40000000400))) (S2.mk (S1.mk (0x186208703842087) (0x1180210111812101)) (S1.mk (0x4454444444144444) (0x87c5054446852540)))) (S3.mk (S2.mk (S1.mk (0x504258503042485) (0x1090209010802010)) (S1.mk (0x625260d2629060c2) (0x405010504010104))) (S2.mk (S1.mk (0x102018303010183) (0x614041406142414)) (S1.mk (0x186218203852186) (0xa191211120912111))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1116210611042106) (0x1102210313012103)) (S1.mk (0x510051004100510) (0x190019001800190))) (S2.mk (S1.mk (0x652045206100452) (0x908010c0900010c0)) (S1.mk (0x615121d0601121c0) (0x4949480909484809)))) (S3.mk (S2.mk (S1.mk (0x8686840606848406) (0x2602240226002402)) (S1.mk (0x4011005040110040) (0x148000901480001))) (S2.mk (S1.mk (0x295001702950013) (0x80d1c4504091c451)) (S1.mk (0x104010501040001) (0x4410441044104000))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x1108180811080800) (0x801084101000841)) (S1.mk (0x512059303010593) (0x228022808200228))) (S2.mk (S1.mk (0x544055404040554) (0x4001500100405001)) (S1.mk (0x8116e1160490e106) (0x511041004110400)))) (S3.mk (S2.mk (S1.mk (0x5048100810481000) (0xa195211520952101)) (S1.mk (0x8828802088200020) (0x4414401044100010))) (S2.mk (S1.mk (0x1141104011400040) (0x2282208022800080)) (S1.mk (0x1506250213042502) (0xa2d1e4506291e451))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xd18050c0914050c0) (0xe240a0c06280a0c0)) (S1.mk (0x8901080989080809) (0x4602040646040406))) (S2.mk (S1.mk (0xc540854044808540) (0x5901580111085801)) (S1.mk (0xa602a4022204a402) (0x4653045646150457)))) (S3.mk (S2.mk (S1.mk (0xa791251522912515) (0x6651645466156455)) (S1.mk (0x1801180118001801) (0x2503250224012502))) (S2.mk (S1.mk (0x2107610624016106) (0x635321d2629121c2)) (S1.mk (0x2415641524156415) (0x4645444646054447)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8293c0120291c013) (0x1900180011081800)) (S1.mk (0x2600240022042400) (0x48c8488808484880))) (S2.mk (S1.mk (0x4654445646144456) (0x2414641424146414)) (S1.mk (0x9980188099081880) (0x6640244066042440)))) (S3.mk (S2.mk (S1.mk (0x85c5454444854544) (0x900080809080808)) (S1.mk (0x604440406044404) (0xc00088804000c8))) (S2.mk (S1.mk (0xc00044408000c4) (0x9004101080049)) (S1.mk (0x406048202040486) (0x5001404010015))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xc000500080405800) (0xc000a0004080a400)) (S1.mk (0x501048004810480) (0x5040100810481008))) (S2.mk (S1.mk (0x141084081400840) (0x282048042800480)) (S1.mk (0x1014200412042004) (0x4441440144014001)))) (S3.mk (S2.mk (S1.mk (0x1801180118000801) (0x2503240224010402)) (S1.mk (0x58c0188018401080) (0xa4c0244024802040))) (S2.mk (S1.mk (0x8110a1100090a100) (0x908080909080801)) (S1.mk (0x605040706050403) (0x81d1055440910554))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x584258501852585) (0x307400606014006)) (S1.mk (0xc4c1044444850445) (0x2212609222906082))) (S2.mk (S1.mk (0xa091600020916001) (0x900080909080809)) (S1.mk (0x614441606144416) (0x112019303000093)))) (S3.mk (S2.mk (S1.mk (0x444045404000054) (0x8110e1100090e100)) (S1.mk (0x1114010411040104) (0x2610241026102410))) (S2.mk (S1.mk (0x695041706950413) (0x809084101080841)) (S1.mk (0x516059303050593) (0x545055404050554))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1194219411842194) (0x2311211122112111)) (S1.mk (0x584058001840500) (0x2713251226112502))) (S2.mk (S1.mk (0xa022a0028022a000) (0x5011500140115000)) (S1.mk (0x841084101400841) (0x482048202800482)))) (S3.mk (S2.mk (S1.mk (0x514051404140514) (0x2511251524152505)) (S1.mk (0x11401000114011) (0x8085800500858001))) (S2.mk (S1.mk (0x102210203002102) (0x2016601624106006)) (S1.mk (0xa293e0022291e003) (0x604040606040406)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xa312e1922290e182) (0xe202a0826280a082)) (S1.mk (0x8181000181000001) (0x630321c2628121c2))) (S2.mk (S1.mk (0x4450444044104440) (0x4441044044010440)) (S1.mk (0x451445004114451) (0x4500050044000500)))) (S3.mk (S2.mk (S1.mk (0x102210203012102) (0x111219000912180)) (S1.mk (0x504050101040401) (0x501050404010504))) (S2.mk (S1.mk (0x109080901080801) (0x206040602040402)) (S1.mk (0x504050101040501) (0x1090209010802090))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x104050101050501) (0x401050404050504)) (S1.mk (0x8290001002900010) (0x504010101050101))) (S2.mk (S1.mk (0x501040404050404) (0x1112210311012103)) (S1.mk (0xa4d4245464942444) (0x40c0488880404888)))) (S3.mk (S2.mk (S1.mk (0x80c0844440808444) (0x809184101081841)) (S1.mk (0x406248202042482) (0x6501248064012480))) (S2.mk (S1.mk (0x82a022208220222) (0x415011104110111)) (S1.mk (0x149084801480848) (0x286048402840484)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xd8c8588898485880) (0xe4c4a4446484a440)) (S1.mk (0x2303218222812182) (0x2210601022106010))) (S2.mk (S1.mk (0x204400606044006) (0x1410111414001114)) (S1.mk (0x4640044246000442) (0x1180210011802100)))) (S3.mk (S2.mk (S1.mk (0x1090009010800090) (0x401040000050401)) (S1.mk (0xa090201020902000) (0x1114010411040004))) (S2.mk (S1.mk (0x11001000110000) (0x48000800480000)) (S1.mk (0x10001000100000) (0x1102210211002102))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x111001000110000) (0x4048000800480000)) (S1.mk (0x8094401400944010) (0x8808800088000000))) (S2.mk (S1.mk (0x4404400044000000) (0x1101100011000000)) (S1.mk (0x2202200022000000) (0x1110010111000101)))) (S3.mk (S2.mk (S1.mk (0x294001602940012) (0x4081408980004089)) (S1.mk (0x8042804640008046) (0x412049202000492))) (S2.mk (S1.mk (0x8102a1020080a102) (0x4880488000084880)) (S1.mk (0x8440844000048440) (0xa094201420942000)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xa2c1a4406281a441) (0x2303200222012002)) (S1.mk (0xc4c1044044810441) (0x10400000104000))) (S2.mk (S1.mk (0x10401000104000) (0x8080800080800)) (S1.mk (0x4040400040400) (0x405440404054405)))) (S3.mk (S2.mk (S1.mk (0x480248000802480) (0x6703240266012402)) (S1.mk (0xe6d1645466956455) (0x6653641666156417))) (S2.mk (S1.mk (0xa283e0022281e003) (0xa312a1922290a182)) (S1.mk (0x6750655066106540) (0xd909580999085801))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xe606a4066604a402) (0x6056605664106046)) (S1.mk (0x11001100110001) (0x600040006002400))) (S2.mk (S1.mk (0x484048000840484) (0x11001000110011)) (S1.mk (0x8480040400800404) (0x1012200210002002)))) (S3.mk (S2.mk (S1.mk (0x8001100180001001) (0x4002200240002002)) (S1.mk (0x180088001000880) (0x240044002000440))) (S2.mk (S1.mk (0x1110210011002000) (0x1504050011040500)) (S1.mk (0x8801080188000801) (0x4503050244010502))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x51c0508011405080) (0xa2c0a0402280a040)) (S1.mk (0x100010001000000) (0x4157615644116146))) (S2.mk (S1.mk (0x2213209222112082) (0x44c4044444840444)) (S1.mk (0x6651640466156405) (0x4552655244106542)))) (S3.mk (S2.mk (S1.mk (0x8111809000918080) (0x8595451404954514)) (S1.mk (0x1181188091000880) (0x2242244062000440))) (S2.mk (S1.mk (0x2306610626006106) (0xc4d0c4404490c440)) (S1.mk (0xa293a0122291a013) (0x908010c0904010c0))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x605420d4649020c4) (0x2216609626106086)) (S1.mk (0xa480a4002480a400) (0xa101a1002081a100))) (S2.mk (S1.mk (0x4840480008484800) (0x8484c4040484c404)) (S1.mk (0x580058100810581) (0xa790251422942514)))) (S3.mk (S2.mk (S1.mk (0x1116211613042116) (0x8680040402800404)) (S1.mk (0x1016200210042002) (0xc1c1400181404001))) (S2.mk (S1.mk (0x8685840706858407) (0x4042200240002002)) (S1.mk (0x1110218011002080) (0x502250203002502)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xa706e5062680e506) (0xa020a220a020a220)) (S1.mk (0x5010511050105110) (0xd880588098085880))) (S2.mk (S1.mk (0xe440a4406404a440) (0x86008602840006)) (S1.mk (0x8680040006802400) (0x1094008010840084)))) (S3.mk (S2.mk (S1.mk (0xd1c1100191401001) (0xe2d3201262912013)) (S1.mk (0x2020220220202202) (0x1010110110101101))) (S2.mk (S1.mk (0x4040480880404808) (0x8080840440808404)) (S1.mk (0x404248002042480) (0x101411004014110))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6414649464106484) (0x1112211313002113)) (S1.mk (0x2401240524052405) (0x1186218613842186))) (S2.mk (S1.mk (0xa6d3e4522691e453) (0xc6d4c4564694c456)) (S1.mk (0x182018203800182) (0x1180218011802180)))) (S3.mk (S2.mk (S1.mk (0x1114010411050104) (0x1180218111812181)) (S1.mk (0x6645244466052445) (0x1110211011002110))) (S2.mk (S1.mk (0x114051100050511) (0x441054400050544)) (S1.mk (0x1402241212002412) (0x8240844242008442)))))))))))) (S11.mk (S10.mk (S9.mk (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x184008501840005) (0x411001504110005)) (S1.mk (0x701050006012500) (0x1094009010840094))) (S2.mk (S1.mk (0x504250103042401) (0x501450404014104)) (S1.mk (0x405040d0409040c0) (0x109080901080809)))) (S3.mk (S2.mk (S1.mk (0x102018203000182) (0x184018000850184)) (S1.mk (0x411041000150411) (0xa091201120912001))) (S2.mk (S1.mk (0x1112210211002102) (0x59c0588819485888)) (S1.mk (0xa6c1a4442685a445) (0x6753255266112542))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x295001602950013) (0x1112211211002112)) (S1.mk (0x8106e1060480e106) (0x4880488080084880))) (S2.mk (S1.mk (0x8440844040048440) (0xa095201520952001)) (S1.mk (0x8490c4100490c410) (0xc9c1488189404881)))) (S3.mk (S2.mk (S1.mk (0x1502250213002502) (0xd980588099085880)) (S1.mk (0xe640a4406604a440) (0xe151a1d06091a1c0))) (S2.mk (S1.mk (0xa292e0122290e012) (0x6501240064012400)) (S1.mk (0x5940180019401800) (0x415001104110011)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x149004801480048) (0x506250203042502)) (S1.mk (0xd8c0588098405880) (0xe4c0a4406480a440))) (S2.mk (S1.mk (0xe6d2245266902452) (0x8284800602848002)) (S1.mk (0x4243000342010003) (0x2414641424106404)))) (S3.mk (S2.mk (S1.mk (0x2200302012003) (0x2715651426156514)) (S1.mk (0x848080808480808) (0x600040406040404))) (S2.mk (S1.mk (0x2400240424002404) (0x2214601426106004)) (S1.mk (0xa391211022912100) (0x8801180188001801))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4402240244002402) (0x1980188019001880)) (S1.mk (0x2640244026002440) (0x1112210213002002))) (S2.mk (S1.mk (0x6402240264002402) (0x8111819000918180)) (S1.mk (0x9901180199001001) (0x6602240266002002)))) (S3.mk (S2.mk (S1.mk (0x9980188099000880) (0x8081c0000081c001)) (S1.mk (0x9101100191001801) (0x6202200262002402))) (S2.mk (S1.mk (0x8980088089001880) (0x4640044046002440)) (S1.mk (0x2216209626902086) (0xc4d1445444954455))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x1582258213802502) (0x710051406102514)) (S1.mk (0x5414510454101104) (0x5141580191404801))) (S2.mk (S1.mk (0x1514251013042410) (0x1194018511850185)) (S1.mk (0x8094c0140094c010) (0x50c058c0104048c0)))) (S3.mk (S2.mk (S1.mk (0x2011209020112080) (0x8101818000818180)) (S1.mk (0x8900080189000801) (0x4600040246000402))) (S2.mk (S1.mk (0x8091001000910011) (0x404020c0408020c0)) (S1.mk (0x8280000002800000) (0x1014000010040000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x8080000000800000) (0x2014209424102084)) (S1.mk (0x8280000002802000) (0xc0c8400880484000))) (S2.mk (S1.mk (0xc0c5800440858001) (0x10110000101)) (S1.mk (0x80880000808) (0x4400040444000404)))) (S3.mk (S2.mk (S1.mk (0x208002002080) (0x2082208220802082)) (S1.mk (0xc0c0400080404000) (0x8504c5040480c504))) (S2.mk (S1.mk (0x1104010411050104) (0x4401040144050401)) (S1.mk (0xc0c0000080400000) (0xc0d1001040910011)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x615441706154417) (0x601040606050407)) (S1.mk (0x84000400840000) (0x8084000400840000))) (S2.mk (S1.mk (0x511051004110500) (0x1196218713842187)) (S1.mk (0x4141000101400001) (0x8282000202800002)))) (S3.mk (S2.mk (S1.mk (0x4501054044010540) (0x4140400101404001)) (S1.mk (0x8280800202808002) (0x441044004010441))) (S2.mk (S1.mk (0x14009404900084) (0x82008302800003)) (S1.mk (0x100210001012100) (0x10209000902080))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x6400248064002480) (0x102010303000103)) (S1.mk (0x184218400852184) (0x411441100154411))) (S2.mk (S1.mk (0xa6d4245466942444) (0x8394411406904114)) (S1.mk (0xa494241424942404) (0x8381010102812101)))) (S3.mk (S2.mk (S1.mk (0x100218103012181) (0x411041104110411)) (S1.mk (0x2211201122112011) (0x1104010411040104))) (S2.mk (S1.mk (0x2703250226012502) (0xe4d1e4506491e451)) (S1.mk (0x441444004014441) (0x8000004080400040)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4014009444900084) (0x6200702052007)) (S1.mk (0x110219000902180) (0xa022a02280222022))) (S2.mk (S1.mk (0x5011501140111011) (0x5048504810484048)) (S1.mk (0x1184018511850185) (0x4411041544150415)))) (S3.mk (S2.mk (S1.mk (0x4145404444014044) (0x411440004114401)) (S1.mk (0x410101c0408101c0) (0x86208302852087))) (S2.mk (S1.mk (0x4140400901484009) (0x1041104110400041)) (S1.mk (0x441044504010045) (0x5108580811085800))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa204a4042204a400) (0xa016e0962490e086)) (S1.mk (0x4652045246100452) (0x615561d4641161c4))) (S2.mk (S1.mk (0x2105610424016104) (0x2111219020112180)) (S1.mk (0x624020c0628020c0) (0x2313219222112182)))) (S3.mk (S2.mk (S1.mk (0xa010a0902090a080) (0xd901580199405001)) (S1.mk (0xe602a4026680a002) (0x9980188099080880))) (S2.mk (S1.mk (0x4143204240012042) (0x41c1088101400881)) (S1.mk (0x82c2044202800442) (0x2610640026106400)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0xc10181c0408181c0) (0x4412641244106402)) (S1.mk (0x1188188811081880) (0x2244244422042440))) (S2.mk (S1.mk (0x8585050400850504) (0x1112211213002012)) (S1.mk (0x2104610424006104) (0x6301214062012140)))) (S3.mk (S2.mk (S1.mk (0xc940480189404801) (0xc680840246808402)) (S1.mk (0x8293001202910013) (0x1000104010401040))) (S2.mk (S1.mk (0x2014209424902084) (0x1194219411852194)) (S1.mk (0x8980088189080881) (0x4651445346154453))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xc1c0400181404001) (0xc2c5c0064281c006)) (S1.mk (0xa014a0942490a084) (0x1104010511050105))) (S2.mk (S1.mk (0x4401040544050405) (0xc1c1000181400001)) (S1.mk (0xc2d3001242910013) (0x506250703052507)))) (S3.mk (S2.mk (S1.mk (0x1184218511852185) (0xa791251522952515)) (S1.mk (0x184218001842184) (0x4141480181404801))) (S2.mk (S1.mk (0x8282840242808402) (0x1414241012042410)) (S1.mk (0x6454645464106444) (0x415041504150415))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8495c4140495c415) (0x216401606104006)) (S1.mk (0xe6d4e4546694e450) (0x1114011011040110))) (S2.mk (S1.mk (0x450045004100450) (0xa291601022916011)) (S1.mk (0x182018303800103) (0x180218001812180)))) (S3.mk (S2.mk (S1.mk (0x410441004144410) (0x14609404906084)) (S1.mk (0xa381210122812101) (0x82218302802183))) (S2.mk (S1.mk (0x100218101012181) (0x205000702050003)) (S1.mk (0x182208303802083) (0x180210101812101))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x410440404144404) (0xa4d0e4402490e440)) (S1.mk (0x10c018c8904008c8) (0x20c024c4608004c4))) (S2.mk (S1.mk (0xc410e4904490e480) (0x634321c2628121c2)) (S1.mk (0xc0c5800540858001) (0x504058401050584)))) (S3.mk (S2.mk (S1.mk (0x8390011002900110) (0x2301210122012101)) (S1.mk (0x102210301002103) (0x8281800202818003))) (S2.mk (S1.mk (0x511051400150504) (0x1400000014001)) (S1.mk (0x4000008040800080) (0x1000000010001)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x81d0055040900550) (0x11400000114001)) (S1.mk (0x1014000510050005) (0x8180000981080009))) (S2.mk (S1.mk (0x1001104110000041) (0x110011101000011)) (S1.mk (0x440044404000444) (0x110411000104100)))) (S3.mk (S2.mk (S1.mk (0x624020c0620020c0) (0x8901080989000809)) (S1.mk (0x4602040646000406) (0x8681840606858407))) (S2.mk (S1.mk (0x4041000040010000) (0x4041000040010001)) (S1.mk (0xa680240026802400) (0x908110c1904010c1))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x615761d6649161c6) (0x6200600042006)) (S1.mk (0x600040206040402) (0x81c1054040810540))) (S2.mk (S1.mk (0x107400604014006) (0x2210201022102000)) (S1.mk (0x8191011000910100) (0x2006600624006006)))) (S3.mk (S2.mk (S1.mk (0x6351215062112140) (0xc949480989484801)) (S1.mk (0xc686840646848402) (0xc4d1045044910451))) (S2.mk (S1.mk (0x2213600222116003) (0x2312611222106102)) (S1.mk (0x4941480109404801) (0x8682840206808402))))))))) (S8.mk (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8292c0120290c012) (0x604020c0600020c0)) (S1.mk (0x8695841706958417) (0x404040100040401))) (S2.mk (S1.mk (0x81c1054440810544) (0x4256405646104046)) (S1.mk (0xa191211020912100) (0x2828202a0820202a)))) (S3.mk (S2.mk (S1.mk (0x4141404901404049) (0x8282808602808086)) (S1.mk (0x1414049410040494) (0x634321c2620121c2))) (S2.mk (S1.mk (0xc9c1488989404889) (0xc6c2844646808446)) (S1.mk (0x684040606840402) (0x2701250422012504))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4317415646114146) (0x1016201610042016)) (S1.mk (0x981088101080881) (0x642044202040442))) (S2.mk (S1.mk (0x1194218411842084) (0x4451441144114011)) (S1.mk (0xa390211022902110) (0xa794651426946514)))) (S3.mk (S2.mk (S1.mk (0x8191011100910111) (0x1100218111012181)) (S1.mk (0x614041406142404) (0x106210203052106))) (S2.mk (S1.mk (0x2701250522012505) (0x1190218011812180)) (S1.mk (0x4450441044144410) (0x6641244066012441)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x8014e0940490e084) (0x2610641422106414)) (S1.mk (0x106210701042107) (0x81d1055040910550))) (S2.mk (S1.mk (0xe351a1d06291a1c0) (0x1102210311012103)) (S1.mk (0xc949480989484809) (0x6200700052007)))) (S3.mk (S2.mk (S1.mk (0x81d1055140910551) (0x624220c2620020c2)) (S1.mk (0x8981088989000889) (0x4642044646000446))) (S2.mk (S1.mk (0x6200302052007) (0x635321d2621121c2)) (S1.mk (0xe6d3e4526691e453) (0x6111215060112140))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x106210703042007) (0xc410c4904490c480)) (S1.mk (0xc6c2844246808442) (0xd000504090405040))) (S2.mk (S1.mk (0xe000a0806080a080) (0x8480840004848400)) (S1.mk (0x8295c0160295c013) (0x2107600624016006)))) (S3.mk (S2.mk (S1.mk (0x2311211022112100) (0xc848480888484800)) (S1.mk (0xc484840444848404) (0x81d5055440950540))) (S2.mk (S1.mk (0x2213601222116013) (0x2312211222102102)) (S1.mk (0x117611604116106) (0x2213201222112002))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x88c8088888480880) (0x495041504950411)) (S1.mk (0x514059101050591) (0x8595051504950505))) (S2.mk (S1.mk (0x8181000981080009) (0x6740254066002540)) (S1.mk (0xa081e0002081e001) (0x2212601222106012)))) (S3.mk (S2.mk (S1.mk (0x2016201624102006) (0xd9c0188099401880)) (S1.mk (0xe6c0244066802440) (0x204000602040002))) (S2.mk (S1.mk (0x5840580818485808) (0xa481a4042485a405)) (S1.mk (0x284000602840002) (0x818100c1814000c1))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x424200c2428000c2) (0x1012201310012013)) (S1.mk (0x402048202000482) (0x8002a0020080a002))) (S2.mk (S1.mk (0x880088008080880) (0x440044004040440)) (S1.mk (0xa084200420842000) (0x220022202000222)))) (S3.mk (S2.mk (S1.mk (0x112211303002113) (0x100000801080008)) (S1.mk (0x100000901080009) (0x586058302850583))) (S2.mk (S1.mk (0x2601240426052405) (0x8090401000904010)) (S1.mk (0xa281200022812001) (0x1116210713042107)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x294401606944016) (0x106210603042106)) (S1.mk (0x8085c0050485c005) (0x4402040244000402))) (S2.mk (S1.mk (0x1980188819081888) (0x2641244426052445)) (S1.mk (0xa291201022912011) (0x416241602042416)))) (S3.mk (S2.mk (S1.mk (0xc54085c0448085c0) (0x2714651426146514)) (S1.mk (0x116211703052117) (0x2650645026106450))) (S2.mk (S1.mk (0x1102210213012102) (0x415121d0409121c0)) (S1.mk (0x4149480901484809) (0xa091e0102091e011))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa283a0022281a003) (0x2312219222102182)) (S1.mk (0xc4d0444044904440) (0x2652645226106452))) (S2.mk (S1.mk (0x1100104011401040) (0x2311219022912180)) (S1.mk (0xc848480888484808) (0x85d5055540950545)))) (S3.mk (S2.mk (S1.mk (0x84d4c4540494c454) (0xa681a4042685a405)) (S1.mk (0x2216209626102086) (0x1116211713042117))) (S2.mk (S1.mk (0xa683a4062685a407) (0x112211303012113)) (S1.mk (0xa690241422902414) (0x484048500840485)))))))) (S7.mk (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4401040144010401) (0xc1c8400981484001)) (S1.mk (0xa290601022906010) (0x1114010511040105))) (S2.mk (S1.mk (0x4441044544010445) (0xe6c1240466852405)) (S1.mk (0x8294401406904014) (0x1114010111050101)))) (S3.mk (S2.mk (S1.mk (0xc6c3840246818402) (0xe702a5026680a502)) (S1.mk (0xe6c3244266812443) (0x1012201312012013))) (S2.mk (S1.mk (0x215001702150013) (0x1194019411840194)) (S1.mk (0x4651445346114453) (0x8216809606908086))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x1100010011010100) (0x4400040044040400)) (S1.mk (0x4051001040110011) (0x5001500110405001))) (S2.mk (S1.mk (0xa016e0162490e006) (0x1010201010002010)) (S1.mk (0x1012201210002012) (0x6747654666016546)))) (S3.mk (S2.mk (S1.mk (0x4650445246104452) (0x8085800400858001)) (S1.mk (0x211401202114013) (0x605660d6649060c6))) (S2.mk (S1.mk (0x1190219011812190) (0x4650445246144452)) (S1.mk (0x8291c0120291c013) (0xc454c4544490c444)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2501250524052505) (0xe4d4e4546494e450)) (S1.mk (0xe256e0566690e046) (0x2214609426106084))) (S2.mk (S1.mk (0xa791251422952504) (0x1116211613042016)) (S1.mk (0x8295801702958013) (0xa194611424906114)))) (S3.mk (S2.mk (S1.mk (0x485040404850405) (0xa391611022916110)) (S1.mk (0x1114011511040115) (0xe6c3244666852447))) (S2.mk (S1.mk (0xd08150c1904050c1) (0xe056e0d66490e0c6)) (S1.mk (0xa216e0162690e006) (0x84d1c4500491c451))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4543054244010542) (0x901080909000809)) (S1.mk (0x602040606000406) (0x1016200710052007))) (S2.mk (S1.mk (0x8095c0140095c011) (0x604220c2608020c2)) (S1.mk (0x981088909080889) (0x642044606040446)))) (S3.mk (S2.mk (S1.mk (0x4655445646154457) (0x9101104191401041)) (S1.mk (0x6202208262802082) (0x605440506054405))) (S2.mk (S1.mk (0x615441606154417) (0x8216c0960690c086)) (S1.mk (0xe141a1c06081a1c0) (0x8686c4060684c406))))))) (S6.mk (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x2200208022002080) (0x8800080888000808)) (S1.mk (0x49004901480049) (0x84d5445544954455))) (S2.mk (S1.mk (0x8010809000908080) (0x8014809404908084)) (S1.mk (0x8180000181000001) (0x4241000342010003)))) (S3.mk (S2.mk (S1.mk (0x8284c0060284c006) (0xa311a1902291a180)) (S1.mk (0x84c5044544850445) (0x6652245266102452))) (S2.mk (S1.mk (0xe6d1645066916451) (0xc054e0d44490e0c4)) (S1.mk (0x4641044246010442) (0x5148500811485000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0xa295e0142295e011) (0x586058702850587)) (S1.mk (0x112211203002112) (0x425600d6469000c6))) (S2.mk (S1.mk (0xc2c5800742858003) (0x1112211213012112)) (S1.mk (0x486248302842483) (0x2711251522152515)))) (S3.mk (S2.mk (S1.mk (0x110411000104110) (0x110011101000111)) (S1.mk (0x1416241212042412) (0xc6c7844646858447))) (S2.mk (S1.mk (0x8181010100810101) (0x81c1054140810541)) (S1.mk (0x2200300012003) (0xa391611122916111)))))) (S5.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x4643044646050447) (0x1094208410842084)) (S1.mk (0xc2d5c0174295c013) (0xa014e0142490e004))) (S2.mk (S1.mk (0xa214e0942690e084) (0xe6d2e4526690e452)) (S1.mk (0x5048500810485000) (0xa084a0042084a000)))) (S3.mk (S2.mk (S1.mk (0xa002a0022080a002) (0x2203200222012003)) (S1.mk (0x2603240626052407) (0x216001606100006))) (S2.mk (S1.mk (0xa297e0162295e013) (0x415101d0409101c0)) (S1.mk (0xc1c9400981484009) (0x1094008410840084))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x4051001140110011) (0xa781250422852504)) (S1.mk (0x1016201712052017) (0x414101c0408101c0))) (S2.mk (S1.mk (0x4141400901484009) (0x6651645066116451)) (S1.mk (0xc18140c1814040c1) (0xc256c0d64690c0c6)))) (S3.mk (S2.mk (S1.mk (0x2701250422052504) (0x1016201612042016)) (S1.mk (0x6650645066106450) (n0))) (z2)))))))) (z9)) (z10))
noncomputable def theMasks : VMasks := let m0 := vm0; let m1 := Nat.lor m0 (Nat.shiftLeft m0 vsh0); let m2 := Nat.lor m1 (Nat.shiftLeft m1 vsh1); let m3 := Nat.lor m2 (Nat.shiftLeft m2 vsh2); let m4 := Nat.lor m3 (Nat.shiftLeft m3 vsh3); let m5 := Nat.lor m4 (Nat.shiftLeft m4 vsh4); let m6 := Nat.lor m5 (Nat.shiftLeft m5 vsh5); let m7 := Nat.lor m6 (Nat.shiftLeft m6 vsh6); let m8 := Nat.lor m7 (Nat.shiftLeft m7 vsh7); let m9 := Nat.lor m8 (Nat.shiftLeft m8 vsh8); let m10 := Nat.lor m9 (Nat.shiftLeft m9 vsh9); let m11 := Nat.lor m10 (Nat.shiftLeft m10 vsh10); VMasks.mk m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
noncomputable def ok14 (rs v : S12) : Bool := al12 (fun _ vi => Nat.beq (Nat.land vi hi2L) n0) rs v
noncomputable def stepStr (rs tr : S12) (sh : Nat) : Nat := pv12 (mp12 (fun r => Nat.lor (Nat.add (g12 tr (Nat.land r m13)) (g12 tr (Nat.land (Nat.shiftRight r k13) m13))) (Nat.shiftLeft (g12 tr (Nat.land (Nat.shiftRight r k26) m13)) sh)) rs)
noncomputable def stepLtr (rs tr : S12) : Nat := pv12 (mp12 (fun r => Nat.add (g12 tr (Nat.land r m13)) (g12 tr (Nat.land (Nat.shiftRight r k13) m13))) rs)
noncomputable def stepRtr (rs tr : S12) : Nat := pv12 (mp12 (fun r => g12 tr (Nat.land (Nat.shiftRight r k26) m13)) rs)
noncomputable def stepS (ms : VMasks) (rs : S12) (v sh : Nat) : Nat := stepStr rs (uv12 ms v) sh
noncomputable def stepL (ms : VMasks) (rs : S12) (v : Nat) : Nat := stepLtr rs (uv12 ms v)
noncomputable def stepR (ms : VMasks) (rs : S12) (v : Nat) : Nat := stepRtr rs (uv12 ms v)
noncomputable def chkV (ms : VMasks) (rs : S12) (v : Nat) : Bool := let tr := uv12 ms v; Bool.rec false (al12 (fun r vi => Nat.beq (Nat.land (Nat.add (Nat.mul (Nat.sub lim15 (Nat.mul kP (Nat.land (Nat.shiftRight r k39) m13))) repL) (Nat.mul kQ vi)) msbL) n0) rs tr) (ok14 rs tr)
noncomputable def runSuf (ms : VMasks) (rs : S12) : List Nat -> Nat -> Bool × Nat := List.rec (fun v => (ok14 rs (uv12 ms v), v)) (fun sh _ ih v => let tr := uv12 ms v; Bool.rec (false, n0) (ih (stepStr rs tr sh)) (ok14 rs tr))
noncomputable def walkHi (ms : VMasks) (rs : S12) : Nat -> Nat -> Bool := Nat.rec (chkV ms rs) (fun _ ih v => let tr := uv12 ms v; Bool.rec false (Bool.rec false (ih (stepRtr rs tr)) (ih (stepLtr rs tr))) (ok14 rs tr))
def shList : List Nat := [16, 32, 64, 128, 256, 512, 1024, 2048]
noncomputable def checkAll : Bool :=
  let ms := theMasks; let rs := rsTree
  let v0 := pv12 (mp12 (fun r => Nat.land (Nat.shiftRight r k39) m13) rs)
  let p := runSuf ms rs shList v0
  p.1 && walkHi ms rs kBhi p.2
theorem strip_cert_ok : checkAll = true := by decide +kernel

structure Nib16 where (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : S4)
def nib00 : Nib16 := Nib16.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x100000001)) (S1.mk (0x0) (0x100000001))) (S2.mk (S1.mk (0x8000000080) (0x8100000081)) (S1.mk (0x8000000080) (0x8100000081)))) (S3.mk (S2.mk (S1.mk (0x0) (0x100000001)) (S1.mk (0x0) (0x100000001))) (S2.mk (S1.mk (0x8000000080) (0x8100000081)) (S1.mk (0x8000000080) (0x8100000081))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x400000004000)) (S1.mk (0x0) (0x400000004000))) (S2.mk (S1.mk (0x80000000800) (0x480000004800)) (S1.mk (0x80000000800) (0x480000004800)))) (S3.mk (S2.mk (S1.mk (0x0) (0x400000004000)) (S1.mk (0x0) (0x400000004000))) (S2.mk (S1.mk (0x80000000800) (0x480000004800)) (S1.mk (0x80000000800) (0x480000004800))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x1000000010000000)) (S1.mk (0x0) (0x1000000010000000))) (S2.mk (S1.mk (0x800000008000000) (0x1800000018000000)) (S1.mk (0x800000008000000) (0x1800000018000000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x1000000010000000)) (S1.mk (0x0) (0x1000000010000000))) (S2.mk (S1.mk (0x800000008000000) (0x1800000018000000)) (S1.mk (0x800000008000000) (0x1800000018000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x40000000400000)) (S1.mk (0x0) (0x40000000400000))) (S2.mk (S1.mk (0x8000000080000) (0x48000000480000)) (S1.mk (0x8000000080000) (0x48000000480000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x40000000400000)) (S1.mk (0x0) (0x40000000400000))) (S2.mk (S1.mk (0x8000000080000) (0x48000000480000)) (S1.mk (0x8000000080000) (0x48000000480000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x100000001000000)) (S1.mk (0x0) (0x100000001000000))) (S2.mk (S1.mk (0x8000000080000000) (0x8100000081000000)) (S1.mk (0x8000000080000000) (0x8100000081000000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x100000001000000)) (S1.mk (0x0) (0x100000001000000))) (S2.mk (S1.mk (0x8000000080000000) (0x8100000081000000)) (S1.mk (0x8000000080000000) (0x8100000081000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x40000000400000)) (S1.mk (0x0) (0x40000000400000))) (S2.mk (S1.mk (0x8000000080000) (0x48000000480000)) (S1.mk (0x8000000080000) (0x48000000480000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x40000000400000)) (S1.mk (0x0) (0x40000000400000))) (S2.mk (S1.mk (0x8000000080000) (0x48000000480000)) (S1.mk (0x8000000080000) (0x48000000480000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x100000001000)) (S1.mk (0x0) (0x100000001000))) (S2.mk (S1.mk (0x80000000800) (0x180000001800)) (S1.mk (0x80000000800) (0x180000001800)))) (S3.mk (S2.mk (S1.mk (0x0) (0x100000001000)) (S1.mk (0x0) (0x100000001000))) (S2.mk (S1.mk (0x80000000800) (0x180000001800)) (S1.mk (0x80000000800) (0x180000001800))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x4000000040)) (S1.mk (0x0) (0x4000000040))) (S2.mk (S1.mk (0x800000008) (0x4800000048)) (S1.mk (0x800000008) (0x4800000048)))) (S3.mk (S2.mk (S1.mk (0x0) (0x4000000040)) (S1.mk (0x0) (0x4000000040))) (S2.mk (S1.mk (0x800000008) (0x4800000048)) (S1.mk (0x800000008) (0x4800000048))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x1000000000000)) (S1.mk (0x0) (0x1000000000000))) (S2.mk (S1.mk (0x80000000000000) (0x81000000000000)) (S1.mk (0x80000000000000) (0x81000000000000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x1000000000000)) (S1.mk (0x0) (0x1000000000000))) (S2.mk (S1.mk (0x80000000000000) (0x81000000000000)) (S1.mk (0x80000000000000) (0x81000000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x4000000000000000)) (S1.mk (0x0) (0x4000000000000000))) (S2.mk (S1.mk (0x800000000000000) (0x4800000000000000)) (S1.mk (0x800000000000000) (0x4800000000000000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x4000000000000000)) (S1.mk (0x0) (0x4000000000000000))) (S2.mk (S1.mk (0x800000000000000) (0x4800000000000000)) (S1.mk (0x800000000000000) (0x4800000000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x100000000000)) (S1.mk (0x0) (0x100000000000))) (S2.mk (S1.mk (0x80000000000) (0x180000000000)) (S1.mk (0x80000000000) (0x180000000000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x100000000000)) (S1.mk (0x0) (0x100000000000))) (S2.mk (S1.mk (0x80000000000) (0x180000000000)) (S1.mk (0x80000000000) (0x180000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x4000000000)) (S1.mk (0x0) (0x4000000000))) (S2.mk (S1.mk (0x800000000) (0x4800000000)) (S1.mk (0x800000000) (0x4800000000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x4000000000)) (S1.mk (0x0) (0x4000000000))) (S2.mk (S1.mk (0x800000000) (0x4800000000)) (S1.mk (0x800000000) (0x4800000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x1000000)) (S1.mk (0x0) (0x1000000))) (S2.mk (S1.mk (0x80000000) (0x81000000)) (S1.mk (0x80000000) (0x81000000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x1000000)) (S1.mk (0x0) (0x1000000))) (S2.mk (S1.mk (0x80000000) (0x81000000)) (S1.mk (0x80000000) (0x81000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x400000)) (S1.mk (0x0) (0x400000))) (S2.mk (S1.mk (0x80000) (0x480000)) (S1.mk (0x80000) (0x480000)))) (S3.mk (S2.mk (S1.mk (0x0) (0x400000)) (S1.mk (0x0) (0x400000))) (S2.mk (S1.mk (0x80000) (0x480000)) (S1.mk (0x80000) (0x480000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x1000)) (S1.mk (0x0) (0x1000))) (S2.mk (S1.mk (0x800) (0x1800)) (S1.mk (0x800) (0x1800)))) (S3.mk (S2.mk (S1.mk (0x0) (0x1000)) (S1.mk (0x0) (0x1000))) (S2.mk (S1.mk (0x800) (0x1800)) (S1.mk (0x800) (0x1800))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x40)) (S1.mk (0x0) (0x40))) (S2.mk (S1.mk (0x8) (0x48)) (S1.mk (0x8) (0x48)))) (S3.mk (S2.mk (S1.mk (0x0) (0x40)) (S1.mk (0x0) (0x40))) (S2.mk (S1.mk (0x8) (0x48)) (S1.mk (0x8) (0x48)))))
def nib01 : Nib16 := Nib16.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x800000008) (0x800000008))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x800000008) (0x800000008)))) (S3.mk (S2.mk (S1.mk (0x2000000020) (0x2000000020)) (S1.mk (0x2800000028) (0x2800000028))) (S2.mk (S1.mk (0x2000000020) (0x2000000020)) (S1.mk (0x2800000028) (0x2800000028))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x200000002000) (0x200000002000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x200000002000) (0x200000002000)))) (S3.mk (S2.mk (S1.mk (0x20000000200) (0x20000000200)) (S1.mk (0x220000002200) (0x220000002200))) (S2.mk (S1.mk (0x20000000200) (0x20000000200)) (S1.mk (0x220000002200) (0x220000002200))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x8000000080000000) (0x8000000080000000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x8000000080000000) (0x8000000080000000)))) (S3.mk (S2.mk (S1.mk (0x200000002000000) (0x200000002000000)) (S1.mk (0x8200000082000000) (0x8200000082000000))) (S2.mk (S1.mk (0x200000002000000) (0x200000002000000)) (S1.mk (0x8200000082000000) (0x8200000082000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x20000000200000) (0x20000000200000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x20000000200000) (0x20000000200000)))) (S3.mk (S2.mk (S1.mk (0x2000000020000) (0x2000000020000)) (S1.mk (0x22000000220000) (0x22000000220000))) (S2.mk (S1.mk (0x2000000020000) (0x2000000020000)) (S1.mk (0x22000000220000) (0x22000000220000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x800000008000000) (0x800000008000000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x800000008000000) (0x800000008000000)))) (S3.mk (S2.mk (S1.mk (0x2000000020000000) (0x2000000020000000)) (S1.mk (0x2800000028000000) (0x2800000028000000))) (S2.mk (S1.mk (0x2000000020000000) (0x2000000020000000)) (S1.mk (0x2800000028000000) (0x2800000028000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x20000000200000) (0x20000000200000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x20000000200000) (0x20000000200000)))) (S3.mk (S2.mk (S1.mk (0x2000000020000) (0x2000000020000)) (S1.mk (0x22000000220000) (0x22000000220000))) (S2.mk (S1.mk (0x2000000020000) (0x2000000020000)) (S1.mk (0x22000000220000) (0x22000000220000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x800000008000) (0x800000008000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x800000008000) (0x800000008000)))) (S3.mk (S2.mk (S1.mk (0x20000000200) (0x20000000200)) (S1.mk (0x820000008200) (0x820000008200))) (S2.mk (S1.mk (0x20000000200) (0x20000000200)) (S1.mk (0x820000008200) (0x820000008200))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x2000000020) (0x2000000020))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x2000000020) (0x2000000020)))) (S3.mk (S2.mk (S1.mk (0x200000002) (0x200000002)) (S1.mk (0x2200000022) (0x2200000022))) (S2.mk (S1.mk (0x200000002) (0x200000002)) (S1.mk (0x2200000022) (0x2200000022))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x8000000000000) (0x8000000000000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x8000000000000) (0x8000000000000)))) (S3.mk (S2.mk (S1.mk (0x20000000000000) (0x20000000000000)) (S1.mk (0x28000000000000) (0x28000000000000))) (S2.mk (S1.mk (0x20000000000000) (0x20000000000000)) (S1.mk (0x28000000000000) (0x28000000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x2000000000000000) (0x2000000000000000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x2000000000000000) (0x2000000000000000)))) (S3.mk (S2.mk (S1.mk (0x200000000000000) (0x200000000000000)) (S1.mk (0x2200000000000000) (0x2200000000000000))) (S2.mk (S1.mk (0x200000000000000) (0x200000000000000)) (S1.mk (0x2200000000000000) (0x2200000000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x800000000000) (0x800000000000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x800000000000) (0x800000000000)))) (S3.mk (S2.mk (S1.mk (0x20000000000) (0x20000000000)) (S1.mk (0x820000000000) (0x820000000000))) (S2.mk (S1.mk (0x20000000000) (0x20000000000)) (S1.mk (0x820000000000) (0x820000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x2000000000) (0x2000000000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x2000000000) (0x2000000000)))) (S3.mk (S2.mk (S1.mk (0x200000000) (0x200000000)) (S1.mk (0x2200000000) (0x2200000000))) (S2.mk (S1.mk (0x200000000) (0x200000000)) (S1.mk (0x2200000000) (0x2200000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x8000000) (0x8000000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x8000000) (0x8000000)))) (S3.mk (S2.mk (S1.mk (0x20000000) (0x20000000)) (S1.mk (0x28000000) (0x28000000))) (S2.mk (S1.mk (0x20000000) (0x20000000)) (S1.mk (0x28000000) (0x28000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x200000) (0x200000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x200000) (0x200000)))) (S3.mk (S2.mk (S1.mk (0x20000) (0x20000)) (S1.mk (0x220000) (0x220000))) (S2.mk (S1.mk (0x20000) (0x20000)) (S1.mk (0x220000) (0x220000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x8000) (0x8000))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x8000) (0x8000)))) (S3.mk (S2.mk (S1.mk (0x200) (0x200)) (S1.mk (0x8200) (0x8200))) (S2.mk (S1.mk (0x200) (0x200)) (S1.mk (0x8200) (0x8200))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x20) (0x20))) (S2.mk (S1.mk (0x0) (0x0)) (S1.mk (0x20) (0x20)))) (S3.mk (S2.mk (S1.mk (0x2) (0x2)) (S1.mk (0x22) (0x22))) (S2.mk (S1.mk (0x2) (0x2)) (S1.mk (0x22) (0x22)))))
def nib11 : Nib16 := Nib16.mk (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x200000002)) (S1.mk (0x400000004) (0x600000006))) (S2.mk (S1.mk (0x4000000040) (0x4200000042)) (S1.mk (0x4400000044) (0x4600000046)))) (S3.mk (S2.mk (S1.mk (0x1000000010) (0x1200000012)) (S1.mk (0x1400000014) (0x1600000016))) (S2.mk (S1.mk (0x5000000050) (0x5200000052)) (S1.mk (0x5400000054) (0x5600000056))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x800000008000)) (S1.mk (0x100000001000) (0x900000009000))) (S2.mk (S1.mk (0x40000000400) (0x840000008400)) (S1.mk (0x140000001400) (0x940000009400)))) (S3.mk (S2.mk (S1.mk (0x10000000100) (0x810000008100)) (S1.mk (0x110000001100) (0x910000009100))) (S2.mk (S1.mk (0x50000000500) (0x850000008500)) (S1.mk (0x150000001500) (0x950000009500))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x2000000020000000)) (S1.mk (0x4000000040000000) (0x6000000060000000))) (S2.mk (S1.mk (0x400000004000000) (0x2400000024000000)) (S1.mk (0x4400000044000000) (0x6400000064000000)))) (S3.mk (S2.mk (S1.mk (0x100000001000000) (0x2100000021000000)) (S1.mk (0x4100000041000000) (0x6100000061000000))) (S2.mk (S1.mk (0x500000005000000) (0x2500000025000000)) (S1.mk (0x4500000045000000) (0x6500000065000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x80000000800000)) (S1.mk (0x10000000100000) (0x90000000900000))) (S2.mk (S1.mk (0x4000000040000) (0x84000000840000)) (S1.mk (0x14000000140000) (0x94000000940000)))) (S3.mk (S2.mk (S1.mk (0x1000000010000) (0x81000000810000)) (S1.mk (0x11000000110000) (0x91000000910000))) (S2.mk (S1.mk (0x5000000050000) (0x85000000850000)) (S1.mk (0x15000000150000) (0x95000000950000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x200000002000000)) (S1.mk (0x400000004000000) (0x600000006000000))) (S2.mk (S1.mk (0x4000000040000000) (0x4200000042000000)) (S1.mk (0x4400000044000000) (0x4600000046000000)))) (S3.mk (S2.mk (S1.mk (0x1000000010000000) (0x1200000012000000)) (S1.mk (0x1400000014000000) (0x1600000016000000))) (S2.mk (S1.mk (0x5000000050000000) (0x5200000052000000)) (S1.mk (0x5400000054000000) (0x5600000056000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x80000000800000)) (S1.mk (0x10000000100000) (0x90000000900000))) (S2.mk (S1.mk (0x4000000040000) (0x84000000840000)) (S1.mk (0x14000000140000) (0x94000000940000)))) (S3.mk (S2.mk (S1.mk (0x1000000010000) (0x81000000810000)) (S1.mk (0x11000000110000) (0x91000000910000))) (S2.mk (S1.mk (0x5000000050000) (0x85000000850000)) (S1.mk (0x15000000150000) (0x95000000950000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x200000002000)) (S1.mk (0x400000004000) (0x600000006000))) (S2.mk (S1.mk (0x40000000400) (0x240000002400)) (S1.mk (0x440000004400) (0x640000006400)))) (S3.mk (S2.mk (S1.mk (0x10000000100) (0x210000002100)) (S1.mk (0x410000004100) (0x610000006100))) (S2.mk (S1.mk (0x50000000500) (0x250000002500)) (S1.mk (0x450000004500) (0x650000006500))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x8000000080)) (S1.mk (0x1000000010) (0x9000000090))) (S2.mk (S1.mk (0x400000004) (0x8400000084)) (S1.mk (0x1400000014) (0x9400000094)))) (S3.mk (S2.mk (S1.mk (0x100000001) (0x8100000081)) (S1.mk (0x1100000011) (0x9100000091))) (S2.mk (S1.mk (0x500000005) (0x8500000085)) (S1.mk (0x1500000015) (0x9500000095))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x2000000000000)) (S1.mk (0x4000000000000) (0x6000000000000))) (S2.mk (S1.mk (0x40000000000000) (0x42000000000000)) (S1.mk (0x44000000000000) (0x46000000000000)))) (S3.mk (S2.mk (S1.mk (0x10000000000000) (0x12000000000000)) (S1.mk (0x14000000000000) (0x16000000000000))) (S2.mk (S1.mk (0x50000000000000) (0x52000000000000)) (S1.mk (0x54000000000000) (0x56000000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x8000000000000000)) (S1.mk (0x1000000000000000) (0x9000000000000000))) (S2.mk (S1.mk (0x400000000000000) (0x8400000000000000)) (S1.mk (0x1400000000000000) (0x9400000000000000)))) (S3.mk (S2.mk (S1.mk (0x100000000000000) (0x8100000000000000)) (S1.mk (0x1100000000000000) (0x9100000000000000))) (S2.mk (S1.mk (0x500000000000000) (0x8500000000000000)) (S1.mk (0x1500000000000000) (0x9500000000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x200000000000)) (S1.mk (0x400000000000) (0x600000000000))) (S2.mk (S1.mk (0x40000000000) (0x240000000000)) (S1.mk (0x440000000000) (0x640000000000)))) (S3.mk (S2.mk (S1.mk (0x10000000000) (0x210000000000)) (S1.mk (0x410000000000) (0x610000000000))) (S2.mk (S1.mk (0x50000000000) (0x250000000000)) (S1.mk (0x450000000000) (0x650000000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x8000000000)) (S1.mk (0x1000000000) (0x9000000000))) (S2.mk (S1.mk (0x400000000) (0x8400000000)) (S1.mk (0x1400000000) (0x9400000000)))) (S3.mk (S2.mk (S1.mk (0x100000000) (0x8100000000)) (S1.mk (0x1100000000) (0x9100000000))) (S2.mk (S1.mk (0x500000000) (0x8500000000)) (S1.mk (0x1500000000) (0x9500000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x2000000)) (S1.mk (0x4000000) (0x6000000))) (S2.mk (S1.mk (0x40000000) (0x42000000)) (S1.mk (0x44000000) (0x46000000)))) (S3.mk (S2.mk (S1.mk (0x10000000) (0x12000000)) (S1.mk (0x14000000) (0x16000000))) (S2.mk (S1.mk (0x50000000) (0x52000000)) (S1.mk (0x54000000) (0x56000000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x800000)) (S1.mk (0x100000) (0x900000))) (S2.mk (S1.mk (0x40000) (0x840000)) (S1.mk (0x140000) (0x940000)))) (S3.mk (S2.mk (S1.mk (0x10000) (0x810000)) (S1.mk (0x110000) (0x910000))) (S2.mk (S1.mk (0x50000) (0x850000)) (S1.mk (0x150000) (0x950000))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x2000)) (S1.mk (0x4000) (0x6000))) (S2.mk (S1.mk (0x400) (0x2400)) (S1.mk (0x4400) (0x6400)))) (S3.mk (S2.mk (S1.mk (0x100) (0x2100)) (S1.mk (0x4100) (0x6100))) (S2.mk (S1.mk (0x500) (0x2500)) (S1.mk (0x4500) (0x6500))))) (S4.mk (S3.mk (S2.mk (S1.mk (0x0) (0x80)) (S1.mk (0x10) (0x90))) (S2.mk (S1.mk (0x4) (0x84)) (S1.mk (0x14) (0x94)))) (S3.mk (S2.mk (S1.mk (0x1) (0x81)) (S1.mk (0x11) (0x91))) (S2.mk (S1.mk (0x5) (0x85)) (S1.mk (0x15) (0x95)))))
noncomputable def getNib (nt : Nib16) (j : Nat) : S4 :=
  if j = 0 then nt.t0 else if j = 1 then nt.t1 else if j = 2 then nt.t2 else if j = 3 then nt.t3 else if j = 4 then nt.t4 else if j = 5 then nt.t5 else if j = 6 then nt.t6 else if j = 7 then nt.t7 else if j = 8 then nt.t8 else if j = 9 then nt.t9 else if j = 10 then nt.t10 else if j = 11 then nt.t11 else if j = 12 then nt.t12 else if j = 13 then nt.t13 else if j = 14 then nt.t14 else nt.t15
noncomputable def nibLoop (nt : Nib16) (m : Nat) : Nat -> Nat := Nat.rec n0 (fun j ih =>
  Nat.lor ih (g4 (getNib nt j) (Nat.land (Nat.shiftRight m (Nat.mul k4 j)) k15)))
noncomputable def chkEdge (ms : S12) (sm q' : Nat) : Bool :=
  Bool.rec (Nat.beq sm n0) (Nat.beq (Nat.land sm (Nat.xor all64 (g12 ms q'))) n0) (Nat.ble (Nat.add q' k1) kM)
noncomputable def allActive (rs : S12) : Nat -> Bool := Nat.rec true (fun q ih =>
  Bool.rec false (Bool.rec true false (Nat.beq (g12 rs q) n0)) ih)
noncomputable def coverNode (r m : Nat) : Bool :=
  let w := Nat.land (Nat.shiftRight r k39) m13
  let e0 := Nat.land r m13
  let e1 := Nat.land (Nat.shiftRight r k13) m13
  let e2 := Nat.land (Nat.shiftRight r k26) m13
  (Nat.ble kwMin w && Nat.ble e0 kM && Nat.ble e1 kM && Nat.ble e2 kM && Nat.ble w kw0) &&
  (chkEdge msTree (nibLoop nib00 m k16) e0 && chkEdge msTree (nibLoop nib01 m k16) e1 && chkEdge msTree (nibLoop nib11 m k16) e2)
noncomputable def checkCover : Bool :=
  (Nat.beq (g12 msTree n0) all64 && Nat.beq (Nat.land (Nat.shiftRight (g12 rsTree n0) k39) m13) kw0 && Nat.beq (g12 rsTree kM) n0) &&
  (allActive rsTree kM && al12 coverNode rsTree msTree)
theorem cover_ok : checkCover = true := by decide +kernel
def code6 (f : Nat -> Bool) : Nat :=
  (if f 0 then 1 else 0) + 2 * ((if f 1 then 1 else 0) + 2 * ((if f 2 then 1 else 0) +
  2 * ((if f 3 then 1 else 0) + 2 * ((if f 4 then 1 else 0) + 2 * (if f 5 then 1 else 0)))))
def nextCode6 (c0 : Bool) (s : Nat) (ext : Bool) : Nat :=
  code6 (fun j =>
    let l := if j = 0 then c0 else s.testBit (j - 1)
    let m := s.testBit j
    let r := if j = 5 then ext else s.testBit (j + 1)
    rule l m r)
noncomputable def innerNib (tb : S4) (r n0c n1c : Nat) : Nat -> Bool :=
  Nat.rec true (fun v ihv => Bool.rec ihv (Bool.rec false (Bool.rec false ihv (Nat.testBit (g4 tb v) n1c)) (Nat.testBit (g4 tb v) n0c)) (Nat.testBit v r))
noncomputable def chkNibFast (nt : Nib16) (c0 obs : Bool) : Nat -> Bool := Nat.rec true (fun s ih =>
  Bool.rec false
    (Bool.rec true
      (innerNib (getNib nt (Nat.div s k4)) (Nat.mod s k4) (nextCode6 c0 s false) (nextCode6 c0 s true) k16)
      (Bool.beq (Bool.or c0 (Nat.testBit s n0)) obs)) ih)
theorem nib_fast_ok : Bool.and (chkNibFast nib00 false false k64) (Bool.and (chkNibFast nib01 false true k64) (chkNibFast nib11 true true k64)) = true := by decide +kernel

theorem testBit_lor' (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or a b i
theorem testBit_land' (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and a b i
theorem testBit_xor' (a b i : Nat) : (Nat.xor a b).testBit i = xor (a.testBit i) (b.testBit i) := Nat.testBit_xor a b i
theorem testBit_shr' (a b i : Nat) : (Nat.shiftRight a b).testBit i = a.testBit (b + i) := Nat.testBit_shiftRight a
theorem testBit_shl' (a b i : Nat) : (Nat.shiftLeft a b).testBit i = (decide (b ≤ i) && a.testBit (i - b)) := Nat.testBit_shiftLeft a
abbrev leftWord := Rule30LeftRichness.leftWord
/-! ### 3. Formal `≤ 4 * n` Left-Word Poverty Barrier for Rules 90, 150, and 210 -/
def rLeftWord (g : Bool -> Bool -> Bool) (t n : Nat) : List Bool :=
  (List.range n).map fun k => run g t (-((k + 1 : Nat) : Int))
theorem sym90 (a b c : Bool) : xor a (g90 b c) = xor c (g90 b a) := by cases a <;> cases c <;> rfl
theorem sym150 (a b c : Bool) : xor a (g150 b c) = xor c (g150 b a) := by cases a <;> cases b <;> cases c <;> rfl
theorem run90_gt {t : Nat} {p : Int} (h : (t : Int) < p) : run g90 t p = false := by
  rw [← run_symm g90 sym90 t p]; exact run_eq_false_of_lt g90 rfl t (-p) (by omega)
theorem run150_gt {t : Nat} {p : Int} (h : (t : Int) < p) : run g150 t p = false := by
  rw [← run_symm g150 sym150 t p]; exact run_eq_false_of_lt g150 rfl t (-p) (by omega)
theorem run90_step2m : ∀ (m t : Nat) (p : Int),
    run g90 (t + 2 ^ m) p = xor (run g90 t (p - (2 ^ m : Nat))) (run g90 t (p + (2 ^ m : Nat)))
  | 0, t, p => rfl
  | m + 1, t, p => by
    rw [Nat.pow_succ, show t + 2 ^ m * 2 = (t + 2 ^ m) + 2 ^ m by omega, run90_step2m m (t + 2 ^ m) p, run90_step2m m t, run90_step2m m t]
    rw [show p - (2 ^ m : Nat) - (2 ^ m : Nat) = p - ((2 ^ m * 2 : Nat) : Int) by omega,
        show p - (2 ^ m : Nat) + (2 ^ m : Nat) = p by omega,
        show p + (2 ^ m : Nat) - (2 ^ m : Nat) = p by omega,
        show p + (2 ^ m : Nat) + (2 ^ m : Nat) = p + ((2 ^ m * 2 : Nat) : Int) by omega]
    cases run g90 t (p - ((2 ^ m * 2 : Nat) : Int)) <;> cases run g90 t p <;> cases run g90 t (p + ((2 ^ m * 2 : Nat) : Int)) <;> rfl
theorem run150_step2m : ∀ (m t : Nat) (p : Int),
    run g150 (t + 2 ^ m) p = xor (run g150 t (p - (2 ^ m : Nat))) (xor (run g150 t p) (run g150 t (p + (2 ^ m : Nat))))
  | 0, t, p => by show xor (run g150 t (p - 1)) (xor (run g150 t p) (run g150 t (p + 1))) = _; rfl
  | m + 1, t, p => by
    rw [Nat.pow_succ, show t + 2 ^ m * 2 = (t + 2 ^ m) + 2 ^ m by omega, run150_step2m m (t + 2 ^ m) p, run150_step2m m t, run150_step2m m t, run150_step2m m t]
    rw [show p - (2 ^ m : Nat) - (2 ^ m : Nat) = p - ((2 ^ m * 2 : Nat) : Int) by omega,
        show p - (2 ^ m : Nat) + (2 ^ m : Nat) = p by omega,
        show p + (2 ^ m : Nat) - (2 ^ m : Nat) = p by omega,
        show p + (2 ^ m : Nat) + (2 ^ m : Nat) = p + ((2 ^ m * 2 : Nat) : Int) by omega]
    cases run g150 t (p - ((2 ^ m * 2 : Nat) : Int)) <;> cases run g150 t (p - (2 ^ m : Nat)) <;>
      cases run g150 t p <;> cases run g150 t (p + (2 ^ m : Nat)) <;>
      cases run g150 t (p + ((2 ^ m * 2 : Nat) : Int)) <;> rfl
def ceilLog2 (n : Nat) : Nat := if n ≤ 1 then 1 else 1 + ceilLog2 (n / 2)
theorem pow_ceilLog2 (n : Nat) (hn : 1 ≤ n) : n < 2 ^ ceilLog2 n ∧ 2 ^ ceilLog2 n ≤ 2 * n := by
  induction n using Nat.strongRecOn with | ind n ih =>
  by_cases h1 : n ≤ 1
  · have heq : n = 1 := by omega
    rw [heq]
    unfold ceilLog2
    decide
  · unfold ceilLog2
    rw [ite_eq_right h1, Nat.pow_add, Nat.pow_one]
    have ⟨hlo, hhi⟩ := ih (n / 2) (by omega) (by omega)
    omega
theorem highest_pow2_aux : ∀ (fuel m t : Nat), 2 ^ m ≤ t → t - 2 ^ m ≤ fuel → ∃ m' r, m ≤ m' ∧ r < 2 ^ m' ∧ t = r + 2 ^ m'
  | 0, m, t, hge, hfuel => ⟨m, 0, Nat.le_refl _, Nat.two_pow_pos m, by omega⟩
  | fuel + 1, m, t, hge, hfuel => by
    by_cases hlt : t < 2 ^ (m + 1)
    · refine ⟨m, t - 2 ^ m, Nat.le_refl _, ?_, by omega⟩
      rw [Nat.pow_succ] at hlt
      omega
    · have hp : 0 < 2 ^ m := Nat.two_pow_pos m
      have hge' : 2 ^ (m + 1) ≤ t := by omega
      have h2 : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ _ _
      obtain ⟨m', r, hm', hr, ht⟩ := highest_pow2_aux fuel (m + 1) t hge' (by omega)
      exact ⟨m', r, by omega, hr, ht⟩
theorem fold90 (n : Nat) (hn : 1 ≤ n) : ∀ t, ∃ t', t' < 2 * 2 ^ ceilLog2 n ∧ rLeftWord g90 t n = rLeftWord g90 t' n := by
  intro t; induction t using Nat.strongRecOn with | ind t ih =>
  let k := ceilLog2 n; have ⟨hnk, _⟩ := pow_ceilLog2 n hn
  by_cases hbase : t < 2 * 2 ^ k
  · exact ⟨t, hbase, rfl⟩
  · have hge : 2 ^ (k + 1) ≤ t := by rw [Nat.pow_succ]; omega
    obtain ⟨m, r, hm, hr, ht⟩ := highest_pow2_aux t (k + 1) t hge (by omega)
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm'k : 2 ^ k ≤ 2 ^ m' := Nat.pow_le_pow_right (by omega) (by omega)
    have hpow : 2 ^ (m' + 1) = 2 * 2 ^ m' := by rw [Nat.pow_succ]; omega
    have hp_m : 0 < 2 ^ m' := Nat.two_pow_pos m'
    have hn_lt_m : n < 2 ^ m' := Nat.lt_of_lt_of_le hnk hm'k
    by_cases hcase : r < 2 ^ (m' + 1) - n
    · refine ⟨0, (by have := Nat.two_pow_pos k; omega), ?_⟩
      unfold rLeftWord; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
      rw [ht, run90_step2m (m' + 1) r, run_eq_false_of_lt g90 rfl r (-((j + 1 : Nat) : Int) - (2 ^ (m' + 1) : Nat)) (by omega), run90_gt (t := r) (p := -((j + 1 : Nat) : Int) + (2 ^ (m' + 1) : Nat)) (by omega), run_eq_false_of_lt g90 rfl 0 (-((j + 1 : Nat) : Int)) (by omega)]; rfl
    · let s := r - 2 ^ m'
      have hs_lt : s < 2 ^ m' := by omega
      have hr_eq : r = s + 2 ^ m' := by omega
      obtain ⟨t', ht'_lt, ht'_eq⟩ := ih r (by omega)
      refine ⟨t', ht'_lt, ?_⟩
      rw [← ht'_eq]; unfold rLeftWord; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
      rw [ht, run90_step2m (m' + 1) r, run_eq_false_of_lt g90 rfl r (-((j + 1 : Nat) : Int) - (2 ^ (m' + 1) : Nat)) (by omega), Bool.false_xor]
      rw [hr_eq, run90_step2m m' s, run90_step2m m' s]
      rw [run90_gt (t := s) (p := -((j + 1 : Nat) : Int) + (2 ^ (m' + 1) : Nat) + (2 ^ m' : Nat)) (by omega), Bool.xor_false]
      rw [run_eq_false_of_lt g90 rfl s (-((j + 1 : Nat) : Int) - (2 ^ m' : Nat)) (by omega), Bool.false_xor]
      congr 1; omega
theorem fold150 (n : Nat) (hn : 1 ≤ n) : ∀ t, ∃ t', t' < 2 * 2 ^ ceilLog2 n ∧ rLeftWord g150 t n = rLeftWord g150 t' n := by
  intro t; induction t using Nat.strongRecOn with | ind t ih =>
  let k := ceilLog2 n; have ⟨hnk, _⟩ := pow_ceilLog2 n hn
  by_cases hbase : t < 2 * 2 ^ k
  · exact ⟨t, hbase, rfl⟩
  · have hge : 2 ^ (k + 1) ≤ t := by rw [Nat.pow_succ]; omega
    obtain ⟨m, r, hm, hr, ht⟩ := highest_pow2_aux t (k + 1) t hge (by omega)
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm'k : 2 ^ k ≤ 2 ^ m' := Nat.pow_le_pow_right (by omega) (by omega)
    have hpow : 2 ^ (m' + 1) = 2 * 2 ^ m' := by rw [Nat.pow_succ]; omega
    have hp_m : 0 < 2 ^ m' := Nat.two_pow_pos m'
    have hn_lt_m : n < 2 ^ m' := Nat.lt_of_lt_of_le hnk hm'k
    by_cases hcase : r < 2 ^ (m' + 1) - n
    · obtain ⟨t', ht'_lt, ht'_eq⟩ := ih r (by omega)
      refine ⟨t', ht'_lt, ?_⟩
      rw [← ht'_eq]; unfold rLeftWord; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
      rw [ht, run150_step2m (m' + 1) r, run_eq_false_of_lt g150 rfl r (-((j + 1 : Nat) : Int) - (2 ^ (m' + 1) : Nat)) (by omega), run150_gt (t := r) (p := -((j + 1 : Nat) : Int) + (2 ^ (m' + 1) : Nat)) (by omega), Bool.false_xor, Bool.xor_false]
    · let s := r - 2 ^ m'
      have hs_lt : s < 2 ^ m' := by omega
      have hr_eq : r = s + 2 ^ m' := by omega
      obtain ⟨t', ht'_lt, ht'_eq⟩ := ih s (by omega)
      refine ⟨t', ht'_lt, ?_⟩
      rw [← ht'_eq]; unfold rLeftWord; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
      rw [ht, run150_step2m (m' + 1) r, run_eq_false_of_lt g150 rfl r (-((j + 1 : Nat) : Int) - (2 ^ (m' + 1) : Nat)) (by omega), Bool.false_xor]
      rw [hr_eq, run150_step2m m' s, run150_step2m m' s, run_eq_false_of_lt g150 rfl s (-((j + 1 : Nat) : Int) - (2 ^ m' : Nat)) (by omega), Bool.false_xor]
      rw [run150_gt (t := s) (p := -((j + 1 : Nat) : Int) + (2 ^ (m' + 1) : Nat)) (by omega)]
      rw [run150_gt (t := s) (p := -((j + 1 : Nat) : Int) + (2 ^ (m' + 1) : Nat) + (2 ^ m' : Nat)) (by omega)]
      rw [show -((j + 1 : Nat) : Int) + ((2 ^ (m' + 1) : Nat) : Int) - ((2 ^ m' : Nat) : Int) = -((j + 1 : Nat) : Int) + ((2 ^ m' : Nat) : Int) by omega]
      cases run g150 s (-((j + 1 : Nat) : Int)) <;> cases run g150 s (-((j + 1 : Nat) : Int) + (2 ^ m' : Nat)) <;> rfl
theorem rLeftWord_210_eq_90 (t n : Nat) : rLeftWord g210 t n = rLeftWord g90 t n := by
  unfold rLeftWord; apply List.map_congr_left; intro j _; exact (run210_eq t (-((j + 1 : Nat) : Int))).1
theorem nodup_le_of_fold {g : Bool -> Bool -> Bool} {n B : Nat}
    (hfold : ∀ t, ∃ t', t' < B ∧ rLeftWord g t n = rLeftWord g t' n)
    (ts : List Nat) (hnd : (ts.map (fun t => rLeftWord g t n)).Nodup) : ts.length ≤ B := by
  have hsub : ts.map (fun t => rLeftWord g t n) ⊆ (List.range B).map (fun t => rLeftWord g t n) := by
    intro w hw; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hw; obtain ⟨t', ht', heq⟩ := hfold t
    exact List.mem_map.mpr ⟨t', List.mem_range.mpr ht', heq.symm⟩
  calc ts.length = (ts.map (fun t => rLeftWord g t n)).length := (List.length_map _).symm
    _ ≤ ((List.range B).map (fun t => rLeftWord g t n)).length := length_le_of_subset hnd hsub
    _ = B := by rw [List.length_map, List.length_range]
theorem rule90_leftWords_le_4n {n : Nat} (hn : 1 ≤ n) (ts : List Nat)
    (hnd : (ts.map (fun t => rLeftWord g90 t n)).Nodup) : ts.length ≤ 4 * n := by
  have h := nodup_le_of_fold (fold90 n hn) ts hnd; have ⟨_, hhi⟩ := pow_ceilLog2 n hn; omega
theorem rule150_leftWords_le_4n {n : Nat} (hn : 1 ≤ n) (ts : List Nat)
    (hnd : (ts.map (fun t => rLeftWord g150 t n)).Nodup) : ts.length ≤ 4 * n := by
  have h := nodup_le_of_fold (fold150 n hn) ts hnd; have ⟨_, hhi⟩ := pow_ceilLog2 n hn; omega
theorem rule210_leftWords_le_4n {n : Nat} (hn : 1 ≤ n) (ts : List Nat)
    (hnd : (ts.map (fun t => rLeftWord g210 t n)).Nodup) : ts.length ≤ 4 * n := by
  have heq : ts.map (fun t => rLeftWord g210 t n) = ts.map (fun t => rLeftWord g90 t n) := by
    apply List.map_congr_left; intro t _; exact rLeftWord_210_eq_90 t n
  rw [heq] at hnd; exact rule90_leftWords_le_4n hn ts hnd

/-! ### 4. Formal Soundness Bridge: 6-Cell Strip Cover, SIMD Block Bound, and Problem 1 -/
theorem bool_rec_eq_ite {α : Type} (f t : α) (c : Bool) : Bool.rec f t c = (if c then t else f) := by cases c <;> rfl
theorem bool_rec_false_eq {b c : Bool} (h : Bool.rec false b c = true) : c = true ∧ b = true := by cases c <;> cases b <;> simp at h ⊢
theorem beq_n0_false_of_ne {x : Nat} (h : x ≠ 0) : Nat.beq x n0 = false := by
  cases hb : Nat.beq x n0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h
theorem g1_mp1 (f : Nat -> Nat) (r : S1) (i : Nat) : g1 (mp1 f r) i = mp0 f (g1 r i) := by unfold g1 mp1; cases Nat.testBit i b0 <;> rfl
theorem g2_mp2 (f : Nat -> Nat) (r : S2) (i : Nat) : g2 (mp2 f r) i = mp0 f (g2 r i) := by unfold g2 mp2; cases Nat.testBit i b1 <;> simp [g1_mp1]
theorem g3_mp3 (f : Nat -> Nat) (r : S3) (i : Nat) : g3 (mp3 f r) i = mp0 f (g3 r i) := by unfold g3 mp3; cases Nat.testBit i b2 <;> simp [g2_mp2]
theorem g4_mp4 (f : Nat -> Nat) (r : S4) (i : Nat) : g4 (mp4 f r) i = mp0 f (g4 r i) := by unfold g4 mp4; cases Nat.testBit i b3 <;> simp [g3_mp3]
theorem g5_mp5 (f : Nat -> Nat) (r : S5) (i : Nat) : g5 (mp5 f r) i = mp0 f (g5 r i) := by unfold g5 mp5; cases Nat.testBit i b4 <;> simp [g4_mp4]
theorem g6_mp6 (f : Nat -> Nat) (r : S6) (i : Nat) : g6 (mp6 f r) i = mp0 f (g6 r i) := by unfold g6 mp6; cases Nat.testBit i b5 <;> simp [g5_mp5]
theorem g7_mp7 (f : Nat -> Nat) (r : S7) (i : Nat) : g7 (mp7 f r) i = mp0 f (g7 r i) := by unfold g7 mp7; cases Nat.testBit i b6 <;> simp [g6_mp6]
theorem g8_mp8 (f : Nat -> Nat) (r : S8) (i : Nat) : g8 (mp8 f r) i = mp0 f (g8 r i) := by unfold g8 mp8; cases Nat.testBit i b7 <;> simp [g7_mp7]
theorem g9_mp9 (f : Nat -> Nat) (r : S9) (i : Nat) : g9 (mp9 f r) i = mp0 f (g9 r i) := by unfold g9 mp9; cases Nat.testBit i b8 <;> simp [g8_mp8]
theorem g10_mp10 (f : Nat -> Nat) (r : S10) (i : Nat) : g10 (mp10 f r) i = mp0 f (g10 r i) := by unfold g10 mp10; cases Nat.testBit i b9 <;> simp [g9_mp9]
theorem g11_mp11 (f : Nat -> Nat) (r : S11) (i : Nat) : g11 (mp11 f r) i = mp0 f (g11 r i) := by unfold g11 mp11; cases Nat.testBit i b10 <;> simp [g10_mp10]
theorem g12_mp12 (f : Nat -> Nat) (r : S12) (i : Nat) : g12 (mp12 f r) i = mp0 f (g12 r i) := by unfold g12 mp12; cases Nat.testBit i b11 <;> simp [g11_mp11]
theorem al1_spec (f : Nat -> Nat -> Bool) (r v : S1) (h : al1 f r v = true) (i : Nat) : al0 f (g1 r i) (g1 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g1; cases Nat.testBit i b0 <;> assumption
theorem al2_spec (f : Nat -> Nat -> Bool) (r v : S2) (h : al2 f r v = true) (i : Nat) : al0 f (g2 r i) (g2 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g2; cases Nat.testBit i b1
  · exact al1_spec f r.a v.a ha i
  · exact al1_spec f r.b v.b hb i
theorem al3_spec (f : Nat -> Nat -> Bool) (r v : S3) (h : al3 f r v = true) (i : Nat) : al0 f (g3 r i) (g3 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g3; cases Nat.testBit i b2
  · exact al2_spec f r.a v.a ha i
  · exact al2_spec f r.b v.b hb i
theorem al4_spec (f : Nat -> Nat -> Bool) (r v : S4) (h : al4 f r v = true) (i : Nat) : al0 f (g4 r i) (g4 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g4; cases Nat.testBit i b3
  · exact al3_spec f r.a v.a ha i
  · exact al3_spec f r.b v.b hb i
theorem al5_spec (f : Nat -> Nat -> Bool) (r v : S5) (h : al5 f r v = true) (i : Nat) : al0 f (g5 r i) (g5 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g5; cases Nat.testBit i b4
  · exact al4_spec f r.a v.a ha i
  · exact al4_spec f r.b v.b hb i
theorem al6_spec (f : Nat -> Nat -> Bool) (r v : S6) (h : al6 f r v = true) (i : Nat) : al0 f (g6 r i) (g6 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g6; cases Nat.testBit i b5
  · exact al5_spec f r.a v.a ha i
  · exact al5_spec f r.b v.b hb i
theorem al7_spec (f : Nat -> Nat -> Bool) (r v : S7) (h : al7 f r v = true) (i : Nat) : al0 f (g7 r i) (g7 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g7; cases Nat.testBit i b6
  · exact al6_spec f r.a v.a ha i
  · exact al6_spec f r.b v.b hb i
theorem al8_spec (f : Nat -> Nat -> Bool) (r v : S8) (h : al8 f r v = true) (i : Nat) : al0 f (g8 r i) (g8 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g8; cases Nat.testBit i b7
  · exact al7_spec f r.a v.a ha i
  · exact al7_spec f r.b v.b hb i
theorem al9_spec (f : Nat -> Nat -> Bool) (r v : S9) (h : al9 f r v = true) (i : Nat) : al0 f (g9 r i) (g9 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g9; cases Nat.testBit i b8
  · exact al8_spec f r.a v.a ha i
  · exact al8_spec f r.b v.b hb i
theorem al10_spec (f : Nat -> Nat -> Bool) (r v : S10) (h : al10 f r v = true) (i : Nat) : al0 f (g10 r i) (g10 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g10; cases Nat.testBit i b9
  · exact al9_spec f r.a v.a ha i
  · exact al9_spec f r.b v.b hb i
theorem al11_spec (f : Nat -> Nat -> Bool) (r v : S11) (h : al11 f r v = true) (i : Nat) : al0 f (g11 r i) (g11 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g11; cases Nat.testBit i b10
  · exact al10_spec f r.a v.a ha i
  · exact al10_spec f r.b v.b hb i
theorem al12_spec (f : Nat -> Nat -> Bool) (r v : S12) (h : al12 f r v = true) (i : Nat) : al0 f (g12 r i) (g12 v i) = true := by
  obtain ⟨ha, hb⟩ := bool_rec_false_eq h; unfold g12; cases Nat.testBit i b11
  · exact al11_spec f r.a v.a ha i
  · exact al11_spec f r.b v.b hb i
def BitBounded (B x : Nat) : Prop := ∀ j, B ≤ j → x.testBit j = false
def MaskIs (B m : Nat) : Prop := ∀ j, m.testBit j = decide (j < B)
theorem vm0_mask : MaskIs vsh0 vm0 := by intro j; rw [show vm0 = 2 ^ vsh0 - 1 by decide +kernel]; exact Nat.testBit_two_pow_sub_one vsh0 j
theorem mask_double {B m : Nat} (hm : MaskIs B m) : MaskIs (2 * B) (Nat.lor m (Nat.shiftLeft m B)) := by
  intro j; rw [testBit_lor', testBit_shl', hm, hm]
  by_cases h1 : j < B
  · have h2 : j < 2 * B := (by omega); simp [h1, h2]
  · have hge : B ≤ j := by omega
    by_cases h2 : j - B < B
    · have h3 : j < 2 * B := (by omega); simp [h1, hge, h2, h3]
    · have h3 : ¬ j < 2 * B := (by omega); simp [h1, hge, h2, h3]
theorem m0_spec : MaskIs vsh0 theMasks.m0 := vm0_mask
theorem m1_spec : MaskIs vsh1 theMasks.m1 := by rw [show vsh1 = 2 * vsh0 by decide]; exact mask_double m0_spec
theorem m2_spec : MaskIs vsh2 theMasks.m2 := by rw [show vsh2 = 2 * vsh1 by decide]; exact mask_double m1_spec
theorem m3_spec : MaskIs vsh3 theMasks.m3 := by rw [show vsh3 = 2 * vsh2 by decide]; exact mask_double m2_spec
theorem m4_spec : MaskIs vsh4 theMasks.m4 := by rw [show vsh4 = 2 * vsh3 by decide]; exact mask_double m3_spec
theorem m5_spec : MaskIs vsh5 theMasks.m5 := by rw [show vsh5 = 2 * vsh4 by decide]; exact mask_double m4_spec
theorem m6_spec : MaskIs vsh6 theMasks.m6 := by rw [show vsh6 = 2 * vsh5 by decide]; exact mask_double m5_spec
theorem m7_spec : MaskIs vsh7 theMasks.m7 := by rw [show vsh7 = 2 * vsh6 by decide]; exact mask_double m6_spec
theorem m8_spec : MaskIs vsh8 theMasks.m8 := by rw [show vsh8 = 2 * vsh7 by decide]; exact mask_double m7_spec
theorem m9_spec : MaskIs vsh9 theMasks.m9 := by rw [show vsh9 = 2 * vsh8 by decide]; exact mask_double m8_spec
theorem m10_spec : MaskIs vsh10 theMasks.m10 := by rw [show vsh10 = 2 * vsh9 by decide]; exact mask_double m9_spec
theorem m11_spec : MaskIs vsh11 theMasks.m11 := by rw [show vsh11 = 2 * vsh10 by decide]; exact mask_double m10_spec
theorem land_mask_bounded {B m : Nat} (hm : MaskIs B m) (x : Nat) : BitBounded B (Nat.land x m) := by
  intro j hj; rw [testBit_land', hm]; have hlt : ¬ j < B := (by omega); simp [hlt]
theorem lor_shift_bounded {B a b : Nat} (ha : BitBounded B a) (hb : BitBounded B b) : BitBounded (2 * B) (Nat.lor a (Nat.shiftLeft b B)) := by
  intro j hj; rw [testBit_lor', testBit_shl', ha j (by omega), hb (j - B) (by omega)]; simp
theorem land_lor_shift {B m a b : Nat} (hm : MaskIs B m) (ha : BitBounded B a) : Nat.land (Nat.lor a (Nat.shiftLeft b B)) m = a := by
  apply Nat.eq_of_testBit_eq; intro j; rw [testBit_land', testBit_lor', testBit_shl', hm]
  by_cases hj : j < B
  · have hge : ¬ B ≤ j := (by omega); simp [hj, hge]
  · simp [hj, ha j (by omega)]
theorem land_self_of_bounded {B m a : Nat} (hm : MaskIs B m) (ha : BitBounded B a) : Nat.land a m = a := by
  apply Nat.eq_of_testBit_eq; intro j; rw [testBit_land', hm]; by_cases hj : j < B
  · simp [hj]
  · simp [hj, ha j (by omega)]
theorem shr_lor_shift {B a b : Nat} (ha : BitBounded B a) : Nat.shiftRight (Nat.lor a (Nat.shiftLeft b B)) B = b := by
  apply Nat.eq_of_testBit_eq; intro j; rw [testBit_shr', testBit_lor', testBit_shl']
  rw [ha (B + j) (by omega)]; have hge : B ≤ B + j := (by omega); have hsub : B + j - B = j := (by omega); simp [hge, hsub]
def Wf1 (t : S1) : Prop := BitBounded vsh0 t.a ∧ BitBounded vsh0 t.b
def Wf2 (t : S2) : Prop := Wf1 t.a ∧ Wf1 t.b
def Wf3 (t : S3) : Prop := Wf2 t.a ∧ Wf2 t.b
def Wf4 (t : S4) : Prop := Wf3 t.a ∧ Wf3 t.b
def Wf5 (t : S5) : Prop := Wf4 t.a ∧ Wf4 t.b
def Wf6 (t : S6) : Prop := Wf5 t.a ∧ Wf5 t.b
def Wf7 (t : S7) : Prop := Wf6 t.a ∧ Wf6 t.b
def Wf8 (t : S8) : Prop := Wf7 t.a ∧ Wf7 t.b
def Wf9 (t : S9) : Prop := Wf8 t.a ∧ Wf8 t.b
def Wf10 (t : S10) : Prop := Wf9 t.a ∧ Wf9 t.b
def Wf11 (t : S11) : Prop := Wf10 t.a ∧ Wf10 t.b
def Wf12 (t : S12) : Prop := Wf11 t.a ∧ Wf11 t.b
theorem pv1_bdd {t : S1} (ht : Wf1 t) : BitBounded vsh1 (pv1 t) := by rw [show vsh1 = 2 * vsh0 by decide]; exact lor_shift_bounded ht.1 ht.2
theorem pv2_bdd {t : S2} (ht : Wf2 t) : BitBounded vsh2 (pv2 t) := by rw [show vsh2 = 2 * vsh1 by decide]; exact lor_shift_bounded (pv1_bdd ht.1) (pv1_bdd ht.2)
theorem pv3_bdd {t : S3} (ht : Wf3 t) : BitBounded vsh3 (pv3 t) := by rw [show vsh3 = 2 * vsh2 by decide]; exact lor_shift_bounded (pv2_bdd ht.1) (pv2_bdd ht.2)
theorem pv4_bdd {t : S4} (ht : Wf4 t) : BitBounded vsh4 (pv4 t) := by rw [show vsh4 = 2 * vsh3 by decide]; exact lor_shift_bounded (pv3_bdd ht.1) (pv3_bdd ht.2)
theorem pv5_bdd {t : S5} (ht : Wf5 t) : BitBounded vsh5 (pv5 t) := by rw [show vsh5 = 2 * vsh4 by decide]; exact lor_shift_bounded (pv4_bdd ht.1) (pv4_bdd ht.2)
theorem pv6_bdd {t : S6} (ht : Wf6 t) : BitBounded vsh6 (pv6 t) := by rw [show vsh6 = 2 * vsh5 by decide]; exact lor_shift_bounded (pv5_bdd ht.1) (pv5_bdd ht.2)
theorem pv7_bdd {t : S7} (ht : Wf7 t) : BitBounded vsh7 (pv7 t) := by rw [show vsh7 = 2 * vsh6 by decide]; exact lor_shift_bounded (pv6_bdd ht.1) (pv6_bdd ht.2)
theorem pv8_bdd {t : S8} (ht : Wf8 t) : BitBounded vsh8 (pv8 t) := by rw [show vsh8 = 2 * vsh7 by decide]; exact lor_shift_bounded (pv7_bdd ht.1) (pv7_bdd ht.2)
theorem pv9_bdd {t : S9} (ht : Wf9 t) : BitBounded vsh9 (pv9 t) := by rw [show vsh9 = 2 * vsh8 by decide]; exact lor_shift_bounded (pv8_bdd ht.1) (pv8_bdd ht.2)
theorem pv10_bdd {t : S10} (ht : Wf10 t) : BitBounded vsh10 (pv10 t) := by rw [show vsh10 = 2 * vsh9 by decide]; exact lor_shift_bounded (pv9_bdd ht.1) (pv9_bdd ht.2)
theorem pv11_bdd {t : S11} (ht : Wf11 t) : BitBounded vsh11 (pv11 t) := by rw [show vsh11 = 2 * vsh10 by decide]; exact lor_shift_bounded (pv10_bdd ht.1) (pv10_bdd ht.2)
theorem uv1_pv1 {t : S1} (ht : Wf1 t) : uv1 theMasks (pv1 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv1 pv1
  congr 1
  · exact land_lor_shift m0_spec ha
  · rw [shr_lor_shift ha]; exact land_self_of_bounded m0_spec hb
theorem uv2_pv2 {t : S2} (ht : Wf2 t) : uv2 theMasks (pv2 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv2 pv2
  congr 1
  · rw [land_lor_shift m1_spec (pv1_bdd ha)]; exact uv1_pv1 ha
  · rw [shr_lor_shift (pv1_bdd ha)]; exact uv1_pv1 hb
theorem uv3_pv3 {t : S3} (ht : Wf3 t) : uv3 theMasks (pv3 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv3 pv3
  congr 1
  · rw [land_lor_shift m2_spec (pv2_bdd ha)]; exact uv2_pv2 ha
  · rw [shr_lor_shift (pv2_bdd ha)]; exact uv2_pv2 hb
theorem uv4_pv4 {t : S4} (ht : Wf4 t) : uv4 theMasks (pv4 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv4 pv4
  congr 1
  · rw [land_lor_shift m3_spec (pv3_bdd ha)]; exact uv3_pv3 ha
  · rw [shr_lor_shift (pv3_bdd ha)]; exact uv3_pv3 hb
theorem uv5_pv5 {t : S5} (ht : Wf5 t) : uv5 theMasks (pv5 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv5 pv5
  congr 1
  · rw [land_lor_shift m4_spec (pv4_bdd ha)]; exact uv4_pv4 ha
  · rw [shr_lor_shift (pv4_bdd ha)]; exact uv4_pv4 hb
theorem uv6_pv6 {t : S6} (ht : Wf6 t) : uv6 theMasks (pv6 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv6 pv6
  congr 1
  · rw [land_lor_shift m5_spec (pv5_bdd ha)]; exact uv5_pv5 ha
  · rw [shr_lor_shift (pv5_bdd ha)]; exact uv5_pv5 hb
theorem uv7_pv7 {t : S7} (ht : Wf7 t) : uv7 theMasks (pv7 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv7 pv7
  congr 1
  · rw [land_lor_shift m6_spec (pv6_bdd ha)]; exact uv6_pv6 ha
  · rw [shr_lor_shift (pv6_bdd ha)]; exact uv6_pv6 hb
theorem uv8_pv8 {t : S8} (ht : Wf8 t) : uv8 theMasks (pv8 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv8 pv8
  congr 1
  · rw [land_lor_shift m7_spec (pv7_bdd ha)]; exact uv7_pv7 ha
  · rw [shr_lor_shift (pv7_bdd ha)]; exact uv7_pv7 hb
theorem uv9_pv9 {t : S9} (ht : Wf9 t) : uv9 theMasks (pv9 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv9 pv9
  congr 1
  · rw [land_lor_shift m8_spec (pv8_bdd ha)]; exact uv8_pv8 ha
  · rw [shr_lor_shift (pv8_bdd ha)]; exact uv8_pv8 hb
theorem uv10_pv10 {t : S10} (ht : Wf10 t) : uv10 theMasks (pv10 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv10 pv10
  congr 1
  · rw [land_lor_shift m9_spec (pv9_bdd ha)]; exact uv9_pv9 ha
  · rw [shr_lor_shift (pv9_bdd ha)]; exact uv9_pv9 hb
theorem uv11_pv11 {t : S11} (ht : Wf11 t) : uv11 theMasks (pv11 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv11 pv11
  congr 1
  · rw [land_lor_shift m10_spec (pv10_bdd ha)]; exact uv10_pv10 ha
  · rw [shr_lor_shift (pv10_bdd ha)]; exact uv10_pv10 hb
theorem uv12_pv12 {t : S12} (ht : Wf12 t) : uv12 theMasks (pv12 t) = t := by
  rcases t with ⟨a, b⟩; rcases ht with ⟨ha, hb⟩; unfold uv12 pv12
  congr 1
  · rw [land_lor_shift m11_spec (pv11_bdd ha)]; exact uv11_pv11 ha
  · rw [shr_lor_shift (pv11_bdd ha)]; exact uv11_pv11 hb
theorem mp0_bdd (f : Nat -> Nat) (r : Nat) : BitBounded vsh0 (mp0 f r) := by
  unfold mp0; rw [bool_rec_eq_ite]; split
  · intro j _; exact Nat.zero_testBit j
  · exact land_mask_bounded vm0_mask (f r)
theorem mp1_wf (f : Nat -> Nat) (r : S1) : Wf1 (mp1 f r) := ⟨mp0_bdd f r.a, mp0_bdd f r.b⟩
theorem mp2_wf (f : Nat -> Nat) (r : S2) : Wf2 (mp2 f r) := ⟨mp1_wf f r.a, mp1_wf f r.b⟩
theorem mp3_wf (f : Nat -> Nat) (r : S3) : Wf3 (mp3 f r) := ⟨mp2_wf f r.a, mp2_wf f r.b⟩
theorem mp4_wf (f : Nat -> Nat) (r : S4) : Wf4 (mp4 f r) := ⟨mp3_wf f r.a, mp3_wf f r.b⟩
theorem mp5_wf (f : Nat -> Nat) (r : S5) : Wf5 (mp5 f r) := ⟨mp4_wf f r.a, mp4_wf f r.b⟩
theorem mp6_wf (f : Nat -> Nat) (r : S6) : Wf6 (mp6 f r) := ⟨mp5_wf f r.a, mp5_wf f r.b⟩
theorem mp7_wf (f : Nat -> Nat) (r : S7) : Wf7 (mp7 f r) := ⟨mp6_wf f r.a, mp6_wf f r.b⟩
theorem mp8_wf (f : Nat -> Nat) (r : S8) : Wf8 (mp8 f r) := ⟨mp7_wf f r.a, mp7_wf f r.b⟩
theorem mp9_wf (f : Nat -> Nat) (r : S9) : Wf9 (mp9 f r) := ⟨mp8_wf f r.a, mp8_wf f r.b⟩
theorem mp10_wf (f : Nat -> Nat) (r : S10) : Wf10 (mp10 f r) := ⟨mp9_wf f r.a, mp9_wf f r.b⟩
theorem mp11_wf (f : Nat -> Nat) (r : S11) : Wf11 (mp11 f r) := ⟨mp10_wf f r.a, mp10_wf f r.b⟩
theorem mp12_wf (f : Nat -> Nat) (r : S12) : Wf12 (mp12 f r) := ⟨mp11_wf f r.a, mp11_wf f r.b⟩

-- 4A. 6-Cell Right Strip Dynamics & Nibble Cover Soundness:
def rStrip6 (x : Int -> Bool) (t : Nat) : Nat := code6 (fun j => evol x t ((j : Int) + 1))
theorem code6_lt (f : Nat -> Bool) : code6 f < 64 := by
  unfold code6; cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> cases f 5 <;> decide
theorem code6_testBit (f : Nat -> Bool) (j : Nat) (hj : j < 6) : (code6 f).testBit j = f j := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold code6; cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> cases f 5 <;> decide)
theorem code6_congr {f g : Nat -> Bool} (h : ∀ j, j < 6 → f j = g j) : code6 f = code6 g := by
  unfold code6; rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide)]
theorem rStrip6_succ (x : Int -> Bool) (t : Nat) : rStrip6 x (t + 1) = nextCode6 (evol x t 0) (rStrip6 x t) (evol x t 7) := by
  unfold rStrip6 nextCode6; apply code6_congr; intro j hj; rw [evol_succ]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only [↓reduceIte]; rw [code6_testBit _ 0 (by decide), code6_testBit _ 1 (by decide)]; congr 1
  · dsimp only [↓reduceIte]; rw [code6_testBit _ 0 (by decide), code6_testBit _ 1 (by decide), code6_testBit _ 2 (by decide)]; congr 1
  · dsimp only [↓reduceIte]; rw [code6_testBit _ 1 (by decide), code6_testBit _ 2 (by decide), code6_testBit _ 3 (by decide)]; congr 1
  · dsimp only [↓reduceIte]; rw [code6_testBit _ 2 (by decide), code6_testBit _ 3 (by decide), code6_testBit _ 4 (by decide)]; congr 1
  · dsimp only [↓reduceIte]; rw [code6_testBit _ 3 (by decide), code6_testBit _ 4 (by decide), code6_testBit _ 5 (by decide)]; congr 1
  · dsimp only [↓reduceIte]; rw [code6_testBit _ 4 (by decide), code6_testBit _ 5 (by decide)]; congr 1
theorem nibLoop_mem (nt : Nib16) (m : Nat) : ∀ J j b, j < J →
    (g4 (getNib nt j) (Nat.land (Nat.shiftRight m (Nat.mul k4 j)) k15)).testBit b = true → (nibLoop nt m J).testBit b = true
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | J + 1, j, b, hj, hb => by
    change (Nat.lor (nibLoop nt m J) (g4 (getNib nt J) (Nat.land (Nat.shiftRight m (Nat.mul k4 J)) k15))).testBit b = true
    rw [testBit_lor']
    by_cases hjeq : j = J
    · subst hjeq; rw [hb, Bool.or_true]
    · rw [nibLoop_mem nt m J j b (by omega) hb, Bool.true_or]
theorem innerNib_spec (tb : S4) (r n0c n1c : Nat) : ∀ V v, v < V → innerNib tb r n0c n1c V = true →
    v.testBit r = true → (g4 tb v).testBit n0c = true ∧ (g4 tb v).testBit n1c = true
  | 0, _, hv, _, _ => absurd hv (Nat.not_lt_zero _)
  | V + 1, v, hv, h, hvr => by
    change Bool.rec (innerNib tb r n0c n1c V) (Bool.rec false (Bool.rec false (innerNib tb r n0c n1c V) ((g4 tb V).testBit n1c)) ((g4 tb V).testBit n0c)) (V.testBit r) = true at h
    by_cases hveq : v = V
    · subst hveq; rw [hvr] at h; dsimp only at h
      obtain ⟨hc0, h'⟩ := bool_rec_false_eq h; obtain ⟨hc1, _⟩ := bool_rec_false_eq h'; exact ⟨hc0, hc1⟩
    · cases hVr : V.testBit r <;> rw [hVr] at h <;> dsimp only at h
      · exact innerNib_spec tb r n0c n1c V v (by omega) h hvr
      · obtain ⟨_, h'⟩ := bool_rec_false_eq h; obtain ⟨_, h''⟩ := bool_rec_false_eq h'
        exact innerNib_spec tb r n0c n1c V v (by omega) h'' hvr
theorem chkNibFast_spec (nt : Nib16) (c0 obs : Bool) : ∀ S s, s < S → chkNibFast nt c0 obs S = true →
    (c0 || s.testBit 0) = obs → ∀ v, v < 16 → v.testBit (s % 4) = true → ∀ ext,
    (g4 (getNib nt (s / 4)) v).testBit (nextCode6 c0 s ext) = true
  | 0, _, hs, _, _, _, _, _, _ => absurd hs (Nat.not_lt_zero _)
  | S + 1, s, hs, h, hobs, v, hv, hvr, ext => by
    change Bool.rec false (Bool.rec true (innerNib (getNib nt (S / 4)) (S % 4) (nextCode6 c0 S false) (nextCode6 c0 S true) 16) (Bool.beq (c0 || S.testBit 0) obs)) (chkNibFast nt c0 obs S) = true at h
    obtain ⟨hprev, hcur⟩ := bool_rec_false_eq h
    by_cases hseq : s = S
    · subst hseq; have hbb : Bool.beq obs obs = true := by cases obs <;> rfl
      rw [hobs, hbb] at hcur; dsimp only at hcur
      obtain ⟨e0, e1⟩ := innerNib_spec _ _ _ _ 16 v hv hcur hvr; cases ext <;> assumption
    · exact chkNibFast_spec nt c0 obs S s (by omega) hprev hobs v hv hvr ext
theorem nibLoop_step_sound {nt : Nib16} {c0 obs : Bool} (hnib : chkNibFast nt c0 obs k64 = true)
    {m s : Nat} (hs : s < 64) (hms : m.testBit s = true) (hobs : (c0 || s.testBit 0) = obs) (ext : Bool) :
    (nibLoop nt m k16).testBit (nextCode6 c0 s ext) = true := by
  let j := s / 4
  let v := Nat.land (Nat.shiftRight m (Nat.mul k4 j)) k15
  have hj : j < 16 := by omega
  have hv_lt : v < 16 := by
    change ((m >>> (4 * j)) &&& (2 ^ 4 - 1)) < 16
    rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by decide)
  have hvr : v.testBit (s % 4) = true := by
    change (Nat.land (Nat.shiftRight m (4 * j)) (2 ^ 4 - 1)).testBit (s % 4) = true
    rw [testBit_land', Nat.testBit_two_pow_sub_one, testBit_shr']
    have hmod : s % 4 < 4 := by omega
    rw [decide_eq_true hmod, Bool.and_true, show 4 * j + s % 4 = s by omega, hms]
  have hstep := chkNibFast_spec nt c0 obs 64 s hs hnib hobs v hv_lt hvr ext
  exact nibLoop_mem nt m 16 j _ hj hstep

noncomputable def recOf (q : Nat) : Nat := g12 rsTree q
noncomputable def maskOf (q : Nat) : Nat := g12 msTree q
noncomputable def e00 (q : Nat) : Nat := Nat.land (recOf q) m13
noncomputable def e01 (q : Nat) : Nat := Nat.land (Nat.shiftRight (recOf q) k13) m13
noncomputable def e11 (q : Nat) : Nat := Nat.land (Nat.shiftRight (recOf q) k26) m13
noncomputable def wRaw (q : Nat) : Nat := Nat.land (Nat.shiftRight (recOf q) k39) m13
noncomputable def wOf (q : Nat) : Nat := if q < kM then wRaw q else 0
theorem allActive_spec : ∀ Q q, q < Q → allActive rsTree Q = true → recOf q ≠ 0
  | 0, _, hq, _ => absurd hq (Nat.not_lt_zero _)
  | Q + 1, q, hq, h => by
    change Bool.rec false (Bool.rec true false (Nat.beq (g12 rsTree Q) n0)) (allActive rsTree Q) = true at h
    obtain ⟨hprev, hcur⟩ := bool_rec_false_eq h
    by_cases hqe : q = Q
    · subst hqe; intro hz; change g12 rsTree q = 0 at hz; rw [hz] at hcur; simp [n0] at hcur
    · exact allActive_spec Q q (by omega) hprev
theorem chkEdge_spec {sm q' s' : Nat} (h : chkEdge msTree sm q' = true) (_hle : q' ≤ kM) (hs' : s' < 64) (hbit : sm.testBit s' = true) :
    q' < kM ∧ (maskOf q').testBit s' = true := by
  unfold chkEdge at h
  cases hble : Nat.ble (Nat.add q' k1) kM <;> rw [hble] at h <;> dsimp only at h
  · have hzero : sm = 0 := Nat.eq_of_beq_eq_true h; subst hzero; simp at hbit
  · have hlt : q' < kM := by
      have hle' := Nat.le_of_ble_eq_true hble
      rw [Nat.add_eq] at hle'
      unfold k1 at hle'
      omega
    have hland : Nat.land sm (Nat.xor all64 (maskOf q')) = 0 := Nat.eq_of_beq_eq_true h
    have hb := congrArg (fun z => z.testBit s') hland
    simp only [testBit_land', Nat.zero_testBit, testBit_xor'] at hb
    have hall : all64.testBit s' = true := by rw [show all64 = 2 ^ 64 - 1 by decide, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hs'
    rw [hbit, hall] at hb
    refine ⟨hlt, ?_⟩
    cases hm_bit : (maskOf q').testBit s' <;> rw [hm_bit] at hb <;> revert hb <;> decide
theorem cover_facts :
    maskOf 0 = all64 ∧ wRaw 0 = kw0 ∧ recOf kM = 0 ∧
    ∀ q, q < kM → recOf q ≠ 0 ∧ kwMin ≤ wRaw q ∧ wRaw q ≤ kw0 ∧ e00 q ≤ kM ∧ e01 q ≤ kM ∧ e11 q ≤ kM ∧
      chkEdge msTree (nibLoop nib00 (maskOf q) k16) (e00 q) = true ∧
      chkEdge msTree (nibLoop nib01 (maskOf q) k16) (e01 q) = true ∧
      chkEdge msTree (nibLoop nib11 (maskOf q) k16) (e11 q) = true := by
  have h := cover_ok
  simp only [checkCover, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hm0, hw0⟩, hrM⟩, hact, hal⟩
  refine ⟨Nat.eq_of_beq_eq_true hm0, Nat.eq_of_beq_eq_true hw0, Nat.eq_of_beq_eq_true hrM, fun q hq => ?_⟩
  have hnz := allActive_spec kM q hq hact
  have hq_al := al12_spec coverNode rsTree msTree hal q
  unfold al0 at hq_al
  have hbeq := beq_n0_false_of_ne hnz
  change Bool.rec (coverNode (recOf q) (maskOf q)) true (Nat.beq (recOf q) n0) = true at hq_al
  rw [hbeq] at hq_al
  dsimp only [coverNode] at hq_al
  simp only [Bool.and_eq_true] at hq_al
  rcases hq_al with ⟨⟨⟨⟨⟨hwmin, he0⟩, he1⟩, he2⟩, hwmax⟩, ⟨hc0, hc1⟩, hc2⟩
  exact ⟨hnz, Nat.le_of_ble_eq_true hwmin, Nat.le_of_ble_eq_true hwmax, Nat.le_of_ble_eq_true he0, Nat.le_of_ble_eq_true he1, Nat.le_of_ble_eq_true he2, hc0, hc1, hc2⟩
noncomputable def dfaWords : Nat -> List Bool -> List (List Bool)
  | q, [] => if q < kM then [[]] else []
  | q, false :: cs => if q < kM then (dfaWords (e00 q) cs).map (false :: ·) ++ (dfaWords (e01 q) cs).map (true :: ·) else []
  | q, true :: cs => if q < kM then (dfaWords (e11 q) cs).map (true :: ·) else []
def segment (f : Nat -> Bool) : Nat -> Nat -> List Bool
  | _, 0 => []
  | t, n + 1 => f t :: segment f (t + 1) n
theorem segment_length (f : Nat -> Bool) (t n : Nat) : (segment f t n).length = n := by
  induction n generalizing t with | zero => rfl | succ n ih => simp [segment, ih]
theorem strip_or_words_mem_aux (x : Int -> Bool) : ∀ n t q, q < kM → (maskOf q).testBit (rStrip6 x t) = true →
    segment (fun i => evol x i 0 || evol x i 1) t n ∈ dfaWords q (segment (fun i => evol x i 0) t n)
  | 0, _, q, hq, _ => by simp [segment, dfaWords, hq]
  | n + 1, t, q, hq, hm => by
    obtain ⟨_, _, _, hcov⟩ := cover_facts
    obtain ⟨_, _, _, he0, he1, he2, hc0, hc1, hc2⟩ := hcov q hq
    have hn012 := nib_fast_ok
    have hn00 : chkNibFast nib00 false false k64 = true := (Bool.and_eq_true _ _).mp hn012 |>.1
    have hn01 : chkNibFast nib01 false true k64 = true := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hn012).2 |>.1
    have hn11 : chkNibFast nib11 true true k64 = true := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hn012).2 |>.2
    have hs_lt : rStrip6 x t < 64 := code6_lt _
    have hs0 : (rStrip6 x t).testBit 0 = evol x t 1 := code6_testBit _ 0 (by decide)
    have hs'_lt : rStrip6 x (t + 1) < 64 := code6_lt _
    simp only [segment]
    cases hc_val : evol x t 0
    · simp only [dfaWords, hq, ↓reduceIte, Bool.false_or]
      cases h1_val : evol x t 1
      · have hsm := nibLoop_step_sound hn00 hs_lt hm (by rw [hs0, h1_val]; rfl) (evol x t 7)
        have hsucc := rStrip6_succ x t; rw [hc_val] at hsucc; rw [← hsucc] at hsm
        obtain ⟨hq', hm'⟩ := chkEdge_spec hc0 he0 hs'_lt hsm
        exact List.mem_append_left _ (List.mem_map.mpr ⟨_, strip_or_words_mem_aux x n (t + 1) (e00 q) hq' hm', rfl⟩)
      · have hsm := nibLoop_step_sound hn01 hs_lt hm (by rw [hs0, h1_val]; rfl) (evol x t 7)
        have hsucc := rStrip6_succ x t; rw [hc_val] at hsucc; rw [← hsucc] at hsm
        obtain ⟨hq', hm'⟩ := chkEdge_spec hc1 he1 hs'_lt hsm
        exact List.mem_append_right _ (List.mem_map.mpr ⟨_, strip_or_words_mem_aux x n (t + 1) (e01 q) hq' hm', rfl⟩)
    · simp only [dfaWords, hq, ↓reduceIte, Bool.true_or]
      have hsm := nibLoop_step_sound hn11 hs_lt hm (by simp) (evol x t 7)
      have hsucc := rStrip6_succ x t; rw [hc_val] at hsucc; rw [← hsucc] at hsm
      obtain ⟨hq', hm'⟩ := chkEdge_spec hc2 he2 hs'_lt hsm
      exact List.mem_map.mpr ⟨_, strip_or_words_mem_aux x n (t + 1) (e11 q) hq' hm', rfl⟩
theorem strip_or_words_mem (x : Int -> Bool) (t n : Nat) :
    segment (fun i => evol x i 0 || evol x i 1) t n ∈ dfaWords 0 (segment (fun i => evol x i 0) t n) := by
  obtain ⟨hm0, _, _, _⟩ := cover_facts
  apply strip_or_words_mem_aux x n t 0 (by decide)
  rw [hm0, show all64 = 2 ^ 64 - 1 by decide, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true (code6_lt _)

-- 4B. Base-65536 SIMD Soundness & Block Growth Bound:
def digit (v k : Nat) : Nat := (v / 65536 ^ k) % 65536
theorem digit_zero (v : Nat) : digit v 0 = v % 65536 := by simp [digit]
theorem digit_succ (v k : Nat) : digit v (k + 1) = digit (v / 65536) k := by
  simp only [digit, Nat.pow_succ', Nat.div_div_eq_div_mul]
theorem digit_lt (v k : Nat) : digit v k < 65536 := Nat.mod_lt _ (by decide)
theorem digit_add : ∀ k a b, (∀ j, j ≤ k → digit a j + digit b j < 65536) →
    digit (a + b) k = digit a k + digit b k ∧ (a + b) / 65536 ^ (k + 1) = a / 65536 ^ (k + 1) + b / 65536 ^ (k + 1)
  | 0, a, b, h => by have h0 := h 0 (Nat.le_refl 0); simp only [digit, Nat.pow_zero, Nat.div_one] at h0 ⊢; omega
  | k + 1, a, b, h => by
    have h0 := h 0 (Nat.zero_le _); simp only [digit_zero] at h0
    have hdiv : (a + b) / 65536 = a / 65536 + b / 65536 := by omega
    have ih := digit_add k (a / 65536) (b / 65536) (fun j hj => by simpa [digit_succ] using h (j + 1) (by omega))
    rw [digit_succ, digit_succ, digit_succ, hdiv]
    refine ⟨ih.1, ?_⟩
    have hp : 65536 ^ (k + 1 + 1) = 65536 * 65536 ^ (k + 1) := Nat.pow_succ'
    rw [hp, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv, ih.2]
theorem testBit_digit (v k r : Nat) (hr : r < 16) : (digit v k).testBit r = v.testBit (16 * k + r) := by
  unfold digit; rw [show 65536 = 2 ^ 16 by rfl, ← Nat.pow_mul, Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and, Nat.testBit_div_two_pow]
  congr 1; omega
def repN : Nat -> Nat | 0 => 0 | n + 1 => 1 + 65536 * repN n
theorem digit_mul_repN : ∀ n c k, c < 65536 → k < n → digit (c * repN n) k = c
  | 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, c, 0, hc, _ => by
    unfold repN; rw [digit_zero, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm c 65536, Nat.mul_assoc]; omega
  | n + 1, c, k + 1, hc, hk => by
    unfold repN; rw [digit_succ, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm c 65536, Nat.mul_assoc]
    have hdiv : (c + 65536 * (c * repN n)) / 65536 = c * repN n := by omega
    rw [hdiv]; exact digit_mul_repN n c k hc (by omega)
theorem repL_eq : repL = repN kLanes := by decide +kernel
theorem hi2L_eq : hi2L = 49152 * repN kLanes := by decide +kernel
theorem msbL_eq : msbL = 32768 * repN kLanes := by decide +kernel
theorem bitBounded_iff_div_zero (L x : Nat) : BitBounded (16 * L) x ↔ x / 65536 ^ L = 0 := by
  rw [show 65536 = 2 ^ 16 by rfl, ← Nat.pow_mul]
  constructor
  · intro h; apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_div_two_pow, Nat.zero_testBit]; exact h _ (by omega)
  · intro h j hj; have hb := congrArg (fun z => z.testBit (j - 16 * L)) h
    rw [Nat.testBit_div_two_pow, Nat.zero_testBit, show j - 16 * L + 16 * L = j by omega] at hb; exact hb
theorem digit_eq_zero_of_bdd {L x k : Nat} (hb : BitBounded (16 * L) x) (hk : L ≤ k) : digit x k = 0 := by
  have h0 := (bitBounded_iff_div_zero L x).mp hb
  unfold digit; rw [show k = L + (k - L) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul, h0]; simp
theorem digit_lor_shift {L a b : Nat} (ha : BitBounded (16 * L) a) (k : Nat) :
    digit (Nat.lor a (Nat.shiftLeft b (16 * L))) k = if k < L then digit a k else digit b (k - L) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 16
  · rw [testBit_digit _ _ _ hr, testBit_lor', testBit_shl']
    by_cases hk : k < L
    · have hlt : ¬ (16 * L ≤ 16 * k + r) := by omega
      simp [hk, testBit_digit _ _ _ hr, hlt]
    · have hge : 16 * L ≤ 16 * k + r := by omega
      rw [ha (16 * k + r) hge, Bool.false_or]
      simp [hk, testBit_digit _ _ _ hr, hge]
      congr 1
      omega
  · have hd16 : ∀ x, digit x k < 2 ^ 16 := fun x => digit_lt x k
    have hd16' : ∀ x, digit x (k - L) < 2 ^ 16 := fun x => digit_lt x (k - L)
    have h1 : digit (Nat.lor a (Nat.shiftLeft b (16 * L))) k < 2 ^ r :=
      Nat.lt_of_lt_of_le (hd16 _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 16 ≤ r))
    have h2 : (if k < L then digit a k else digit b (k - L)) < 2 ^ r := by
      split
      · exact Nat.lt_of_lt_of_le (hd16 _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 16 ≤ r))
      · exact Nat.lt_of_lt_of_le (hd16' _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 16 ≤ r))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
theorem lt_16384_of_bits {u : Nat} (hu : u < 65536) (h14 : u.testBit 14 = false) (h15 : u.testBit 15 = false) : u < 16384 := by
  have d14 : (u / 2 ^ 14).testBit 0 = false := by rw [Nat.testBit_div_two_pow]; exact h14
  have d15 : (u / 2 ^ 15).testBit 0 = false := by rw [Nat.testBit_div_two_pow]; exact h15
  rw [Nat.testBit_zero] at d14 d15; simp at d14 d15; omega
theorem lt_32768_of_bit15 {u : Nat} (hu : u < 65536) (h15 : u.testBit 15 = false) : u < 32768 := by
  have d15 : (u / 2 ^ 15).testBit 0 = false := by rw [Nat.testBit_div_two_pow]; exact h15
  rw [Nat.testBit_zero] at d15; simp at d15; omega
theorem ok14_digit_lt {tr : S12} (hok : ok14 rsTree tr = true) (hM : g12 tr kM = 0) {q k : Nat} (hq : q ≤ kM) (hk : k < kLanes) :
    digit (g12 tr q) k < 16384 := by
  by_cases hqe : q = kM
  · rw [hqe, hM]; simp [digit]
  · obtain ⟨_, _, _, hcov⟩ := cover_facts
    have hnz := (hcov q (by omega)).1
    have hal := al12_spec _ rsTree tr hok q
    unfold al0 at hal
    have hbeq : Nat.beq (recOf q) n0 = false := beq_n0_false_of_ne hnz
    change Bool.rec _ true (Nat.beq (recOf q) n0) = true at hal
    rw [hbeq] at hal; dsimp only at hal
    have hland : Nat.land (g12 tr q) hi2L = 0 := Nat.eq_of_beq_eq_true hal
    have hd_hi : digit hi2L k = 49152 := by rw [hi2L_eq]; exact digit_mul_repN kLanes 49152 k (by decide) hk
    apply lt_16384_of_bits (digit_lt _ _)
    · have hb := congrArg (fun z => z.testBit (16 * k + 14)) hland
      rw [testBit_land', Nat.zero_testBit, ← testBit_digit _ _ 14 (by decide), ← testBit_digit _ _ 14 (by decide), hd_hi] at hb
      have ht : (49152 : Nat).testBit 14 = true := by decide
      rw [ht, Bool.and_true] at hb; exact hb
    · have hb := congrArg (fun z => z.testBit (16 * k + 15)) hland
      rw [testBit_land', Nat.zero_testBit, ← testBit_digit _ _ 15 (by decide), ← testBit_digit _ _ 15 (by decide), hd_hi] at hb
      have ht : (49152 : Nat).testBit 15 = true := by decide
      rw [ht, Bool.and_true] at hb; exact hb

noncomputable def dfaWeight : List Bool -> Nat -> Nat
  | [], q => wOf q
  | false :: cs, q => if q < kM then dfaWeight cs (e00 q) + dfaWeight cs (e01 q) else 0
  | true :: cs, q => if q < kM then dfaWeight cs (e11 q) else 0
def wordOf : Nat -> Nat -> List Bool
  | 0, _ => []
  | d + 1, k => (if k < 2 ^ d then false else true) :: wordOf d (if k < 2 ^ d then k else k - 2 ^ d)
def codeList : List Bool -> Nat
  | [] => 0
  | false :: xs => codeList xs
  | true :: xs => 2 ^ xs.length + codeList xs
theorem codeList_lt : ∀ xs : List Bool, codeList xs < 2 ^ xs.length
  | [] => by decide
  | false :: xs => by have := codeList_lt xs; unfold codeList; rw [List.length_cons, Nat.pow_succ]; omega
  | true :: xs => by have := codeList_lt xs; unfold codeList; rw [List.length_cons, Nat.pow_succ]; omega
theorem wordOf_codeList : ∀ xs : List Bool, wordOf xs.length (codeList xs) = xs
  | [] => rfl
  | false :: xs => by
    have hlt := codeList_lt xs; simp only [List.length_cons, codeList, wordOf, hlt, ↓reduceIte, wordOf_codeList xs]
  | true :: xs => by
    have hlt := codeList_lt xs; have hge : ¬ (2 ^ xs.length + codeList xs < 2 ^ xs.length) := by omega
    simp only [List.length_cons, codeList, wordOf, hge, ↓reduceIte, show 2 ^ xs.length + codeList xs - 2 ^ xs.length = codeList xs by omega, wordOf_codeList xs]

def VecInv (L : Nat) (f : Nat -> Nat -> Nat) (v : Nat) : Prop :=
  ∃ tr : S12, v = pv12 tr ∧ Wf12 tr ∧ g12 tr kM = 0 ∧
    (∀ q, q ≤ kM → BitBounded (16 * L) (g12 tr q)) ∧ (∀ q, q ≤ kM → ∀ k, k < L → digit (g12 tr q) k = f k q)
theorem bdd_mono {A B x : Nat} (hab : A ≤ B) (ha : BitBounded A x) : BitBounded B x := fun j hj => ha j (by omega)
theorem v0_inv : VecInv 1 (fun k q => dfaWeight (wordOf 0 k) q) (pv12 (mp12 (fun r => Nat.land (Nat.shiftRight r k39) m13) rsTree)) := by
  obtain ⟨_, _, hrM, hcov⟩ := cover_facts
  let tr := mp12 (fun r => Nat.land (Nat.shiftRight r k39) m13) rsTree
  refine ⟨tr, rfl, mp12_wf _ _, ?_, ?_, ?_⟩
  · dsimp [tr]; rw [g12_mp12]; change mp0 _ (recOf kM) = 0; rw [hrM]; rfl
  · intro q hq; dsimp [tr]; rw [g12_mp12]
    by_cases hqe : q = kM
    · subst hqe
      change BitBounded (16 * 1) (mp0 _ (recOf kM))
      rw [hrM]
      intro j _
      exact Nat.zero_testBit j
    · have ⟨hnz, _, hwmax, _⟩ := hcov q (by omega)
      have hbeq : Nat.beq (recOf q) n0 = false := beq_n0_false_of_ne hnz
      change BitBounded (16 * 1) (Bool.rec (Nat.land (wRaw q) vm0) n0 (Nat.beq (recOf q) n0))
      rw [hbeq]; dsimp only
      have hw_lt : wRaw q < 2 ^ 16 := by have : kw0 ≤ 441 := (by decide); omega
      have hw_bdd : BitBounded 16 (wRaw q) := fun j hj => Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw_lt (Nat.pow_le_pow_right (by decide : 0 < 2) hj))
      rw [land_self_of_bounded vm0_mask (bdd_mono (by decide : 16 ≤ vsh0) hw_bdd)]; simpa using hw_bdd
  · intro q hq k hk; have hk0 : k = 0 := (by omega); subst hk0
    dsimp [tr, wordOf, dfaWeight]; rw [g12_mp12]
    by_cases hqe : q = kM
    · subst hqe; change digit (mp0 _ (recOf kM)) 0 = wOf kM; rw [hrM]; simp [mp0, n0, wOf, digit]
    · have hlt : q < kM := (by omega); have ⟨hnz, _, hwmax, _⟩ := hcov q hlt
      have hbeq : Nat.beq (recOf q) n0 = false := beq_n0_false_of_ne hnz
      change digit (Bool.rec (Nat.land (wRaw q) vm0) n0 (Nat.beq (recOf q) n0)) 0 = wOf q
      rw [hbeq]; dsimp only
      have hw_lt : wRaw q < 2 ^ 16 := by have : kw0 ≤ 441 := (by decide); omega
      have hw_bdd : BitBounded 16 (wRaw q) := fun j hj => Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw_lt (Nat.pow_le_pow_right (by decide : 0 < 2) hj))
      rw [land_self_of_bounded vm0_mask (bdd_mono (by decide : 16 ≤ vsh0) hw_bdd), digit_zero, Nat.mod_eq_of_lt hw_lt]; simp only [wOf, hlt, ↓reduceIte]
theorem stepS_inv {d v : Nat} (hd : d < kBsuf) (hinv : VecInv (2 ^ d) (fun k q => dfaWeight (wordOf d k) q) v)
    (hok : ok14 rsTree (uv12 theMasks v) = true) :
    VecInv (2 ^ (d + 1)) (fun k q => dfaWeight (wordOf (d + 1) k) q) (stepS theMasks rsTree v (16 * 2 ^ d)) := by
  obtain ⟨_, _, hrM, hcov⟩ := cover_facts
  obtain ⟨tr, rfl, hwf, htrM, hbdd, hdig⟩ := hinv
  rw [uv12_pv12 hwf] at hok
  have hdl : 2 ^ d ≤ kLanes := by have : kLanes = 2 ^ kBsuf := (by decide); rw [this]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hvsh : 16 * 2 ^ (d + 1) ≤ vsh0 := by
    have h1 : 2 ^ (d + 1) ≤ kLanes := by have : kLanes = 2 ^ kBsuf := (by decide); rw [this]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have h2 : vsh0 = 16 * kLanes := (by decide); omega
  unfold stepS stepStr; rw [uv12_pv12 hwf]
  refine ⟨_, rfl, mp12_wf _ _, ?_, ?_, ?_⟩
  · rw [g12_mp12]; change mp0 _ (recOf kM) = 0; rw [hrM]; rfl
  · intro q hq; rw [g12_mp12]
    by_cases hqe : q = kM
    · subst hqe; change BitBounded _ (mp0 _ (recOf kM)); rw [hrM]; intro j _; exact Nat.zero_testBit j
    · have ⟨hnz, _, _, he0, he1, he2, _⟩ := hcov q (by omega)
      have hbeq : Nat.beq (recOf q) n0 = false := beq_n0_false_of_ne hnz
      let v00 := g12 tr (e00 q); let v01 := g12 tr (e01 q); let v11 := g12 tr (e11 q)
      change BitBounded _ (Bool.rec (Nat.land (Nat.lor (Nat.add v00 v01) (Nat.shiftLeft v11 (16 * 2 ^ d))) vm0) n0 (Nat.beq (recOf q) n0))
      rw [hbeq]; dsimp only
      have hsum_no : ∀ j, j ≤ 2 ^ d - 1 → digit v00 j + digit v01 j < 65536 := by
        intro j hj; have hj' : j < kLanes := by have := Nat.two_pow_pos d; omega
        have l0 : digit v00 j < 16384 := ok14_digit_lt hok htrM he0 hj'
        have l1 : digit v01 j < 16384 := ok14_digit_lt hok htrM he1 hj'
        omega
      have hdiv0 : (v00 + v01) / 65536 ^ (2 ^ d) = 0 := by
        have hp := Nat.two_pow_pos d
        have hda := (digit_add (2 ^ d - 1) v00 v01 hsum_no).2
        rw [show 2 ^ d - 1 + 1 = 2 ^ d by omega] at hda
        rw [hda, (bitBounded_iff_div_zero _ _).mp (hbdd _ he0), (bitBounded_iff_div_zero _ _).mp (hbdd _ he1)]
      have hb_sum : BitBounded (16 * 2 ^ d) (Nat.add v00 v01) := (bitBounded_iff_div_zero _ _).mpr hdiv0
      have hb_comb : BitBounded (16 * 2 ^ (d + 1)) (Nat.lor (Nat.add v00 v01) (Nat.shiftLeft v11 (16 * 2 ^ d))) := by
        rw [Nat.pow_succ, show 16 * (2 ^ d * 2) = 2 * (16 * 2 ^ d) by omega]; exact lor_shift_bounded hb_sum (hbdd _ he2)
      rw [land_self_of_bounded vm0_mask (bdd_mono hvsh hb_comb)]; exact hb_comb
  · intro q hq k hk; rw [g12_mp12]
    by_cases hqe : q = kM
    · subst hqe; change digit (mp0 _ (recOf kM)) k = _; rw [hrM]
      have hz : ∀ w, dfaWeight w kM = 0 := fun w => by cases w with | nil => simp [dfaWeight, wOf] | cons b _ => cases b <;> simp [dfaWeight]
      dsimp only
      rw [hz]
      simp [mp0, n0, digit]
    · have hlt : q < kM := (by omega); have ⟨hnz, _, _, he0, he1, he2, _⟩ := hcov q hlt
      have hbeq : Nat.beq (recOf q) n0 = false := beq_n0_false_of_ne hnz
      let v00 := g12 tr (e00 q); let v01 := g12 tr (e01 q); let v11 := g12 tr (e11 q)
      change digit (Bool.rec (Nat.land (Nat.lor (Nat.add v00 v01) (Nat.shiftLeft v11 (16 * 2 ^ d))) vm0) n0 (Nat.beq (recOf q) n0)) k = _
      rw [hbeq]; dsimp only
      have hsum_no : ∀ j, j < 2 ^ d → digit v00 j + digit v01 j < 65536 := by
        intro j hj; have l0 : digit v00 j < 16384 := ok14_digit_lt hok htrM he0 (by omega)
        have l1 : digit v01 j < 16384 := ok14_digit_lt hok htrM he1 (by omega)
        omega
      have hdiv0 : (v00 + v01) / 65536 ^ (2 ^ d) = 0 := by
        have hp := Nat.two_pow_pos d
        have hda := (digit_add (2 ^ d - 1) v00 v01 (fun j hj => hsum_no j (by omega))).2
        rw [show 2 ^ d - 1 + 1 = 2 ^ d by omega] at hda
        rw [hda, (bitBounded_iff_div_zero _ _).mp (hbdd _ he0), (bitBounded_iff_div_zero _ _).mp (hbdd _ he1)]
      have hb_sum : BitBounded (16 * 2 ^ d) (Nat.add v00 v01) := (bitBounded_iff_div_zero _ _).mpr hdiv0
      have hb_comb : BitBounded (16 * 2 ^ (d + 1)) (Nat.lor (Nat.add v00 v01) (Nat.shiftLeft v11 (16 * 2 ^ d))) := by
        rw [Nat.pow_succ, show 16 * (2 ^ d * 2) = 2 * (16 * 2 ^ d) by omega]; exact lor_shift_bounded hb_sum (hbdd _ he2)
      rw [land_self_of_bounded vm0_mask (bdd_mono hvsh hb_comb), digit_lor_shift hb_sum k]
      by_cases hkd : k < 2 ^ d
      · simp only [hkd, ↓reduceIte, wordOf, dfaWeight, hlt]
        rw [Nat.add_eq, (digit_add k v00 v01 (fun j hj => hsum_no j (by omega))).1, hdig _ he0 k hkd, hdig _ he1 k hkd]
      · have hk2 : k - 2 ^ d < 2 ^ d := by rw [Nat.pow_succ] at hk; omega
        simp only [hkd, ↓reduceIte, wordOf, dfaWeight, hlt]
        exact hdig _ he2 (k - 2 ^ d) hk2
def shFrom : Nat -> Nat -> List Nat | _, 0 => [] | d, m + 1 => (16 * 2 ^ d) :: shFrom (d + 1) m
theorem shList_eq : shList = shFrom 0 kBsuf := by decide +kernel
theorem runSuf_inv : ∀ m d v, d + m ≤ kBsuf → VecInv (2 ^ d) (fun k q => dfaWeight (wordOf d k) q) v →
    (runSuf theMasks rsTree (shFrom d m) v).1 = true →
    VecInv (2 ^ (d + m)) (fun k q => dfaWeight (wordOf (d + m) k) q) (runSuf theMasks rsTree (shFrom d m) v).2 := by
  intro m
  induction m with
  | zero =>
    intro d v _ hinv _
    simpa [shFrom, runSuf] using hinv
  | succ m ih =>
    intro d v hdm hinv hrun
    change ((Bool.rec (false, n0) (runSuf theMasks rsTree (shFrom (d + 1) m) (stepS theMasks rsTree v (16 * 2 ^ d))) (ok14 rsTree (uv12 theMasks v))) : Bool × Nat).1 = true at hrun
    cases hok : ok14 rsTree (uv12 theMasks v) <;> rw [hok] at hrun <;> dsimp only at hrun
    · contradiction
    · have hinv' := stepS_inv (by omega) hinv hok
      have hrec := ih (d + 1) _ (by omega) hinv' hrun
      change VecInv _ _ ((Bool.rec (false, n0) (runSuf theMasks rsTree (shFrom (d + 1) m) (stepS theMasks rsTree v (16 * 2 ^ d))) (ok14 rsTree (uv12 theMasks v))) : Bool × Nat).2
      rw [hok]
      dsimp only
      simpa [show d + 1 + m = d + (m + 1) by omega] using hrec
theorem stepL_inv {pref : List Bool} {v : Nat} (hinv : VecInv kLanes (fun k q => dfaWeight (pref ++ wordOf kBsuf k) q) v)
    (hok : ok14 rsTree (uv12 theMasks v) = true) :
    VecInv kLanes (fun k q => dfaWeight ((false :: pref) ++ wordOf kBsuf k) q) (stepL theMasks rsTree v) := by
  obtain ⟨_, _, hrM, hcov⟩ := cover_facts
  obtain ⟨tr, rfl, hwf, htrM, hbdd, hdig⟩ := hinv
  rw [uv12_pv12 hwf] at hok
  have hvsh : 16 * kLanes = vsh0 := by decide
  unfold stepL stepLtr; rw [uv12_pv12 hwf]
  refine ⟨_, rfl, mp12_wf _ _, ?_, ?_, ?_⟩
  · rw [g12_mp12]; change mp0 _ (recOf kM) = 0; rw [hrM]; rfl
  · intro q hq; rw [g12_mp12]; rw [hvsh]; exact mp0_bdd _ _
  · intro q hq k hk; rw [g12_mp12]
    by_cases hqe : q = kM
    · subst hqe; change digit (mp0 _ (recOf kM)) k = _; rw [hrM]; simp [mp0, n0, digit, dfaWeight]
    · have hlt : q < kM := (by omega); have ⟨hnz, _, _, he0, he1, _⟩ := hcov q hlt
      have hbeq : Nat.beq (recOf q) n0 = false := beq_n0_false_of_ne hnz
      let v00 := g12 tr (e00 q); let v01 := g12 tr (e01 q)
      change digit (Bool.rec (Nat.land (Nat.add v00 v01) vm0) n0 (Nat.beq (recOf q) n0)) k = _
      rw [hbeq]; dsimp only
      have hsum_no : ∀ j, j < kLanes → digit v00 j + digit v01 j < 65536 := by
        intro j hj; have l0 : digit v00 j < 16384 := ok14_digit_lt hok htrM he0 hj
        have l1 : digit v01 j < 16384 := ok14_digit_lt hok htrM he1 hj
        omega
      have hdiv0 : (v00 + v01) / 65536 ^ kLanes = 0 := by
        have hp : 0 < kLanes := by decide
        have hda := (digit_add (kLanes - 1) v00 v01 (fun j hj => hsum_no j (by omega))).2
        rw [show kLanes - 1 + 1 = kLanes by omega] at hda
        rw [hda, (bitBounded_iff_div_zero _ _).mp (hbdd _ he0), (bitBounded_iff_div_zero _ _).mp (hbdd _ he1)]
      have hb_sum : BitBounded vsh0 (Nat.add v00 v01) := by rw [← hvsh]; exact (bitBounded_iff_div_zero _ _).mpr hdiv0
      rw [land_self_of_bounded vm0_mask hb_sum, Nat.add_eq, (digit_add k v00 v01 (fun j hj => hsum_no j (by omega))).1, hdig _ he0 k hk, hdig _ he1 k hk]
      simp [dfaWeight, hlt]
theorem stepR_inv {pref : List Bool} {v : Nat} (hinv : VecInv kLanes (fun k q => dfaWeight (pref ++ wordOf kBsuf k) q) v) :
    VecInv kLanes (fun k q => dfaWeight ((true :: pref) ++ wordOf kBsuf k) q) (stepR theMasks rsTree v) := by
  obtain ⟨_, _, hrM, hcov⟩ := cover_facts
  obtain ⟨tr, rfl, hwf, htrM, hbdd, hdig⟩ := hinv
  have hvsh : 16 * kLanes = vsh0 := by decide
  unfold stepR stepRtr; rw [uv12_pv12 hwf]
  refine ⟨_, rfl, mp12_wf _ _, ?_, ?_, ?_⟩
  · rw [g12_mp12]; change mp0 _ (recOf kM) = 0; rw [hrM]; rfl
  · intro q hq; rw [g12_mp12]; rw [hvsh]; exact mp0_bdd _ _
  · intro q hq k hk; rw [g12_mp12]
    by_cases hqe : q = kM
    · subst hqe; change digit (mp0 _ (recOf kM)) k = _; rw [hrM]; simp [mp0, n0, digit, dfaWeight]
    · have hlt : q < kM := (by omega); have ⟨hnz, _, _, _, _, he2, _⟩ := hcov q hlt
      have hbeq : Nat.beq (recOf q) n0 = false := beq_n0_false_of_ne hnz
      let v11 := g12 tr (e11 q)
      change digit (Bool.rec (Nat.land v11 vm0) n0 (Nat.beq (recOf q) n0)) k = _
      rw [hbeq]; dsimp only
      have hb11 : BitBounded vsh0 v11 := by rw [← hvsh]; exact hbdd _ he2
      rw [land_self_of_bounded vm0_mask hb11, hdig _ he2 k hk]; simp [dfaWeight, hlt]
theorem digit_mul_kQ {x k : Nat} (h : ∀ j, j ≤ k → digit x j < 16384) : digit (Nat.mul kQ x) k = kQ * digit x k := by
  have hq : kQ = 1 ∨ kQ = 2 := by decide
  rcases hq with h1 | h2
  · rw [Nat.mul_eq, h1, Nat.one_mul, Nat.one_mul]
  · rw [Nat.mul_eq, h2, Nat.two_mul, Nat.two_mul, (digit_add k x x (fun j hj => by have := h j hj; omega)).1]
theorem chkV_spec {pref : List Bool} {v : Nat} (hinv : VecInv kLanes (fun k q => dfaWeight (pref ++ wordOf kBsuf k) q) v)
    (hchk : chkV theMasks rsTree v = true) : ∀ q, ∀ k, k < kLanes → kQ * dfaWeight (pref ++ wordOf kBsuf k) q ≤ kP * wOf q := by
  obtain ⟨_, _, _, hcov⟩ := cover_facts
  obtain ⟨tr, rfl, hwf, htrM, _, hdig⟩ := hinv
  unfold chkV at hchk; dsimp only at hchk; rw [uv12_pv12 hwf] at hchk
  obtain ⟨hok, hal⟩ := bool_rec_false_eq hchk
  intro q k hk
  by_cases hlt : q < kM
  · have ⟨hnz, _, hwmax, _⟩ := hcov q hlt
    have hq_al := al12_spec _ rsTree tr hal q
    unfold al0 at hq_al
    have hbeq : Nat.beq (recOf q) n0 = false := beq_n0_false_of_ne hnz
    change Bool.rec _ true (Nat.beq (recOf q) n0) = true at hq_al
    rw [hbeq] at hq_al; dsimp only at hq_al
    let vi := g12 tr q
    let pad := Nat.sub lim15 (Nat.mul kP (wRaw q))
    have hland : Nat.land (Nat.add (Nat.mul pad repL) (Nat.mul kQ vi)) msbL = 0 := Nat.eq_of_beq_eq_true hq_al
    have hpad_lt : kP * wRaw q ≤ 32767 := by have : kP * kw0 ≤ 32767 := (by decide); have := Nat.mul_le_mul_left kP hwmax; omega
    have hd_pad : ∀ j, j < kLanes → digit (Nat.mul pad repL) j = 32767 - kP * wRaw q := by
      intro j hj; rw [Nat.mul_eq, repL_eq]; dsimp [pad, lim15]
      exact digit_mul_repN kLanes _ j (by omega) hj
    have hd_vi : ∀ j, j ≤ k → digit vi j < 16384 := fun j hj => ok14_digit_lt hok htrM (by omega) (by omega)
    have hsum_lt : ∀ j, j ≤ k → digit (Nat.mul pad repL) j + digit (Nat.mul kQ vi) j < 65536 := by
      intro j hj; rw [hd_pad j (by omega), digit_mul_kQ (fun i hi => hd_vi i (by omega))]; have := hd_vi j hj; have : kQ ≤ 2 := (by decide); have := Nat.mul_le_mul_right (digit vi j) this; omega
    have hd_tot : digit (Nat.add (Nat.mul pad repL) (Nat.mul kQ vi)) k = (32767 - kP * wRaw q) + kQ * digit vi k := by
      rw [Nat.add_eq, (digit_add k _ _ hsum_lt).1, hd_pad k hk, digit_mul_kQ hd_vi]
    have hd_msb : digit msbL k = 32768 := by rw [msbL_eq]; exact digit_mul_repN kLanes 32768 k (by decide) hk
    have hb15 := congrArg (fun z => z.testBit (16 * k + 15)) hland
    rw [testBit_land', Nat.zero_testBit, ← testBit_digit _ _ 15 (by decide), ← testBit_digit _ _ 15 (by decide), hd_msb] at hb15
    have ht : (32768 : Nat).testBit 15 = true := by decide
    rw [ht, Bool.and_true] at hb15
    have htot_lt := lt_32768_of_bit15 (digit_lt _ _) hb15
    rw [hd_tot] at htot_lt
    dsimp only [vi] at htot_lt
    rw [hdig q (by omega) k hk] at htot_lt
    dsimp only at htot_lt
    simp only [wOf, hlt, ↓reduceIte]
    dsimp only [kP, kQ] at hpad_lt htot_lt ⊢
    omega
  · have h0w : ∀ w, dfaWeight w q = 0 := by intro w; cases w with | nil => simp [dfaWeight, wOf, hlt] | cons b ws => cases b <;> simp [dfaWeight, hlt]
    rw [h0w]; simp [wOf, hlt]
theorem walkHi_spec : ∀ h pref v, VecInv kLanes (fun k q => dfaWeight (pref ++ wordOf kBsuf k) q) v →
    walkHi theMasks rsTree h v = true → ∀ u : List Bool, u.length = h → ∀ q k, k < kLanes →
    kQ * dfaWeight (u.reverse ++ pref ++ wordOf kBsuf k) q ≤ kP * wOf q
  | 0, pref, v, hinv, hw, u, hu, q, k, hk => by
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero hu; subst hu0; simpa using chkV_spec hinv hw q k hk
  | h + 1, pref, v, hinv, hw, u, hu, q, k, hk => by
    change Bool.rec false (Bool.rec false (walkHi theMasks rsTree h (stepR theMasks rsTree v)) (walkHi theMasks rsTree h (stepL theMasks rsTree v))) (ok14 rsTree (uv12 theMasks v)) = true at hw
    obtain ⟨hok, hlr⟩ := bool_rec_false_eq hw
    obtain ⟨hwL, hwR⟩ := bool_rec_false_eq hlr
    match u, hu with
    | false :: us, hu' =>
      have ih := walkHi_spec h (false :: pref) _ (stepL_inv hinv hok) hwL us (by simpa using hu') q k hk
      simpa [List.reverse_cons, List.append_assoc] using ih
    | true :: us, hu' =>
      have ih := walkHi_spec h (true :: pref) _ (stepR_inv hinv) hwR us (by simpa using hu') q k hk
      simpa [List.reverse_cons, List.append_assoc] using ih
theorem block_bound_one (c : List Bool) (hc : c.length = kBtot) (q : Nat) : kQ * dfaWeight c q ≤ kP * wOf q := by
  have h := strip_cert_ok
  unfold checkAll at h
  dsimp only at h
  obtain ⟨hp1, hwh⟩ := (Bool.and_eq_true _ _).mp h
  rw [shList_eq] at hp1 hwh
  have hinv_s := runSuf_inv kBsuf 0 _ (by omega) v0_inv hp1
  have hkl : 2 ^ kBsuf = kLanes := by decide
  rw [Nat.zero_add, hkl] at hinv_s
  let u := (c.take kBhi).reverse
  let suf := c.drop kBhi
  have htot : kBtot = kBhi + kBsuf := by decide
  have hu_len : u.length = kBhi := by simp [u, hc, htot]
  have hsuf_len : suf.length = kBsuf := by simp [suf, hc, htot]
  have hk : codeList suf < kLanes := by have := codeList_lt suf; rw [hsuf_len, show 2 ^ kBsuf = kLanes by decide] at this; exact this
  have hres := walkHi_spec kBhi [] _ (by simpa using hinv_s) hwh u hu_len q (codeList suf) hk
  have hword : wordOf kBsuf (codeList suf) = suf := by rw [← hsuf_len]; exact wordOf_codeList suf
  have hcat : u.reverse ++ [] ++ wordOf kBsuf (codeList suf) = c := by simp [u, suf, hword, List.take_append_drop]
  rw [hcat] at hres; exact hres
theorem dfaWeight_append_le : ∀ (u v : List Bool) {a b : Nat}, (∀ q, a * dfaWeight v q ≤ b * wOf q) →
    ∀ q, a * dfaWeight (u ++ v) q ≤ b * dfaWeight u q
  | [], v, _, _, hv, q => hv q
  | false :: us, v, a, b, hv, q => by
    by_cases hq : q < kM
    · simp only [List.cons_append, dfaWeight, hq, ↓reduceIte, Nat.mul_add]
      exact Nat.add_le_add (dfaWeight_append_le us v hv (e00 q)) (dfaWeight_append_le us v hv (e01 q))
    · simp [dfaWeight, hq]
  | true :: us, v, a, b, hv, q => by
    by_cases hq : q < kM
    · simp only [List.cons_append, dfaWeight, hq, ↓reduceIte]; exact dfaWeight_append_le us v hv (e11 q)
    · simp [dfaWeight, hq]
theorem dfaWeight_blocks : ∀ m (c : List Bool), c.length = kBtot * m → ∀ q, kQ ^ m * dfaWeight c q ≤ kP ^ m * wOf q
  | 0, c, hc, q => by have : c = [] := List.eq_nil_of_length_eq_zero (by simpa using hc); subst this; simp [dfaWeight]
  | m + 1, c, hc, q => by
    let pre := c.take (kBtot * m); let last := c.drop (kBtot * m)
    have hpre : pre.length = kBtot * m := by
      simp only [pre, List.length_take, hc, Nat.mul_succ]
      omega
    have hlast : last.length = kBtot := by
      simp only [last, List.length_drop, hc, Nat.mul_succ]
      omega
    have hcat : c = pre ++ last := (List.take_append_drop _ _).symm
    rw [hcat, Nat.pow_succ, Nat.pow_succ]
    calc (kQ ^ m * kQ) * dfaWeight (pre ++ last) q
      _ = kQ ^ m * (kQ * dfaWeight (pre ++ last) q) := by rw [Nat.mul_assoc]
      _ ≤ kQ ^ m * (kP * dfaWeight pre q) := Nat.mul_le_mul_left _ (dfaWeight_append_le pre last (block_bound_one last hlast) q)
      _ = kP * (kQ ^ m * dfaWeight pre q) := by rw [← Nat.mul_assoc, Nat.mul_comm (kQ ^ m) kP, Nat.mul_assoc]
      _ ≤ kP * (kP ^ m * wOf q) := Nat.mul_le_mul_left _ (dfaWeight_blocks m pre hpre q)
      _ = (kP ^ m * kP) * wOf q := by rw [← Nat.mul_assoc, Nat.mul_comm kP (kP ^ m)]
theorem dfaWords_length_le_weight : ∀ (c : List Bool) (q : Nat), kwMin * (dfaWords q c).length ≤ dfaWeight c q
  | [], q => by
    by_cases hq : q < kM
    · obtain ⟨_, _, _, hcov⟩ := cover_facts; have hw := (hcov q hq).2.1; simp [dfaWords, dfaWeight, wOf, hq]; omega
    · simp [dfaWords, dfaWeight, wOf, hq]
  | false :: cs, q => by
    by_cases hq : q < kM
    · simp only [dfaWords, dfaWeight, hq, ↓reduceIte, List.length_append, List.length_map, Nat.mul_add]
      exact Nat.add_le_add (dfaWords_length_le_weight cs (e00 q)) (dfaWords_length_le_weight cs (e01 q))
    · simp [dfaWords, dfaWeight, hq]
  | true :: cs, q => by
    by_cases hq : q < kM
    · simp only [dfaWords, dfaWeight, hq, ↓reduceIte, List.length_map]; exact dfaWords_length_le_weight cs (e11 q)
    · simp [dfaWords, dfaWeight, hq]
theorem strip_or_word_count (m : Nat) (c : List Bool) (hc : c.length = 12 * m) :
    16 * 2 ^ m * (dfaWords 0 c).length ≤ 147 * 21 ^ m := by
  obtain ⟨_, hw0, _, _⟩ := cover_facts
  have h1 := dfaWords_length_le_weight c 0
  have h2 := dfaWeight_blocks m c hc 0
  have h3 := Nat.mul_le_mul_left (kQ ^ m) h1
  have hw0' : wOf 0 = kw0 := by
    simp [wOf, (by decide : 0 < kM), hw0]
  rw [hw0'] at h2
  have h4 : (kwMin * kQ ^ m) * (dfaWords 0 c).length ≤ kP ^ m * kw0 := by
    calc (kwMin * kQ ^ m) * (dfaWords 0 c).length
      _ = kQ ^ m * (kwMin * (dfaWords 0 c).length) := by rw [Nat.mul_comm kwMin, Nat.mul_assoc]
      _ ≤ kQ ^ m * dfaWeight c 0 := h3
      _ ≤ kP ^ m * kw0 := h2
  have hkw1 : kwMin = 3 * 16 := by decide
  have hkw2 : kw0 = 3 * 147 := by decide
  have hq_eq : kQ = 2 := rfl
  have hp_eq : kP = 21 := rfl
  rw [hkw1, hkw2, hq_eq, hp_eq] at h4
  have hlhs : (3 * 16 * 2 ^ m) * (dfaWords 0 c).length = 3 * (16 * 2 ^ m * (dfaWords 0 c).length) := by
    simp only [Nat.mul_assoc]
  have hrhs : 21 ^ m * (3 * 147) = 3 * (147 * 21 ^ m) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (21 ^ m) 3, Nat.mul_assoc, Nat.mul_comm (21 ^ m) 147]
  rw [hlhs, hrhs] at h4
  omega

-- 4C. Periodic Center Left-Word Richness Bound & Problem 1 Reduction:
theorem segment_at {f : Nat -> Bool} {i j n : Nat} (h : segment f i n = segment f j n) (k : Nat) (hk : k < n) : f (i + k) = f (j + k) := by
  induction n generalizing i j k with
  | zero => omega
  | succ n ih =>
    have hh := List.cons.inj h
    cases k with
    | zero => simpa using hh.1
    | succ k => simpa only [show i + (k + 1) = i + 1 + k by omega, show j + (k + 1) = j + 1 + k by omega] using ih hh.2 k (by omega)
theorem segment_congr {f g : Nat -> Bool} {i j n : Nat} (h : ∀ k, k < n → f (i + k) = g (j + k)) : segment f i n = segment g j n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    simp only [segment, List.cons.injEq]
    refine ⟨by simpa using h 0 (by omega), ih fun k hk => ?_⟩
    simpa only [show i + 1 + k = i + (k + 1) by omega, show j + 1 + k = j + (k + 1) by omega] using h (k + 1) (by omega)
theorem columns_eq {s t m : Nat} (hc : ∀ k, k ≤ m → cell (s + k) 0 = cell (t + k) 0) (ho : ∀ k, k < m → orCol 0 (s + k) = orCol 0 (t + k)) :
    ∀ j k : Nat, k + j ≤ m → cell (s + k) (-(j : Int)) = cell (t + k) (-(j : Int)) := by
  have step : ∀ j, (∀ k, k + j ≤ m → cell (s + k) (-(j : Int)) = cell (t + k) (-(j : Int))) ∧
      (∀ k, k + (j + 1) ≤ m → cell (s + k) (-((j + 1 : Nat) : Int)) = cell (t + k) (-((j + 1 : Nat) : Int))) := by
    intro j; induction j with
    | zero =>
      refine ⟨fun k hk => by simpa using hc k (by omega), fun k hk => ?_⟩
      rw [show (-((0 + 1 : Nat) : Int)) = 0 - 1 by omega, cell_left' (s + k) 0, cell_left' (t + k) 0,
          show s + k + 1 = s + (k + 1) by omega, show t + k + 1 = t + (k + 1) by omega, hc (k + 1) (by omega), ho k (by omega)]
    | succ j ih =>
      refine ⟨ih.2, fun k hk => ?_⟩
      rw [show (-((j + 1 + 1 : Nat) : Int)) = (-((j + 1 : Nat) : Int)) - 1 by omega, cell_left (s + k), cell_left (t + k),
          show (-((j + 1 : Nat) : Int)) + 1 = -((j : Nat) : Int) by omega, show s + k + 1 = s + (k + 1) by omega, show t + k + 1 = t + (k + 1) by omega,
          ih.2 (k + 1) (by omega), ih.2 k (by omega), ih.1 k (by omega)]
  exact fun j k hk => (step j).1 k hk
theorem leftWord_eq {s t m : Nat} (hc : ∀ k, k ≤ m → cell (s + k) 0 = cell (t + k) 0) (ho : ∀ k, k < m → orCol 0 (s + k) = orCol 0 (t + k)) : leftWord s m = leftWord t m := by
  unfold leftWord; apply List.map_congr_left; intro k hk
  have hk' := List.mem_range.mp hk
  have h := columns_eq hc ho (k + 1) 0 (by omega)
  rw [Nat.add_zero, Nat.add_zero] at h
  exact Eq.trans (congrArg (cell _) (by omega)) (Eq.trans h (congrArg (cell _) (by omega)))
theorem center_phase {T P : Nat} (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) :
    ∀ t, T ≤ t → cell t 0 = cell (T + (t - T) % P) 0 := by
  have shift : ∀ q x, T ≤ x → cell (x + P * q) 0 = cell x 0 := by
    intro q; induction q with
    | zero => intro x _; simp
    | succ q ih => intro x hx; rw [show x + P * (q + 1) = (x + P * q) + P by rw [Nat.mul_succ]; omega, per _ (by omega), ih x hx]
  intro t ht; have hd := Nat.mod_add_div (t - T) P
  have hs := shift ((t - T) / P) (T + (t - T) % P) (by omega)
  rw [show T + (t - T) % P + P * ((t - T) / P) = t by omega] at hs; exact hs
def keyStrip (T P m t : Nat) : Nat × List Bool :=
  if t < T then (t, []) else (T + (t - T) % P, segment (orCol 0) t (12 * m))
theorem leftWord_of_keyStrip {T P m : Nat} (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) {a b : Nat}
    (h : keyStrip T P m a = keyStrip T P m b) : leftWord a (12 * m) = leftWord b (12 * m) := by
  unfold keyStrip at h
  by_cases ha : a < T <;> by_cases hb : b < T <;> simp only [ha, hb, ↓reduceIte] at h
  · rw [(Prod.mk.inj h).1]
  · have := (Prod.mk.inj h).1; omega
  · have := (Prod.mk.inj h).1; omega
  · obtain ⟨hphase, hor⟩ := Prod.mk.inj h
    apply leftWord_eq
    · intro k _
      rw [center_phase per (a + k) (by omega), center_phase per (b + k) (by omega)]
      congr 2
      have h1 : (a + k - T) % P = ((a - T) % P + k % P) % P := by rw [show a + k - T = (a - T) + k by omega, Nat.add_mod]
      have h2 : (b + k - T) % P = ((b - T) % P + k % P) % P := by rw [show b + k - T = (b - T) + k by omega, Nat.add_mod]
      rw [h1, h2, show (a - T) % P = (b - T) % P by omega]
    · exact fun k hk => segment_at hor k hk
noncomputable def keyListStrip (T P m : Nat) : List (Nat × List Bool) :=
  (List.range T).map (fun t => (t, [])) ++
    (List.range P).flatMap (fun p =>
      (dfaWords 0 (segment (fun i => cell i 0) (T + p) (12 * m))).map (fun w => (T + p, w)))
theorem keyStrip_mem {T P m : Nat} (hp : 0 < P) (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (t : Nat) : keyStrip T P m t ∈ keyListStrip T P m := by
  unfold keyStrip keyListStrip
  by_cases ht : t < T
  · simp only [ht, ↓reduceIte]; exact List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  · simp only [ht, ↓reduceIte]; apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨(t - T) % P, List.mem_range.mpr (Nat.mod_lt _ hp), ?_⟩
    refine List.mem_map.mpr ⟨segment (orCol 0) t (12 * m), ?_, rfl⟩
    have obs := strip_or_words_mem seed t (12 * m)
    have e1 : segment (fun i => evol seed i 0 || evol seed i 1) t (12 * m) = segment (orCol 0) t (12 * m) := by
      apply segment_congr; intro k _; simp [orCol, evol_seed]
    have e2 : segment (fun i => evol seed i 0) t (12 * m) = segment (fun i => cell i 0) (T + (t - T) % P) (12 * m) := by
      apply segment_congr; intro k _
      rw [evol_seed, center_phase per (t + k) (by omega), center_phase per (T + (t - T) % P + k) (by omega)]
      congr 2; rw [show t + k - T = (t - T) + k by omega, show T + (t - T) % P + k - T = (t - T) % P + k by omega, Nat.mod_add_mod]
    rw [e1, e2] at obs; exact obs
theorem flatMap_scaled_length_le {β : Type} (A C : Nat) (l : List Nat) (f : Nat -> List β)
    (h : ∀ x, x ∈ l → A * (f x).length ≤ C) : A * (l.flatMap f).length ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.succ_mul]
    omega
theorem length_le_of_periodic_strip {T P : Nat} (hp : 0 < P)
    (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (m : Nat) (ts : List Nat)
    (hnd : (ts.map (fun t => leftWord t (12 * m))).Nodup) :
    16 * 2 ^ m * ts.length ≤ 16 * 2 ^ m * T + 147 * P * 21 ^ m := by
  have hk : (ts.map (keyStrip T P m)).Nodup := by
    rw [List.Nodup, List.pairwise_map] at hnd ⊢
    exact hnd.imp (fun hne heq => hne (leftWord_of_keyStrip per heq))
  have hsub : ts.map (keyStrip T P m) ⊆ keyListStrip T P m := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact keyStrip_mem hp per t
  have hlen : ts.length ≤ (keyListStrip T P m).length := by
    calc ts.length = (ts.map (keyStrip T P m)).length := (List.length_map _).symm
      _ ≤ (keyListStrip T P m).length := hk.length_le_of_subset hsub
  have hkl : 16 * 2 ^ m * (keyListStrip T P m).length ≤ 16 * 2 ^ m * T + P * (147 * 21 ^ m) := by
    unfold keyListStrip
    rw [List.length_append, List.length_map, List.length_range, Nat.mul_add]
    have hfm := flatMap_scaled_length_le (16 * 2 ^ m) (147 * 21 ^ m) (List.range P)
      (fun p => (dfaWords 0 (segment (fun i => cell i 0) (T + p) (12 * m))).map (fun w => (T + p, w)))
      (fun p _ => by rw [List.length_map]; exact strip_or_word_count m _ (segment_length _ _ _))
    rw [List.length_range] at hfm
    omega
  have hmul := Nat.mul_le_mul_left (16 * 2 ^ m) hlen
  have hcomm : 147 * P * 21 ^ m = P * (147 * 21 ^ m) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 147 P, Nat.mul_assoc]
  rw [hcomm]
  omega

theorem problem1_of_strip_rich_left
    (h : ∀ T P : Nat, 0 < P → ∃ m : Nat, ∃ ts : List Nat,
      (ts.map (fun t => leftWord t (12 * m))).Nodup ∧
      16 * 2 ^ m * T + 147 * P * 21 ^ m < 16 * 2 ^ m * ts.length) :
    Rule30Prize.Problem1 := by
  rintro ⟨T, P, hp, per⟩
  obtain ⟨m, ts, hnd, hlt⟩ := h T P hp
  have hb := length_le_of_periodic_strip hp (fun t ht => by simpa [Rule30Prize.center] using per t ht) m ts hnd
  omega
end Rule30LeftRichnessStripCert

namespace Rule30LeftRichness
open Rule30Jen Rule30MaskedJen Rule30Realization Rule30ZeroBoundaryBarriers

/-- Six-cell powerset automaton words compatible with a center trace from state q. -/
noncomputable abbrev dfaWords : Nat → List Bool → List (List Bool) := Rule30LeftRichnessStripCert.dfaWords

/-- Width-n word just left of the center at time t under rule g. -/
abbrev rLeftWord (g : Bool → Bool → Bool) (t n : Nat) : List Bool := Rule30LeftRichnessStripCert.rLeftWord g t n

/-- Length-n slice of a temporal sequence starting at time t. -/
abbrev stripSegment : (Nat → Bool) → Nat → Nat → List Bool := Rule30LeftRichnessStripCert.segment

/-- Every OR trace evol x i 0 || evol x i 1 belongs to dfaWords 0 of the center trace. -/
theorem strip_or_words_mem (x : Int → Bool) (t n : Nat) :
    stripSegment (fun i => evol x i 0 || evol x i 1) t n ∈
      dfaWords 0 (stripSegment (fun i => evol x i 0) t n) :=
  Rule30LeftRichnessStripCert.strip_or_words_mem x t n

/-- Every center word of length 12 * m admits at most (147 / 16) * (21 / 2) ^ m OR words in dfaWords 0. -/
theorem strip_or_word_count (m : Nat) (c : List Bool) (hc : c.length = 12 * m) :
    16 * 2 ^ m * (dfaWords 0 c).length ≤ 147 * 21 ^ m :=
  Rule30LeftRichnessStripCert.strip_or_word_count m c hc

/-- Under a center period P > 0 from T onward, pairwise distinct left words of width 12 * m
satisfy 16 * 2 ^ m * ts.length ≤ 16 * 2 ^ m * T + 147 * P * 21 ^ m. -/
theorem length_le_of_periodic_strip {T P : Nat} (hp : 0 < P)
    (per : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (m : Nat) (ts : List Nat)
    (hnd : (ts.map (fun t => leftWord t (12 * m))).Nodup) :
    16 * 2 ^ m * ts.length ≤ 16 * 2 ^ m * T + 147 * P * 21 ^ m :=
  Rule30LeftRichnessStripCert.length_le_of_periodic_strip hp per m ts hnd

/-- Problem 1 from six-cell strip left-word richness (21/2 bound). -/
theorem problem1_of_strip_rich_left
    (h : ∀ T P : Nat, 0 < P → ∃ m : Nat, ∃ ts : List Nat,
      (ts.map (fun t => leftWord t (12 * m))).Nodup ∧
      16 * 2 ^ m * T + 147 * P * 21 ^ m < 16 * 2 ^ m * ts.length) :
    Rule30Prize.Problem1 :=
  Rule30LeftRichnessStripCert.problem1_of_strip_rich_left h

/-- Exact 2 ^ m-step Frobenius identity for Rule 90. -/
theorem run90_step2m (m t : Nat) (p : Int) :
    Rule30Realization.run Rule30Realization.g90 (t + 2 ^ m) p =
      xor (Rule30Realization.run Rule30Realization.g90 t (p - (2 ^ m : Nat)))
        (Rule30Realization.run Rule30Realization.g90 t (p + (2 ^ m : Nat))) :=
  Rule30LeftRichnessStripCert.run90_step2m m t p

/-- Exact 2 ^ m-step Frobenius identity for Rule 150. -/
theorem run150_step2m (m t : Nat) (p : Int) :
    Rule30Realization.run Rule30Realization.g150 (t + 2 ^ m) p =
      xor (Rule30Realization.run Rule30Realization.g150 t (p - (2 ^ m : Nat)))
        (xor (Rule30Realization.run Rule30Realization.g150 t p)
          (Rule30Realization.run Rule30Realization.g150 t (p + (2 ^ m : Nat)))) :=
  Rule30LeftRichnessStripCert.run150_step2m m t p

/-- Singleton left words of width n ≥ 1 under Rule 90 number at most 4 * n. -/
theorem rule90_leftWords_le_4n {n : Nat} (hn : 1 ≤ n) (ts : List Nat)
    (hnd : (ts.map (fun t => rLeftWord Rule30Realization.g90 t n)).Nodup) : ts.length ≤ 4 * n :=
  Rule30LeftRichnessStripCert.rule90_leftWords_le_4n hn ts hnd

/-- Singleton left words of width n ≥ 1 under Rule 150 number at most 4 * n. -/
theorem rule150_leftWords_le_4n {n : Nat} (hn : 1 ≤ n) (ts : List Nat)
    (hnd : (ts.map (fun t => rLeftWord Rule30Realization.g150 t n)).Nodup) : ts.length ≤ 4 * n :=
  Rule30LeftRichnessStripCert.rule150_leftWords_le_4n hn ts hnd

/-- Singleton left words of width n ≥ 1 under Rule 210 number at most 4 * n. -/
theorem rule210_leftWords_le_4n {n : Nat} (hn : 1 ≤ n) (ts : List Nat)
    (hnd : (ts.map (fun t => rLeftWord Rule30Realization.g210 t n)).Nodup) : ts.length ≤ 4 * n :=
  Rule30LeftRichnessStripCert.rule210_leftWords_le_4n hn ts hnd

end Rule30LeftRichness

end Ruliology.CellularAutomata
