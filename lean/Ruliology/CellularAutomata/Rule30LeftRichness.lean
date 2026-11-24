module

public import Ruliology.CellularAutomata.Rule30MaskedForkRate

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
six-cell strip certificate lowers `1/2` to `log₂(32/3)/12 ≈ 0.2846` bit per cell; that finite
certificate (4594 reachable strip states, all 12-bit center words) is not formalized here. For
rules 90, 150 and 210 the singleton's left words number fewer than `8 n`, so a proof of the
richness hypothesis must use the OR of rule 30. The hypothesis is open.

Contributed by Katip Kurtuluş with Claude (Anthropic), ChatGPT (OpenAI) and Gemini (Google).
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
end Ruliology.CellularAutomata
