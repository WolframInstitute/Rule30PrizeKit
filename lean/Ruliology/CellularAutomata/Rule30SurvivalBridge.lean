module

public import Ruliology.CellularAutomata.Rule30LeftAntiPeriod

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# A repeat budget is mortality of the auxiliary frontier

A finite frontier is a word over `{0,1,2,3}`, stored as bit pairs `(a, b)` with `w_i = 2 a_i + b_i`.
It is the pair of adjacent anti-diagonals of a Rule 30 space-time diagram read from a row with a
leftmost black cell (see `Rule30AlternatingTraceBridge`). `Z` is the partial update on frontiers: a
left-to-right scan that succeeds exactly when its final `u` and `v` agree, emits that common value as
the scalar and appends the birth symbol `(1, 1 XOR s)`. `run` iterates `Z` and keeps every earlier
guard, which is the chronological-guard condition. A frontier is *mortal* when its run eventually
fails a guard.

Proved, for every legal frontier and with no finite computation assumed:

* `reconstruction`: after `n` updates the bit at depth `d` is the formal field of the emitted scalars
  once `n ≥ 1 + floor(d/2)` (high) or `1 + ceil(d/2)` (low), and one step earlier from an onset whose
  terminal high bit is one;
* `runBound`: a run with no repeated scalar from length `a` has length at most `a + 3`, and at most
  `a + 1` when the terminal high bit is one. The period-28 table behind it is evaluated inside the
  kernel by `decide`;
* `survival`: `r + N + 1 ≤ 2^(D+1) (r + 2)` on every successful prefix;
* `budgetAt_iff_mortalAt`, `budget_iff_mortality`: a repeat budget at length `r` is mortality at
  length `r`, in both directions;
* `mortality_of_capacity_budget`: a repeat bound at every capacity `K` gives mortality, for every
  capacity function `Q` at once.

Control, `survival_counting_fails_without_runBound`: the counting inequality is false for tapes in
general, so the run bound is what carries it.

Relation to `Rule30PeriodTwo.Q01`: mortality implies `Q01`
(`Rule30AlternatingTraceBridge.Q01_of_mortality`, which has the proof). The converse is not proved and
not known: mortality quantifies over every legal frontier, including ones not read off any left half.
So a repeat budget, being equivalent to mortality, is at least as strong a target as `Q01`.

Nothing here proves a budget, a capacity bound or mortality, and nothing here bounds the center
column of Rule 30; Problems 1 to 3 stay open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30SurvivalBridge

open Rule30Prize Rule30Diagonals Rule30LeftReset Rule30LeftUnbounded Rule30LeftAntiPeriod


/-- A frontier symbol `w_i = 2 a_i + b_i`, stored as `(a_i, b_i)`, high bit first. -/
abbrev Sym := Bool × Bool

/-- A frontier is legal when it is nonempty and `a_0 = 1`. -/
def Legal : List Sym → Prop
  | [] => False
  | s :: _ => s.1 = true

/-- Scan memory `(u, v, alpha)`. One step on the symbol `(a, b)`:
`v' = v XOR (alpha OR b)`, then `u' = u XOR (v' OR a)`, and the memory becomes `(u', v', a)`. -/
def scanStep (m : Bool × Bool × Bool) (s : Sym) : Bool × Bool × Bool :=
  let v' := xor m.2.1 (m.2.2 || s.2)
  let u' := xor m.1 (v' || s.1)
  (u', v', s.1)

/-- Left-to-right scan: the emitted symbols `(u', v')` and the final memory. -/
def scan : Bool × Bool × Bool → List Sym → List Sym × (Bool × Bool × Bool)
  | m, [] => ([], m)
  | m, s :: w =>
    let m' := scanStep m s
    let r := scan m' w
    ((m'.1, m'.2.1) :: r.1, r.2)

/-- The partial update `Z`. It succeeds exactly when the final `u` and `v` agree; their common
value `s` is the terminal scalar, and the birth symbol `(1, 1 XOR s)` is appended. -/
def Z (w : List Sym) : Option (List Sym × Bool) :=
  let r := scan (false, false, false) w
  if r.2.1 = r.2.2.1 then some (r.1 ++ [(true, !r.2.2.1)], r.2.2.1) else none

/-- `run w N = some (w', tape)`: `N` successive updates all pass their guard, `w'` is the
frontier reached and `tape` lists the scalars in emission order. `none` once a guard fails. -/
def run (w : List Sym) : Nat → Option (List Sym × List Bool)
  | 0 => some (w, [])
  | n + 1 =>
    match run w n with
    | none => none
    | some (w', t) =>
      match Z w' with
      | none => none
      | some (w'', s) => some (w'', t ++ [s])

/-- `D`: the number of equal adjacent scalars in a tape. -/
def repeats : List Bool → Nat
  | a :: b :: t => (if a = b then 1 else 0) + repeats (b :: t)
  | _ => 0

/-- The high bit of the last symbol. -/
def terminalHigh (w : List Sym) : Bool :=
  match w.getLast? with
  | some s => s.1
  | none => false

/-- Formal scalar-history fields. `W j` is the scalar emitted `j` updates ago.
`F 0 = 1`, `F 1 = W`, `F d j = F (d-1) j XOR (G (d-1) j OR F (d-2) (j+1))`;
`G 0 = 1 XOR W`, `G 1 = W`, `G d j = G (d-1) j XOR (F (d-1) (j+1) OR G (d-2) (j+1))`. -/
def FG (W : Nat → Bool) : Nat → Nat → Bool × Bool
  | 0, j => (true, !W j)
  | 1, j => (W j, W j)
  | d + 2, j =>
    (xor (FG W (d + 1) j).1 ((FG W (d + 1) j).2 || (FG W d (j + 1)).1),
     xor (FG W (d + 1) j).2 ((FG W (d + 1) (j + 1)).1 || (FG W d (j + 1)).2))

/-- The window of a tape: the scalar emitted `j` updates ago, `false` beyond the tape. -/
def window (tape : List Bool) (j : Nat) : Bool := tape.reverse.getD j false

/-- The symbol at depth `d`, counted inward from the terminal end. -/
def atDepth (w : List Sym) (d : Nat) : Sym := w.reverse.getD d (false, false)

/-- Reconstruction thresholds. After `n` successful updates from a legal frontier, the high bit
at an existing depth `d` equals `F d 0` once `n ≥ 1 + floor(d/2)` and the low bit equals
`G d 0` once `n ≥ 1 + ceil(d/2)`. From an onset with terminal high bit one the thresholds are
`n ≥ ceil(d/2)` and `n ≥ 1 + floor(d/2)`. -/
def Reconstruction : Prop :=
  ∀ (w w' : List Sym) (n : Nat) (tape : List Bool), Legal w → run w n = some (w', tape) →
    ∀ d, d < w'.length →
      ((1 + d / 2 ≤ n ∨ (terminalHigh w = true ∧ (d + 1) / 2 ≤ n)) →
        (atDepth w' d).1 = (FG (window tape) d 0).1) ∧
      ((1 + (d + 1) / 2 ≤ n ∨ (terminalHigh w = true ∧ 1 + d / 2 ≤ n)) →
        (atDepth w' d).2 = (FG (window tape) d 0).2)

/-- Alternating-run bounds: a run with no repeated scalar from a legal frontier of length `a`
has length at most `a + 3`, and at most `a + 1` when the terminal high bit is one. -/
def RunBound : Prop :=
  ∀ (w w' : List Sym) (L : Nat) (tape : List Bool), Legal w → run w L = some (w', tape) →
    repeats tape = 0 →
      L ≤ w.length + 3 ∧ (terminalHigh w = true → L ≤ w.length + 1)

/-- The survival inequality `r + N + 1 ≤ 2^(D+1) (r + 2)`, and `(r + 1)` in place of `(r + 2)`
when the terminal high bit is one, on every successful prefix. -/
def Survival : Prop :=
  ∀ (w w' : List Sym) (N : Nat) (tape : List Bool), Legal w → 1 ≤ N →
    run w N = some (w', tape) →
      w.length + N + 1 ≤ 2 ^ (repeats tape + 1) * (w.length + 2) ∧
      (terminalHigh w = true → w.length + N + 1 ≤ 2 ^ (repeats tape + 1) * (w.length + 1))

/-- A repeat budget at length `r`: one `B` bounds `D` on every successful tape of every legal
frontier of length `r`. -/
def BudgetAt (r : Nat) : Prop :=
  ∃ B : Nat, ∀ (w w' : List Sym) (N : Nat) (tape : List Bool), Legal w → w.length = r →
    run w N = some (w', tape) → repeats tape ≤ B

/-- Mortality at length `r`: every legal frontier of length `r` eventually fails a guard. -/
def MortalAt (r : Nat) : Prop :=
  ∀ w : List Sym, Legal w → w.length = r → ∃ N : Nat, run w N = none

/-- Mortality: every legal finite frontier eventually fails a chronological guard. -/
def Mortality : Prop := ∀ w : List Sym, Legal w → ∃ N : Nat, run w N = none

/-! ## Reconstruction thresholds -/

/-
Proof of `Reconstruction`. Write A_d(n), B_d(n) for the bits of `atDepth` at depth d after n
successful updates, s for the scalar of the last update, out for the emitted symbols of its scan.
(1) Z w = some (w2, s) gives w2 = out ++ [(1, !s)], so atDepth w2 0 = (1, !s), and the last
    emitted symbol is the final (u, v) = (s, s), so atDepth w2 1 = (s, s) when w is nonempty
    (`scan_last`, `Z_depth`).
(2) Adjacent scan sites k, k+1 satisfy u_k = u_(k+1) XOR (v_(k+1) OR a_(k+1)) and
    v_k = v_(k+1) XOR (a_k OR b_(k+1)). Site k+1 has depth d in out and in w, site k depth d+1,
    and out sits one deeper in w2, which is `scan_depth_rec` and the last clause of `Z_depth`:
    A_(d+2)(n+1) = A_(d+1)(n+1) XOR (B_(d+1)(n+1) OR A_d(n)),
    B_(d+2)(n+1) = B_(d+1)(n+1) XOR (A_(d+1)(n) OR B_d(n)).
(3) FG W d (j+1) = FG (W o succ) d j (`FG_shift`) and window (t ++ [s]) o succ = window t, so
    FG (window (t ++ [s])) d (j+1) = FG (window t) d j with no side condition
    (`FG_window_snoc`). The junk value `false` beyond the tape is therefore never compared.
(4) `recon_aux`: induction on n, inside it a two-step induction on d. The threshold of
    A_(d+2)(n+1) is that of A_d(n) and implies those of A_(d+1)(n+1), B_(d+1)(n+1); the threshold
    of B_(d+2)(n+1) is that of B_d(n) and implies those of B_(d+1)(n+1), A_(d+1)(n). Base n = 0:
    only the terminal-high clause at d = 0 is satisfiable, and A_0(0) = terminalHigh w.
`Legal w` is not used.
-/

theorem atDepth_cons_lt (s : Sym) (w : List Sym) (d : Nat) (h : d < w.length) :
    atDepth (s :: w) d = atDepth w d := by
  unfold atDepth
  rw [List.reverse_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using h)]

theorem atDepth_cons_eq (s : Sym) (w : List Sym) : atDepth (s :: w) w.length = s := by
  unfold atDepth
  rw [List.reverse_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem atDepth_snoc_zero (w : List Sym) (x : Sym) : atDepth (w ++ [x]) 0 = x := by
  simp [atDepth]

theorem atDepth_snoc_succ (w : List Sym) (x : Sym) (d : Nat) :
    atDepth (w ++ [x]) (d + 1) = atDepth w d := by
  simp [atDepth]

theorem atDepth_zero_fst (w : List Sym) : (atDepth w 0).1 = terminalHigh w := by
  unfold atDepth terminalHigh
  rw [List.getLast?_eq_head?_reverse]
  cases w.reverse <;> simp

theorem scan_length (m : Bool × Bool × Bool) (w : List Sym) : (scan m w).1.length = w.length := by
  induction w generalizing m with
  | nil => simp [scan]
  | cons s w ih => simp [scan, ih]

theorem atDepth_cons_eq' (s : Sym) (w : List Sym) (d : Nat) (h : d = w.length) :
    atDepth (s :: w) d = s := by
  subst h; exact atDepth_cons_eq s w

theorem scan_cons (m : Bool × Bool × Bool) (s : Sym) (w : List Sym) :
    scan m (s :: w) =
      (((scanStep m s).1, (scanStep m s).2.1) :: (scan (scanStep m s) w).1,
        (scan (scanStep m s) w).2) := rfl

theorem scan_last (m : Bool × Bool × Bool) (w : List Sym) (h : w ≠ []) :
    atDepth (scan m w).1 0 = ((scan m w).2.1, (scan m w).2.2.1) := by
  induction w generalizing m with
  | nil => exact absurd rfl h
  | cons s w ih =>
    cases w with
    | nil => simp [scan, atDepth]
    | cons s' w'' =>
      rw [scan_cons]
      rw [atDepth_cons_lt _ _ 0 (by rw [scan_length]; simp)]
      exact ih (scanStep m s) (by simp)

theorem scan_depth_rec (m : Bool × Bool × Bool) (w : List Sym) (d : Nat) (h : d + 1 < w.length) :
    atDepth (scan m w).1 (d + 1) =
      (xor (atDepth (scan m w).1 d).1 ((atDepth (scan m w).1 d).2 || (atDepth w d).1),
       xor (atDepth (scan m w).1 d).2 ((atDepth w (d + 1)).1 || (atDepth w d).2)) := by
  induction w generalizing m with
  | nil => simp at h
  | cons s w ih =>
    rw [scan_cons]
    have hlen : (scan (scanStep m s) w).1.length = w.length := scan_length _ _
    by_cases hd : d + 1 < w.length
    · rw [atDepth_cons_lt _ _ (d + 1) (by omega), atDepth_cons_lt _ _ d (by omega),
        atDepth_cons_lt _ _ (d + 1) hd, atDepth_cons_lt _ _ d (by omega)]
      exact ih (scanStep m s) hd
    · have hd' : d + 1 = w.length := by simp at h; omega
      cases w with
      | nil => simp at hd'
      | cons s' w'' =>
        have hd'' : d = w''.length := by simp at hd'; omega
        rw [scan_cons]
        have hlen2 : (scan (scanStep (scanStep m s) s') w'').1.length = w''.length :=
          scan_length _ _
        rw [atDepth_cons_eq' _ _ (d + 1) (by simp; omega),
          atDepth_cons_lt _ _ d (by simp; omega),
          atDepth_cons_eq' _ _ d (by omega),
          atDepth_cons_eq' _ _ (d + 1) (by simp; omega),
          atDepth_cons_lt _ _ d (by simp; omega),
          atDepth_cons_eq' _ _ d hd'']
        obtain ⟨u, v, al⟩ := m
        obtain ⟨a, b⟩ := s
        obtain ⟨a', b'⟩ := s'
        simp only [scanStep]
        cases u <;> cases v <;> cases al <;> cases a <;> cases b <;> cases a' <;> cases b' <;> rfl

theorem Z_spec (w w2 : List Sym) (s : Bool) (h : Z w = some (w2, s)) :
    w2 = (scan (false, false, false) w).1 ++ [(true, !s)] ∧
      (scan (false, false, false) w).2.1 = s ∧ (scan (false, false, false) w).2.2.1 = s := by
  unfold Z at h
  simp only at h
  split at h
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h2] at heq h1
    exact ⟨h1.symm, heq, h2⟩
  · simp at h

theorem FG_shift (W : Nat → Bool) (d : Nat) :
    (∀ j, FG W d (j + 1) = FG (fun i => W (i + 1)) d j) ∧
      (∀ j, FG W (d + 1) (j + 1) = FG (fun i => W (i + 1)) (d + 1) j) := by
  induction d with
  | zero => exact ⟨fun j => by simp [FG], fun j => by simp [FG]⟩
  | succ d ih =>
    refine ⟨ih.2, fun j => ?_⟩
    rw [FG, FG, ih.2 j, ih.2 (j + 1), ih.1 (j + 1)]

theorem window_snoc_zero (t : List Bool) (s : Bool) : window (t ++ [s]) 0 = s := by
  simp [window]

theorem window_snoc_succ (t : List Bool) (s : Bool) (i : Nat) :
    window (t ++ [s]) (i + 1) = window t i := by
  simp [window]

theorem FG_window_snoc (t : List Bool) (s : Bool) (d j : Nat) :
    FG (window (t ++ [s])) d (j + 1) = FG (window t) d j := by
  rw [(FG_shift (window (t ++ [s])) d).1 j]
  have : (fun i => window (t ++ [s]) (i + 1)) = window t := by
    funext i; exact window_snoc_succ t s i
  rw [this]

theorem run_succ_some (w w2 : List Sym) (n : Nat) (tape2 : List Bool)
    (h : run w (n + 1) = some (w2, tape2)) :
    ∃ w' t s, run w n = some (w', t) ∧ Z w' = some (w2, s) ∧ tape2 = t ++ [s] := by
  rw [run] at h
  cases hr : run w n with
  | none => rw [hr] at h; simp at h
  | some p =>
    obtain ⟨w', t⟩ := p
    rw [hr] at h
    simp only at h
    cases hz : Z w' with
    | none => rw [hz] at h; simp at h
    | some q =>
      obtain ⟨w3, s⟩ := q
      rw [hz] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      exact ⟨w', t, s, rfl, hz, h2.symm⟩

/-- The terminal pattern and the depth recurrences of one successful update. -/
theorem Z_depth (w w2 : List Sym) (s : Bool) (h : Z w = some (w2, s)) :
    w2.length = w.length + 1 ∧
    atDepth w2 0 = (true, !s) ∧
    (w ≠ [] → atDepth w2 1 = (s, s)) ∧
    (∀ d, d + 1 < w.length →
      atDepth w2 (d + 2) =
        (xor (atDepth w2 (d + 1)).1 ((atDepth w2 (d + 1)).2 || (atDepth w d).1),
         xor (atDepth w2 (d + 1)).2 ((atDepth w (d + 1)).1 || (atDepth w d).2))) := by
  obtain ⟨h1, h2, h3⟩ := Z_spec w w2 s h
  subst h1
  refine ⟨by simp [scan_length], atDepth_snoc_zero _ _, fun hne => ?_, fun d hd => ?_⟩
  · rw [atDepth_snoc_succ, scan_last _ _ hne, h2, h3]
  · rw [atDepth_snoc_succ, atDepth_snoc_succ, scan_depth_rec _ _ _ hd]

theorem recon_aux (w : List Sym) :
    ∀ (n : Nat) (w' : List Sym) (tape : List Bool), run w n = some (w', tape) →
      ∀ d, d < w'.length →
        ((1 + d / 2 ≤ n ∨ (terminalHigh w = true ∧ (d + 1) / 2 ≤ n)) →
          (atDepth w' d).1 = (FG (window tape) d 0).1) ∧
        ((1 + (d + 1) / 2 ≤ n ∨ (terminalHigh w = true ∧ 1 + d / 2 ≤ n)) →
          (atDepth w' d).2 = (FG (window tape) d 0).2) := by
  intro n
  induction n with
  | zero =>
    intro w' tape hrun d hd
    simp only [run, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun
    subst h1
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rcases hc with hc | ⟨hT, hc⟩
      · omega
      · have hd0 : d = 0 := by omega
        subst hd0
        rw [atDepth_zero_fst, hT]
        simp [FG]
    · rcases hc with hc | ⟨hT, hc⟩ <;> omega
  | succ n ih =>
    intro w2 tape2 hrun
    obtain ⟨w', t, s, hrn, hz, htape⟩ := run_succ_some w w2 n tape2 hrun
    subst htape
    obtain ⟨hlen, hz0, hz1, hzrec⟩ := Z_depth w' w2 s hz
    have hW0 : window (t ++ [s]) 0 = s := window_snoc_zero t s
    have key : ∀ d,
        (d < w2.length →
          ((1 + d / 2 ≤ n + 1 ∨ (terminalHigh w = true ∧ (d + 1) / 2 ≤ n + 1)) →
            (atDepth w2 d).1 = (FG (window (t ++ [s])) d 0).1) ∧
          ((1 + (d + 1) / 2 ≤ n + 1 ∨ (terminalHigh w = true ∧ 1 + d / 2 ≤ n + 1)) →
            (atDepth w2 d).2 = (FG (window (t ++ [s])) d 0).2)) ∧
        (d + 1 < w2.length →
          ((1 + (d + 1) / 2 ≤ n + 1 ∨ (terminalHigh w = true ∧ (d + 1 + 1) / 2 ≤ n + 1)) →
            (atDepth w2 (d + 1)).1 = (FG (window (t ++ [s])) (d + 1) 0).1) ∧
          ((1 + (d + 1 + 1) / 2 ≤ n + 1 ∨ (terminalHigh w = true ∧ 1 + (d + 1) / 2 ≤ n + 1)) →
            (atDepth w2 (d + 1)).2 = (FG (window (t ++ [s])) (d + 1) 0).2)) := by
      intro d
      induction d with
      | zero =>
        refine ⟨fun _ => ?_, fun hd => ?_⟩
        · rw [hz0, FG, hW0]; exact ⟨fun _ => rfl, fun _ => rfl⟩
        · have hne : w' ≠ [] := by
            intro h0; subst h0; simp at hlen; omega
          rw [hz1 hne, FG, hW0]; exact ⟨fun _ => rfl, fun _ => rfl⟩
      | succ d ihd =>
        refine ⟨ihd.2, fun hd => ?_⟩
        have hd' : d + 1 < w'.length := by omega
        have hq1 := ihd.2 (by omega)
        have hp0 := ih w' t hrn d (by omega)
        have hp1 := ih w' t hrn (d + 1) hd'
        rw [hzrec d hd', FG, FG_window_snoc, FG_window_snoc]
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · have e1 : (atDepth w2 (d + 1)).1 = (FG (window (t ++ [s])) (d + 1) 0).1 := by
            apply hq1.1
            rcases hc with hc | ⟨hT, hc⟩
            · left; omega
            · right; exact ⟨hT, by omega⟩
          have e2 : (atDepth w2 (d + 1)).2 = (FG (window (t ++ [s])) (d + 1) 0).2 := by
            apply hq1.2
            rcases hc with hc | ⟨hT, hc⟩
            · left; omega
            · right; exact ⟨hT, by omega⟩
          have e3 : (atDepth w' d).1 = (FG (window t) d 0).1 := by
            apply hp0.1
            rcases hc with hc | ⟨hT, hc⟩
            · left; omega
            · right; exact ⟨hT, by omega⟩
          simp only [e1, e2, e3]
        · have e1 : (atDepth w2 (d + 1)).2 = (FG (window (t ++ [s])) (d + 1) 0).2 := by
            apply hq1.2
            rcases hc with hc | ⟨hT, hc⟩
            · left; omega
            · right; exact ⟨hT, by omega⟩
          have e2 : (atDepth w' (d + 1)).1 = (FG (window t) (d + 1) 0).1 := by
            apply hp1.1
            rcases hc with hc | ⟨hT, hc⟩
            · left; omega
            · right; exact ⟨hT, by omega⟩
          have e3 : (atDepth w' d).2 = (FG (window t) d 0).2 := by
            apply hp0.2
            rcases hc with hc | ⟨hT, hc⟩
            · left; omega
            · right; exact ⟨hT, by omega⟩
          simp only [e1, e2, e3]
    intro d hd
    exact (key d).1 hd

theorem reconstruction : Reconstruction := by
  intro w w' n tape _ hrun d hd
  exact recon_aux w n w' tape hrun d hd

/-! ## Alternating-run bounds -/

/-
Proof plan.
1. Run bookkeeping: a successful run of length n+1 is a successful run of length n followed by
   one successful Z, the tape grows by a snoc; Z keeps Legal, keeps site 0 and adds one symbol.
2. A tape with no repeat is alternating, so its window agrees below the tape length with the
   genuinely alternating signal `alt c`, c the last scalar.
3. Dependency: (FG W d j).1 reads W i only for j <= i < j + (d+1)/2 and (FG W d j).2 only for
   j <= i < j + 1 + d/2. At time n >= a and depth d = a+n-1 both bounds are <= n.
4. For the alternating signal, A c d = FG (alt c) d 0 obeys a closed two-row recurrence coupling
   the phases c and !c; the four-symbol state has period 28 (decide), so A c d = A c (d % 28).
5. Finite facts over one period (decide): no four consecutive depths, and no three consecutive
   depths from an odd depth, carry (true, beta) along the phase-alternating diagonal.
6. Reconstruction pins site 0, which is (true, beta) forever, to A (last scalar) (a+n-1).
-/

/-! ### Scan, Z and run bookkeeping -/

def hd (w : List Sym) : Sym := w.headD (false, false)

theorem scan_length_Rb : ∀ (w : List Sym) (m : Bool × Bool × Bool), (scan m w).1.length = w.length
  | [], _ => rfl
  | s :: w, m => by simp [scan, scan_length_Rb w]

theorem Z_some {w w' : List Sym} {s : Bool} (h : Z w = some (w', s)) :
    w' = (scan (false, false, false) w).1 ++ [(true, !s)] := by
  unfold Z at h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]
  · cases h

theorem Z_inv {w w' : List Sym} {s : Bool} (hl : Legal w) (h : Z w = some (w', s)) :
    Legal w' ∧ hd w' = hd w ∧ w'.length = w.length + 1 := by
  have hw := Z_some h
  subst hw
  refine ⟨?_, ?_, ?_⟩
  · cases w with
    | nil => exact hl.elim
    | cons x rest =>
      obtain ⟨xa, xb⟩ := x
      simp only [Legal] at hl
      subst hl
      simp [scan, scanStep, Legal]
  · cases w with
    | nil => exact hl.elim
    | cons x rest =>
      obtain ⟨xa, xb⟩ := x
      simp only [Legal] at hl
      subst hl
      simp [scan, scanStep, hd]
  · simp [scan_length_Rb]

theorem run_succ_some_Rb {w w'' : List Sym} {n : Nat} {t'' : List Bool}
    (h : run w (n + 1) = some (w'', t'')) :
    ∃ w' t s, run w n = some (w', t) ∧ Z w' = some (w'', s) ∧ t'' = t ++ [s] := by
  simp only [run] at h
  split at h
  · cases h
  · rename_i w' t hrun
    split at h
    · cases h
    · rename_i w2 s hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨w', t, s, hrun, by rw [hz, h.1], h.2.symm⟩

theorem run_inv {w : List Sym} (hl : Legal w) :
    ∀ (n : Nat) (w' : List Sym) (t : List Bool), run w n = some (w', t) →
      Legal w' ∧ hd w' = hd w ∧ w'.length = w.length + n
  | 0, w', t, h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact ⟨hl, rfl, rfl⟩
  | n + 1, w'', t'', h => by
    obtain ⟨w', t, s, hrun, hz, _⟩ := run_succ_some_Rb h
    obtain ⟨h1, h2, h3⟩ := run_inv hl n w' t hrun
    obtain ⟨g1, g2, g3⟩ := Z_inv h1 hz
    exact ⟨g1, g2.trans h2, by omega⟩

theorem run_prefix {w : List Sym} (m : Nat) :
    ∀ (k : Nat) (w' : List Sym) (tape : List Bool), run w (m + k) = some (w', tape) →
      ∃ w1 t1 t2, run w m = some (w1, t1) ∧ tape = t1 ++ t2
  | 0, w', tape, h => ⟨w', tape, [], h, by simp⟩
  | k + 1, w', tape, h => by
    obtain ⟨w2, t, s, hrun, _, ht⟩ := run_succ_some_Rb (n := m + k) h
    obtain ⟨w1, t1, t2, h1, h2⟩ := run_prefix m k w2 t hrun
    exact ⟨w1, t1, t2 ++ [s], h1, by rw [ht, h2, List.append_assoc]⟩

/-! ### Tapes without repeats -/

theorem repeats_append_left : ∀ (t u : List Bool), repeats (t ++ u) = 0 → repeats t = 0
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: t, u, h => by
    have ih := repeats_append_left (b :: t) u
    simp only [List.cons_append, repeats] at h ih ⊢
    omega

theorem repeats_snoc2 : ∀ (t : List Bool) (y x : Bool), repeats (t ++ [y] ++ [x]) = 0 → x = !y
  | [], y, x, h => by
    simp only [List.nil_append, List.cons_append, repeats] at h
    cases x <;> cases y <;> simp_all
  | [a], y, x, h => by
    have ih := repeats_snoc2 [] y x
    simp only [List.nil_append, List.cons_append, repeats] at h ih
    exact ih (by omega)
  | a :: b :: t, y, x, h => by
    have ih := repeats_snoc2 (b :: t) y x
    simp only [List.cons_append, repeats] at h ih
    exact ih (by omega)

theorem window_snoc_zero_Rb (t : List Bool) (s : Bool) : window (t ++ [s]) 0 = s := by
  simp [window]

theorem window_snoc_succ_Rb (t : List Bool) (s : Bool) (i : Nat) :
    window (t ++ [s]) (i + 1) = window t i := by
  simp [window]

/-- One step back along a repeat-free run: the shorter run is repeat-free and the last scalar
flips. -/
theorem run_pred {w w'' : List Sym} {n : Nat} {t'' : List Bool}
    (h : run w (n + 1) = some (w'', t'')) (hrep : repeats t'' = 0) :
    ∃ w' t, run w n = some (w', t) ∧ repeats t = 0 ∧ (1 ≤ n → window t'' 0 = !(window t 0)) := by
  obtain ⟨w', t, s, hrun, _, ht⟩ := run_succ_some_Rb h
  subst ht
  refine ⟨w', t, hrun, repeats_append_left _ _ hrep, ?_⟩
  intro hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨_, t0, y, _, _, ht0⟩ := run_succ_some_Rb hrun
  subst ht0
  rw [window_snoc_zero_Rb, window_snoc_zero_Rb]
  exact repeats_snoc2 t0 y s hrep

/-- The genuinely alternating signal with value `c` at index 0. -/
def alt (c : Bool) : Nat → Bool
  | 0 => c
  | j + 1 => alt (!c) j

theorem run_alt {w : List Sym} :
    ∀ (n : Nat) (w' : List Sym) (t : List Bool), run w n = some (w', t) → repeats t = 0 →
      ∀ i, i < n → window t i = alt (window t 0) i
  | 0, _, _, _, _, i, hi => by omega
  | n + 1, w'', t'', h, hrep, i, hi => by
    cases i with
    | zero => rfl
    | succ i =>
      obtain ⟨w', t, hrun, hrep', hflip⟩ := run_pred h hrep
      obtain ⟨_, t1, s, hrun1, _, ht⟩ := run_succ_some_Rb h
      have hflip' := hflip (by omega)
      have ih := run_alt n w' t hrun hrep' i (by omega)
      have e : t1 = t := by
        rw [hrun] at hrun1
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun1
        exact hrun1.2.symm
      subst e
      subst ht
      rw [window_snoc_succ_Rb, ih]
      rw [window_snoc_zero_Rb] at hflip' ⊢
      rw [hflip']
      simp [alt]

/-! ### Dependency of the formal fields on the window -/

theorem FG_dep (W W' : Nat → Bool) (m : Nat) (h : ∀ i, i < m → W i = W' i) :
    ∀ d j, (j + (d + 1) / 2 ≤ m → (FG W d j).1 = (FG W' d j).1) ∧
           (j + 1 + d / 2 ≤ m → (FG W d j).2 = (FG W' d j).2)
  | 0, j => ⟨fun _ => rfl, fun hj => by simp only [FG]; rw [h j (by omega)]⟩
  | 1, j => ⟨fun hj => by simp only [FG]; exact h j (by omega),
             fun hj => by simp only [FG]; exact h j (by omega)⟩
  | d + 2, j => by
    have h1 := FG_dep W W' m h (d + 1) j
    have h2 := FG_dep W W' m h d (j + 1)
    have h3 := FG_dep W W' m h (d + 1) (j + 1)
    constructor
    · intro hj
      simp only [FG]
      rw [h1.1 (by omega), h1.2 (by omega), h2.1 (by omega)]
    · intro hj
      simp only [FG]
      rw [h1.2 (by omega), h3.1 (by omega), h2.2 (by omega)]

/-! ### The alternating closed form and its period -/

theorem FG_alt_shift : ∀ (d j : Nat) (c : Bool), FG (alt c) d (j + 1) = FG (alt (!c)) d j
  | 0, j, c => by simp only [FG, alt]
  | 1, j, c => by simp only [FG, alt]
  | d + 2, j, c => by
    simp only [FG]
    rw [FG_alt_shift (d + 1) j c, FG_alt_shift d (j + 1) c, FG_alt_shift (d + 1) (j + 1) c]

/-- The field pair at depth `d`, position 0, for the alternating signal of phase `c`. -/
def A (c : Bool) (d : Nat) : Sym := FG (alt c) d 0

theorem A_rec (c : Bool) (d : Nat) :
    A c (d + 2) =
      (xor (A c (d + 1)).1 ((A c (d + 1)).2 || (A (!c) d).1),
       xor (A c (d + 1)).2 ((A (!c) (d + 1)).1 || (A (!c) d).2)) := by
  simp only [A, FG]
  rw [FG_alt_shift d 0 c, FG_alt_shift (d + 1) 0 c]


def stepSt (s : (Sym × Sym) × (Sym × Sym)) : (Sym × Sym) × (Sym × Sym) :=
  (s.2,
   ((xor s.2.1.1 (s.2.1.2 || s.1.2.1), xor s.2.1.2 (s.2.2.1 || s.1.2.2)),
    (xor s.2.2.1 (s.2.2.2 || s.1.1.1), xor s.2.2.2 (s.2.1.1 || s.1.1.2))))

def st : Nat → (Sym × Sym) × (Sym × Sym)
  | 0 => (((true, true), (true, false)), ((false, false), (true, true)))
  | d + 1 => stepSt (st d)

def sel (c : Bool) (s : (Sym × Sym) × (Sym × Sym)) : Sym := if c then s.1.2 else s.1.1

theorem st_spec : ∀ d, st d = ((A false d, A true d), (A false (d + 1), A true (d + 1)))
  | 0 => by simp [st, A, FG, alt]
  | d + 1 => by
    rw [st, st_spec d, A_rec false d, A_rec true d]
    simp [stepSt]

theorem A_eq_sel (c : Bool) (d : Nat) : A c d = sel c (st d) := by
  rw [st_spec d]
  cases c <;> simp [sel]

theorem st_28 : st 28 = st 0 := by decide

theorem st_period : ∀ d, st (d + 28) = st d
  | 0 => st_28
  | d + 1 => by
    have e : d + 1 + 28 = (d + 28) + 1 := by omega
    rw [e, st, st_period d, st]

theorem st_add_mul (r : Nat) : ∀ q, st (r + 28 * q) = st r
  | 0 => rfl
  | q + 1 => by
    have e : r + 28 * (q + 1) = (r + 28 * q) + 28 := by omega
    rw [e, st_period, st_add_mul r q]

theorem A_mod (c : Bool) (d k : Nat) : A c (d + k) = sel c (st (d % 28 + k)) := by
  rw [A_eq_sel]
  have e : d + k = (d % 28 + k) + 28 * (d / 28) := by omega
  rw [e, st_add_mul]

/-- Fact A over one period: no four consecutive anchored depths. -/
theorem factA_fin : ∀ r, r < 28 → ∀ c β : Bool,
    ¬ (sel c (st r) = (true, β) ∧ sel (!c) (st (r + 1)) = (true, β) ∧
       sel c (st (r + 2)) = (true, β) ∧ sel (!c) (st (r + 3)) = (true, β)) := by decide

/-- Fact B over one period: no three consecutive anchored depths from an odd depth. -/
theorem factB_fin : ∀ r, r < 28 → r % 2 = 1 → ∀ c β : Bool,
    ¬ (sel c (st r) = (true, β) ∧ sel (!c) (st (r + 1)) = (true, β) ∧
       sel c (st (r + 2)) = (true, β)) := by decide

theorem factA (d : Nat) (c β : Bool) (h0 : A c d = (true, β)) (h1 : A (!c) (d + 1) = (true, β))
    (h2 : A c (d + 2) = (true, β)) (h3 : A (!c) (d + 3) = (true, β)) : False := by
  have g0 := A_mod c d 0
  rw [Nat.add_zero, Nat.add_zero] at g0
  rw [g0] at h0
  rw [A_mod] at h1 h2 h3
  exact factA_fin (d % 28) (Nat.mod_lt _ (by decide)) c β ⟨h0, h1, h2, h3⟩

theorem factB (d : Nat) (hd : d % 2 = 1) (c β : Bool) (h0 : A c d = (true, β))
    (h1 : A (!c) (d + 1) = (true, β)) (h2 : A c (d + 2) = (true, β)) : False := by
  have g0 := A_mod c d 0
  rw [Nat.add_zero, Nat.add_zero] at g0
  rw [g0] at h0
  rw [A_mod] at h1 h2
  exact factB_fin (d % 28) (Nat.mod_lt _ (by decide)) (by omega) c β ⟨h0, h1, h2⟩

/-! ### The anchor -/

theorem atDepth_last {w : List Sym} (hl : Legal w) : atDepth w (w.length - 1) = hd w := by
  cases w with
  | nil => exact hl.elim
  | cons x rest =>
    simp only [atDepth, hd, List.reverse_cons, List.length_cons, Nat.add_sub_cancel, List.headD_cons]
    rw [List.getD_eq_getElem?_getD]
    simp

theorem hd_legal {w : List Sym} (hl : Legal w) : hd w = (true, (hd w).2) := by
  cases w with
  | nil => exact hl.elim
  | cons x rest =>
    obtain ⟨xa, xb⟩ := x
    simp only [Legal] at hl
    subst hl
    rfl

/-- Site 0 of the frontier after `n` repeat-free updates, read through Reconstruction, is the
alternating closed form at depth `a + n - 1` in the phase of the last scalar. -/
theorem anchor (hrec : Reconstruction) {w wn : List Sym} {n d : Nat} {tn : List Bool}
    (hl : Legal w) (hrun : run w n = some (wn, tn)) (hrep : repeats tn = 0)
    (hd1 : d + 1 = w.length + n)
    (hthr : w.length + 1 ≤ n ∨ (terminalHigh w = true ∧ w.length ≤ n)) :
    A (window tn 0) d = (true, (hd w).2) := by
  obtain ⟨hln, hhd, hlen⟩ := run_inv hl n wn tn hrun
  have ha : 1 ≤ w.length := by
    cases w with
    | nil => exact hl.elim
    | cons x rest => simp
  have hdlt : d < wn.length := by omega
  obtain ⟨r1, r2⟩ := hrec w wn n tn hl hrun d hdlt
  have e1 := r1 (by
    rcases hthr with h | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h1, by omega⟩)
  have e2 := r2 (by
    rcases hthr with h | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h1, by omega⟩)
  have hat : atDepth wn d = hd w := by
    have : d = wn.length - 1 := by omega
    rw [this, atDepth_last hln, hhd]
  have hdep := FG_dep (window tn) (alt (window tn 0)) n (run_alt n wn tn hrun hrep) d 0
  have f1 := hdep.1 (by omega)
  have f2 := hdep.2 (by omega)
  have hw := hd_legal hl
  rw [hat] at e1 e2
  show FG (alt (window tn 0)) d 0 = (true, (hd w).2)
  rw [hw] at e1
  simp only at e1
  apply Prod.ext
  · simp only; rw [← f1, ← e1]
  · simp only; rw [← f2, ← e2]

theorem runBound_of_reconstruction : Reconstruction → RunBound := by
  intro hrec w w' L tape hl hrun hrep
  have ha : 1 ≤ w.length := by
    cases w with
    | nil => exact hl.elim
    | cons x rest => simp
  constructor
  · apply Nat.le_of_not_lt
    intro hL
    obtain ⟨k, rfl⟩ : ∃ k, L = (w.length + 3 + 1) + k := ⟨L - (w.length + 4), by omega⟩
    obtain ⟨w4, t4, u, hrun4, htape⟩ := run_prefix (w.length + 3 + 1) k w' tape hrun
    subst htape
    have hrep4 := repeats_append_left _ _ hrep
    obtain ⟨w3, t3, hrun3, hrep3, hf4⟩ := run_pred hrun4 hrep4
    obtain ⟨w2, t2, hrun2, hrep2, hf3⟩ := run_pred hrun3 hrep3
    obtain ⟨w1, t1, hrun1, hrep1, hf2⟩ := run_pred hrun2 hrep2
    have a1 := anchor hrec (d := 2 * w.length) hl hrun1 hrep1 (by omega) (Or.inl (by omega))
    have a2 := anchor hrec (d := 2 * w.length + 1) hl hrun2 hrep2 (by omega) (Or.inl (by omega))
    have a3 := anchor hrec (d := 2 * w.length + 2) hl hrun3 hrep3 (by omega) (Or.inl (by omega))
    have a4 := anchor hrec (d := 2 * w.length + 3) hl hrun4 hrep4 (by omega) (Or.inl (by omega))
    rw [hf4 (by omega), hf3 (by omega), hf2 (by omega)] at a4
    rw [hf3 (by omega), hf2 (by omega)] at a3
    rw [hf2 (by omega)] at a2
    simp only [Bool.not_not] at a3 a4
    exact factA _ _ _ a1 a2 a3 a4
  · intro hth
    apply Nat.le_of_not_lt
    intro hL
    obtain ⟨k, rfl⟩ : ∃ k, L = (w.length + 1 + 1) + k := ⟨L - (w.length + 2), by omega⟩
    obtain ⟨w2, t2, u, hrun2, htape⟩ := run_prefix (w.length + 1 + 1) k w' tape hrun
    subst htape
    have hrep2 := repeats_append_left _ _ hrep
    obtain ⟨w1, t1, hrun1, hrep1, hf2⟩ := run_pred hrun2 hrep2
    obtain ⟨w0, t0, hrun0, hrep0, hf1⟩ := run_pred hrun1 hrep1
    have a0 := anchor hrec (d := 2 * w.length - 1) hl hrun0 hrep0 (by omega)
      (Or.inr ⟨hth, by omega⟩)
    have a1 := anchor hrec (d := 2 * w.length - 1 + 1) hl hrun1 hrep1 (by omega)
      (Or.inr ⟨hth, by omega⟩)
    have a2 := anchor hrec (d := 2 * w.length - 1 + 2) hl hrun2 hrep2 (by omega)
      (Or.inr ⟨hth, by omega⟩)
    rw [hf2 (by omega), hf1 (by omega)] at a2
    rw [hf1 (by omega)] at a1
    simp only [Bool.not_not] at a2
    exact factB _ (by omega) _ _ a0 a1 a2

/-! ## The survival inequality -/

/-
Proof of `survival_of_runBound`, written out before the Lean.

Write r = w.length. Cut the successful tape immediately before each repeated scalar. The
current (last) block is a run of l >= 1 updates from an onset frontier wq reached after m
updates, m + l = N, and its tape has no repeat. Invariant carried by induction on N:

    r + m + 1 <= 2^D (r + 2),   and   r + m + 1 <= 2^D (r + 1) when terminalHigh w,

with D = repeats tape. For m = 0 it is trivial. Appending a scalar s after last scalar a:
  * s != a: D and m are unchanged, the block grows to l + 1 and is still repeat-free.
  * s  = a: D grows by one and the new onset is m' = m + l = N. RunBound on the closed block
    gives l <= |wq| + 1 = r + m + 1 when m >= 1, because wq is then a successful image and its
    last symbol is the birth symbol (1, _); for m = 0 it gives l <= r + 3, or l <= r + 1 under
    terminalHigh w. Either way r + m' + 1 <= 2 (r + m + 1) <= 2^(D+1) (r + 2), resp. (r + 1),
    using 2^D >= 1 in the m = 0 case.
The same block estimate applied to the unfinished last block is the Survival inequality.
-/

theorem scan_length_S (m : Bool × Bool × Bool) (w : List Sym) :
    (scan m w).1.length = w.length := by
  induction w generalizing m with
  | nil => rfl
  | cons s w ih => simp [scan, ih]

theorem Z_some_S {w w' : List Sym} {s : Bool} (h : Z w = some (w', s)) :
    w' = (scan (false, false, false) w).1 ++ [(true, !s)] := by
  unfold Z at h
  simp only at h
  split at h
  · injection h with h
    injection h with h1 h2
    subst h2
    exact h1.symm
  · cases h

theorem Z_length {w w' : List Sym} {s : Bool} (h : Z w = some (w', s)) :
    w'.length = w.length + 1 := by
  rw [Z_some_S h, List.length_append, scan_length_S]
  rfl

theorem Z_legal {w w' : List Sym} {s : Bool} (hw : Legal w) (h : Z w = some (w', s)) :
    Legal w' := by
  rw [Z_some_S h]
  cases w with
  | nil => exact hw.elim
  | cons x rest =>
    have hx : x.1 = true := hw
    simp [scan, scanStep, Legal, hx]

theorem Z_terminalHigh {w w' : List Sym} {s : Bool} (h : Z w = some (w', s)) :
    terminalHigh w' = true := by
  rw [Z_some_S h]
  simp [terminalHigh]

theorem run_succ_some_S {w w'' : List Sym} {n : Nat} {t' : List Bool}
    (h : run w (n + 1) = some (w'', t')) :
    ∃ w' t s, run w n = some (w', t) ∧ Z w' = some (w'', s) ∧ t' = t ++ [s] := by
  simp only [run] at h
  split at h
  · cases h
  · rename_i w' t hrun
    split at h
    · cases h
    · rename_i w2 s hZ
      injection h with h
      injection h with h1 h2
      subst h1
      subst h2
      exact ⟨w', t, s, hrun, hZ, rfl⟩

theorem run_succ_of {w w' w'' : List Sym} {n : Nat} {t : List Bool} {s : Bool}
    (h1 : run w n = some (w', t)) (h2 : Z w' = some (w'', s)) :
    run w (n + 1) = some (w'', t ++ [s]) := by
  simp only [run, h1, h2]

theorem run_zero_some {w w' : List Sym} {t : List Bool} (h : run w 0 = some (w', t)) :
    w' = w ∧ t = [] := by
  simp only [run] at h
  injection h with h
  injection h with h1 h2
  exact ⟨h1.symm, h2.symm⟩

theorem run_legal {w : List Sym} (hw : Legal w) :
    ∀ (n : Nat) (w' : List Sym) (t : List Bool), run w n = some (w', t) → Legal w' := by
  intro n
  induction n with
  | zero =>
    intro w' t h
    rw [(run_zero_some h).1]
    exact hw
  | succ n ih =>
    intro w' t h
    rcases run_succ_some_S h with ⟨w1, t1, s, h1, hZ, _⟩
    exact Z_legal (ih w1 t1 h1) hZ

theorem run_length {w : List Sym} :
    ∀ (n : Nat) (w' : List Sym) (t : List Bool), run w n = some (w', t) →
      w'.length = w.length + n ∧ t.length = n := by
  intro n
  induction n with
  | zero =>
    intro w' t h
    rcases run_zero_some h with ⟨h1, h2⟩
    subst h1
    subst h2
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro w' t h
    rcases run_succ_some_S h with ⟨w1, t1, s, h1, hZ, ht⟩
    rcases ih w1 t1 h1 with ⟨hl, htl⟩
    refine ⟨?_, ?_⟩
    · rw [Z_length hZ, hl]
      omega
    · rw [ht, List.length_append, htl]
      rfl

theorem run_terminalHigh {w w' : List Sym} {n : Nat} {t : List Bool}
    (h : run w (n + 1) = some (w', t)) : terminalHigh w' = true := by
  rcases run_succ_some_S h with ⟨w1, t1, s, _, hZ, _⟩
  exact Z_terminalHigh hZ

/-- Appending a scalar after a nonempty tape adds one repeat exactly when it equals the last. -/
theorem repeats_concat (t : List Bool) (a s : Bool) :
    repeats ((t ++ [a]) ++ [s]) = repeats (t ++ [a]) + (if a = s then 1 else 0) := by
  induction t with
  | nil => simp [repeats]
  | cons x t ih =>
    cases t with
    | nil => simp [repeats]
    | cons y t' =>
      have e1 : (x :: y :: t' ++ [a]) ++ [s] = x :: y :: ((t' ++ [a]) ++ [s]) := by simp
      have e2 : x :: y :: t' ++ [a] = x :: y :: (t' ++ [a]) := by simp
      have e3 : (y :: t' ++ [a]) ++ [s] = y :: ((t' ++ [a]) ++ [s]) := by simp
      have e4 : y :: t' ++ [a] = y :: (t' ++ [a]) := by simp
      rw [e3, e4] at ih
      rw [e1, e2]
      simp only [repeats]
      rw [ih]
      omega

/-- The block estimate: an onset reached after `m` updates with `r + m + 1 ≤ 2^D (r + 2)`,
followed by a repeat-free block of `l` updates, gives `r + (m + l) + 1 ≤ 2^(D+1) (r + 2)`. -/
theorem bound_of_block (hRB : RunBound) {w : List Sym} (hw : Legal w)
    {m l : Nat} {wq w' : List Sym} {tq tl : List Bool} {D : Nat}
    (h1 : run w m = some (wq, tq)) (h2 : run wq l = some (w', tl)) (hrep : repeats tl = 0)
    (hb : w.length + m + 1 ≤ 2 ^ D * (w.length + 2))
    (hb' : terminalHigh w = true → w.length + m + 1 ≤ 2 ^ D * (w.length + 1)) :
    w.length + (m + l) + 1 ≤ 2 ^ (D + 1) * (w.length + 2) ∧
    (terminalHigh w = true → w.length + (m + l) + 1 ≤ 2 ^ (D + 1) * (w.length + 1)) := by
  have hq : Legal wq := run_legal hw m wq tq h1
  have hlen : wq.length = w.length + m := (run_length m wq tq h1).1
  rcases hRB wq w' l tl hq h2 hrep with ⟨hA, hB⟩
  have hpos : 0 < 2 ^ D := Nat.two_pow_pos D
  have e2 : 2 ^ (D + 1) * (w.length + 2) = 2 * (2 ^ D * (w.length + 2)) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ D) 2, Nat.mul_assoc]
  have e1 : 2 ^ (D + 1) * (w.length + 1) = 2 * (2 ^ D * (w.length + 1)) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ D) 2, Nat.mul_assoc]
  have g2 : w.length + 2 ≤ 2 ^ D * (w.length + 2) := Nat.le_mul_of_pos_left _ hpos
  have g1 : w.length + 1 ≤ 2 ^ D * (w.length + 1) := Nat.le_mul_of_pos_left _ hpos
  rw [e2, e1]
  cases m with
  | zero =>
    have hwq : wq = w := (run_zero_some h1).1
    subst hwq
    refine ⟨by omega, ?_⟩
    intro hT
    have := hB hT
    omega
  | succ m' =>
    have hT' : terminalHigh wq = true := run_terminalHigh h1
    have hl := hB hT'
    refine ⟨by omega, ?_⟩
    intro hT
    have := hb' hT
    omega

/-- The invariant of the current block, by induction on the number of updates. -/
theorem block_invariant (hRB : RunBound) {w : List Sym} (hw : Legal w) :
    ∀ (N : Nat) (w' : List Sym) (tape : List Bool), run w (N + 1) = some (w', tape) →
      ∃ (m l : Nat) (wq : List Sym) (tq tl : List Bool) (a : Bool),
        m + (l + 1) = N + 1 ∧ run w m = some (wq, tq) ∧
        run wq (l + 1) = some (w', tl ++ [a]) ∧
        tape = tq ++ (tl ++ [a]) ∧ repeats (tl ++ [a]) = 0 ∧
        w.length + m + 1 ≤ 2 ^ repeats tape * (w.length + 2) ∧
        (terminalHigh w = true → w.length + m + 1 ≤ 2 ^ repeats tape * (w.length + 1)) := by
  intro N
  induction N with
  | zero =>
    intro w' tape h
    rcases run_succ_some_S h with ⟨w0, t0, s, h0, hZ, ht⟩
    rcases run_zero_some h0 with ⟨e1, e2⟩
    subst e1
    subst e2
    have ht' : tape = [s] := by simpa using ht
    subst ht'
    have hpos : 0 < 2 ^ repeats [s] := Nat.two_pow_pos _
    refine ⟨0, 0, w0, [], [], s, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using h
    · simp
    · simp [repeats]
    · have := Nat.le_mul_of_pos_left (w0.length + 2) hpos
      omega
    · intro _
      have := Nat.le_mul_of_pos_left (w0.length + 1) hpos
      omega
  | succ N ih =>
    intro w'' tape' h
    rcases run_succ_some_S h with ⟨w', tape, s, hrun, hZ, ht⟩
    rcases ih w' tape hrun with ⟨m, l, wq, tq, tl, a, hml, hq, hblk, htape, hrep, hb, hb'⟩
    have hrepT : repeats tape' = repeats tape + (if a = s then 1 else 0) := by
      rw [ht, htape, ← List.append_assoc tq tl [a]]
      exact repeats_concat (tq ++ tl) a s
    by_cases has : a = s
    · -- a repeat: the block closes, the new onset is w' after N + 1 updates
      have hD : repeats tape' = repeats tape + 1 := by rw [hrepT]; simp only [has, ↓reduceIte]
      have hbd := bound_of_block hRB hw hq hblk hrep hb hb'
      have hone : run w' (0 + 1) = some (w'', [] ++ [s]) := run_succ_of rfl hZ
      refine ⟨N + 1, 0, w', tape, [], s, rfl, hrun, hone, ?_, ?_, ?_, ?_⟩
      · simpa using ht
      · simp [repeats]
      · rw [hD, ← hml]
        exact hbd.1
      · intro hT
        rw [hD, ← hml]
        exact hbd.2 hT
    · -- no repeat: the block grows by one
      have hD : repeats tape' = repeats tape := by rw [hrepT]; simp only [has, ↓reduceIte]; rfl
      have hgrow : run wq (l + 1 + 1) = some (w'', (tl ++ [a]) ++ [s]) := run_succ_of hblk hZ
      have hrep' : repeats ((tl ++ [a]) ++ [s]) = 0 := by
        rw [repeats_concat, hrep]; simp only [has, ↓reduceIte]
      refine ⟨m, l + 1, wq, tq, tl ++ [a], s, by omega, hq, hgrow, ?_, hrep', ?_, ?_⟩
      · rw [ht, htape, List.append_assoc]
      · rw [hD]; exact hb
      · rw [hD]; exact hb'

theorem survival_of_runBound : RunBound → Survival := by
  intro hRB w w' N tape hw hN hrun
  cases N with
  | zero => omega
  | succ N =>
    rcases block_invariant hRB hw N w' tape hrun with
      ⟨m, l, wq, tq, tl, a, hml, hq, hblk, _, hrep, hb, hb'⟩
    have hbd := bound_of_block hRB hw hq hblk hrep hb hb'
    rw [hml] at hbd
    exact hbd

/-! ## Budget, mortality and capacity -/

/-
Proof plan.

(1) run w (n+1) unfolds by definition; a `none` at depth n stays `none` at n+1, hence at every
    M ≥ n (induction on the gap).
(2) A successful run of N updates emits exactly N scalars: tape.length = N (induction on N).
(3) repeats tape ≤ tape.length (structural induction, two-step).
(4) horizon_of_budget: if run w N = some (w', tape) with N beyond the horizon, then N ≥ 1, Survival
    gives r + N + 1 ≤ 2^(D+1)(r+2) ≤ 2^(B+1)(r+2) since D ≤ B; contradiction by omega.
(5) mortalAt_of_budgetAt, mortal_of_capacity_budget: instantiate the horizon.
(6) budgetAt_of_mortalAt: the words of length r over four symbols form an explicit finite list
    allWords r, complete by induction. Over an explicit list l, if every member satisfying C dies
    then one bound B covers all deaths (induction on l, max of the bounds). A successful run of
    length N from w with death time N_w ≤ B has N < N_w by (1), so repeats tape ≤ N < B by (2),(3).
(7) The control: alternating tape of length 10 with r = 1 has D = 0 and 12 > 6.
-/

theorem run_succ_of_none {w : List Sym} {n : Nat} (h : run w n = none) :
    run w (n + 1) = none := by
  simp [run, h]

theorem run_none_add {w : List Sym} {n : Nat} (h : run w n = none) :
    ∀ k : Nat, run w (n + k) = none
  | 0 => h
  | k + 1 => run_succ_of_none (run_none_add h k)

theorem run_none_mono {w : List Sym} {n m : Nat} (h : run w n = none) (hnm : n ≤ m) :
    run w m = none := by
  have := run_none_add h (m - n)
  have e : n + (m - n) = m := by omega
  rw [e] at this
  exact this

theorem run_tape_length : ∀ (N : Nat) (w w' : List Sym) (tape : List Bool),
    run w N = some (w', tape) → tape.length = N
  | 0, w, w', tape, h => by
    simp [run] at h
    rw [h.2]; rfl
  | n + 1, w, w', tape, h => by
    simp only [run] at h
    cases hr : run w n with
    | none => rw [hr] at h; simp at h
    | some p =>
      obtain ⟨w1, t⟩ := p
      rw [hr] at h
      simp only at h
      cases hz : Z w1 with
      | none => rw [hz] at h; simp at h
      | some q =>
        obtain ⟨w2, s⟩ := q
        rw [hz] at h
        simp at h
        have ih := run_tape_length n w w1 t hr
        rw [← h.2]
        simp [ih]

theorem repeats_le_length : ∀ tape : List Bool, repeats tape ≤ tape.length
  | [] => by simp [repeats]
  | [_] => by simp [repeats]
  | a :: b :: t => by
    have ih := repeats_le_length (b :: t)
    simp only [repeats, List.length_cons] at ih ⊢
    split <;> omega

theorem horizon_of_budget (hS : Survival) (r B : Nat)
    (hB : ∀ (w w' : List Sym) (N : Nat) (tape : List Bool), Legal w → w.length = r →
      run w N = some (w', tape) → repeats tape ≤ B) :
    ∀ w : List Sym, Legal w → w.length = r → ∀ N : Nat,
      2 ^ (B + 1) * (r + 2) - r - 1 < N → run w N = none := by
  intro w hw hr N hN
  cases hrun : run w N with
  | none => rfl
  | some p =>
    exfalso
    obtain ⟨w', tape⟩ := p
    have hD : repeats tape ≤ B := hB w w' N tape hw hr hrun
    have hN1 : 1 ≤ N := by omega
    have hsurv := (hS w w' N tape hw hN1 hrun).1
    rw [hr] at hsurv
    have hpow : 2 ^ (repeats tape + 1) ≤ 2 ^ (B + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hmul : 2 ^ (repeats tape + 1) * (r + 2) ≤ 2 ^ (B + 1) * (r + 2) :=
      Nat.mul_le_mul_right (r + 2) hpow
    omega

theorem mortalAt_of_budgetAt (hS : Survival) (r : Nat) : BudgetAt r → MortalAt r := by
  intro hB w hw hr
  obtain ⟨B, hB⟩ := hB
  exact ⟨2 ^ (B + 1) * (r + 2) - r - 1 + 1,
    horizon_of_budget hS r B hB w hw hr _ (by omega)⟩

theorem mortal_of_capacity_budget (hS : Survival) (Q : List Sym → Nat)
    (hQ : ∀ K : Nat, ∃ B : Nat, ∀ (w w' : List Sym) (N : Nat) (tape : List Bool), Legal w →
      Q w ≤ K → run w N = some (w', tape) → repeats tape ≤ B) :
    ∀ w : List Sym, Legal w → ∃ N : Nat, run w N = none := by
  intro w hw
  obtain ⟨B, hB⟩ := hQ (Q w)
  refine ⟨2 ^ (B + 1) * (w.length + 2) - w.length - 1 + 1, ?_⟩
  cases hrun : run w (2 ^ (B + 1) * (w.length + 2) - w.length - 1 + 1) with
  | none => rfl
  | some p =>
    exfalso
    obtain ⟨w', tape⟩ := p
    have hD : repeats tape ≤ B := hB w w' _ tape hw (Nat.le_refl _) hrun
    have hsurv := (hS w w' _ tape hw (by omega) hrun).1
    have hpow : 2 ^ (repeats tape + 1) ≤ 2 ^ (B + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hmul : 2 ^ (repeats tape + 1) * (w.length + 2) ≤ 2 ^ (B + 1) * (w.length + 2) :=
      Nat.mul_le_mul_right (w.length + 2) hpow
    omega

/-- The four symbols. -/
def allSyms : List Sym := [(false, false), (false, true), (true, false), (true, true)]

theorem mem_allSyms (s : Sym) : s ∈ allSyms := by
  obtain ⟨a, b⟩ := s
  cases a <;> cases b <;> simp [allSyms]

/-- Every word of length `n` over the four symbols. -/
def allWords : Nat → List (List Sym)
  | 0 => [[]]
  | n + 1 => (allWords n).flatMap (fun w => allSyms.map (fun s => s :: w))

theorem mem_allWords : ∀ w : List Sym, w ∈ allWords w.length
  | [] => by simp [allWords]
  | s :: w => by
    simp only [List.length_cons, allWords, List.mem_flatMap, List.mem_map]
    exact ⟨w, mem_allWords w, s, mem_allSyms s, rfl⟩

/-- Uniform death time over an explicit finite list. -/
theorem uniform_death (C : List Sym → Prop) :
    ∀ l : List (List Sym), (∀ w, w ∈ l → C w → ∃ N : Nat, run w N = none) →
      ∃ B : Nat, ∀ w, w ∈ l → C w → run w B = none
  | [], _ => ⟨0, by intro w hw; simp at hw⟩
  | x :: l, h => by
    obtain ⟨B, hB⟩ := uniform_death C l (fun w hw hc => h w (List.mem_cons_of_mem x hw) hc)
    by_cases hc : C x
    · obtain ⟨N, hN⟩ := h x (List.mem_cons_self) hc
      refine ⟨max N B, ?_⟩
      intro w hw hcw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact run_none_mono hN (by omega)
      · exact run_none_mono (hB w hw' hcw) (by omega)
    · refine ⟨B, ?_⟩
      intro w hw hcw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact absurd hcw hc
      · exact hB w hw' hcw

theorem budgetAt_of_mortalAt (r : Nat) : MortalAt r → BudgetAt r := by
  intro hM
  obtain ⟨B, hB⟩ := uniform_death (fun w => Legal w ∧ w.length = r) (allWords r)
    (fun w _ hc => hM w hc.1 hc.2)
  refine ⟨B, ?_⟩
  intro w w' N tape hw hr hrun
  have hmem : w ∈ allWords r := by
    have := mem_allWords w
    rw [hr] at this
    exact this
  have hdead : run w B = none := hB w hmem ⟨hw, hr⟩
  have hlen : tape.length = N := run_tape_length N w w' tape hrun
  have hrep := repeats_le_length tape
  have hlt : N < B := by
    apply Nat.lt_of_not_le
    intro hle
    have := run_none_mono hdead hle
    rw [hrun] at this
    simp at this
  omega

theorem survival_counting_fails_without_runBound :
    ¬ ∀ (r : Nat) (tape : List Bool), 1 ≤ tape.length →
      r + tape.length + 1 ≤ 2 ^ (repeats tape + 1) * (r + 2) := by
  intro h
  have := h 1 [true, false, true, false, true, false, true, false, true, false] (by decide)
  revert this
  decide

/-! ## The bridges, with every hypothesis discharged -/

theorem runBound : RunBound := runBound_of_reconstruction reconstruction

theorem survival : Survival := survival_of_runBound runBound

/-- budget <-> mortality at each length. -/
theorem budgetAt_iff_mortalAt (r : Nat) : BudgetAt r ↔ MortalAt r :=
  ⟨mortalAt_of_budgetAt survival r, budgetAt_of_mortalAt r⟩

/-- Node `budget` (a repeat budget at every length) is node `mortality`. -/
theorem budget_iff_mortality : (∀ r : Nat, BudgetAt r) ↔ Mortality :=
  ⟨fun h w hw => (budgetAt_iff_mortalAt w.length).mp (h w.length) w hw rfl,
   fun h r => (budgetAt_iff_mortalAt r).mpr (fun w hw _ => h w hw)⟩

/-- capacity -> mortality, for every capacity function `Q`. -/
theorem mortality_of_capacity_budget (Q : List Sym → Nat)
    (hQ : ∀ K : Nat, ∃ B : Nat, ∀ (w w' : List Sym) (N : Nat) (tape : List Bool), Legal w →
      Q w ≤ K → run w N = some (w', tape) → repeats tape ≤ B) : Mortality :=
  mortal_of_capacity_budget survival Q hQ

/-! ## Left-Prefix Causality, 1-Step Memory Erasure, and Left-Front / Right-Terminal Causal Cone Collision -/

/-- One pure left-to-right scan from the zero initial memory `(false, false, false)`. -/
def pureScan (w : List Sym) : List Sym :=
  (scan (false, false, false) w).1

/-- `n`-fold iteration of `pureScan` on a frontier prefix `w`. -/
def iterPureScan : Nat → List Sym → List Sym
  | 0, w => w
  | n + 1, w => pureScan (iterPureScan n w)

/-- `pureScan` preserves list length. -/
theorem pureScan_length (w : List Sym) : (pureScan w).length = w.length :=
  scan_length (false, false, false) w

/-- `iterPureScan n` preserves list length for all `n : Nat`. -/
theorem iterPureScan_length : ∀ (n : Nat) (w : List Sym), (iterPureScan n w).length = w.length
  | 0, _ => rfl
  | n + 1, w => by rw [iterPureScan, pureScan_length, iterPureScan_length n w]

/-- **Left-prefix causality of `scan` (`scan_take`):** for any initial memory `m`, frontier `w`,
and prefix length `k`, the first `k` emitted symbols of `scan m w` depend only on `w.take k`. -/
theorem scan_take : ∀ (k : Nat) (m : Bool × Bool × Bool) (w : List Sym),
    ((scan m w).1).take k = (scan m (w.take k)).1
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | k + 1, m, s :: w => by
    simp only [List.take_succ_cons, scan, scan_take k (scanStep m s) w]

/-- `pureScan` commutes with `.take k` for every `k : Nat`. -/
theorem pureScan_take (k : Nat) (w : List Sym) :
    (pureScan w).take k = pureScan (w.take k) :=
  scan_take k (false, false, false) w

/-- `iterPureScan n` commutes with `.take k` for every `n, k : Nat`. -/
theorem iterPureScan_take : ∀ (n k : Nat) (w : List Sym),
    (iterPureScan n w).take k = iterPureScan n (w.take k)
  | 0, _, _ => rfl
  | n + 1, k, w => by
    rw [iterPureScan, pureScan_take, iterPureScan_take n k w, ← iterPureScan]

/-- **Single-step left-prefix autonomy (`Z_take_eq_pureScan`):** if `Z w = some (w', s)`, then for
every `k ≤ w.length`, `w'.take k = pureScan (w.take k)` (independent of the birth symbol `(1, !s)`). -/
theorem Z_take_eq_pureScan {w w' : List Sym} {s : Bool} {k : Nat}
    (hZ : Z w = some (w', s)) (hk : k ≤ w.length) :
    w'.take k = pureScan (w.take k) := by
  rcases Z_some hZ with ⟨_, rfl⟩
  have hlen : ((scan (false, false, false) w).1).length = w.length :=
    scan_length (false, false, false) w
  rw [List.take_append_of_le_length (by omega)]
  exact scan_take k (false, false, false) w

/-- **Multi-step left-prefix autonomy (`run_take_eq_iterPureScan`):** throughout any successful
`n`-step run `run w n = some (w', tape)` and any `k ≤ w.length`, the prefix `w'.take k` equals
`iterPureScan n (w.take k)`—evolving deterministically and independently of the scalar `tape`. -/
theorem run_take_eq_iterPureScan :
    ∀ {n : Nat} {w w' : List Sym} {tape : List Bool} {k : Nat},
      run w n = some (w', tape) → k ≤ w.length →
      w'.take k = iterPureScan n (w.take k)
  | 0, w, w', tape, k, hrun, _ => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at hrun
    rw [← hrun.1, iterPureScan]
  | n + 1, w, w'', tape, k, hrun, hk => by
    rcases run_succ_some_S hrun with ⟨w', t, s, hr, hZ, _⟩
    have hlen : w'.length = w.length + n := (run_length n w' t hr).1
    have h1 := Z_take_eq_pureScan hZ (k := k) (by omega)
    have ih := run_take_eq_iterPureScan hr hk
    rw [h1, ih, iterPureScan]

/-- **Left-Front Head Permanence (`iterPureScan_head_eq`):** for any legal frontier `(true, b₀) :: w`
and any `n : Nat`, the first symbol of `iterPureScan n ((true, b₀) :: w)` is `(true, b₀)`. -/
theorem iterPureScan_head_eq (b₀ : Bool) (w : List Sym) :
    ∀ n : Nat, (iterPureScan n ((true, b₀) :: w)).take 1 = [(true, b₀)]
  | 0 => rfl
  | n + 1 => by
    rw [iterPureScan, pureScan_take, iterPureScan_head_eq b₀ w n]
    cases b₀ <;> rfl

/-- **1-Step Left-Front Memory Erasure (`pureScan_two_erase_b1`):** for any legal frontier starting
with `(true, b₀) :: (a₁, b₁)`, the first scan step erases `b₁` completely, mapping the 2-symbol
prefix to `[(true, b₀), (b₀ && !a₁, !b₀)]`. -/
theorem pureScan_two_erase_b1 (b₀ a₁ b₁ : Bool) (w : List Sym) :
    (pureScan ((true, b₀) :: (a₁, b₁) :: w)).take 2 =
      [(true, b₀), (b₀ && !a₁, !b₀)] := by
  unfold pureScan scan scanStep
  cases b₀ <;> cases a₁ <;> cases b₁ <;> rfl

/-- When `b₀ = false`, the first two symbols of `iterPureScan n ((true, false) :: s₁ :: w)` are
permanently frozen to `[(true, false), (false, true)]` for all `n ≥ 1`. -/
theorem iterPureScan_two_of_false (s₁ : Sym) (w : List Sym) :
    ∀ n : Nat, 1 ≤ n →
      (iterPureScan n ((true, false) :: s₁ :: w)).take 2 = [(true, false), (false, true)]
  | 0, h => by omega
  | 1, _ => by
    obtain ⟨a₁, b₁⟩ := s₁
    simpa [iterPureScan] using pureScan_two_erase_b1 false a₁ b₁ w
  | n + 2, _ => by
    have ih := iterPureScan_two_of_false s₁ w (n + 1) (by omega)
    rw [iterPureScan, pureScan_take, ih]
    rfl

/-- **2-Symbol Left-Front Period-2 Lock (`iterPureScan_two_period_two`):** for any legal 2-symbol
prefix `[(true, b₀), s₁]` and any `n ≥ 1`, `iterPureScan (n + 2) [(true, b₀), s₁] =
iterPureScan n [(true, b₀), s₁]`. -/
theorem iterPureScan_two_period_two (b₀ : Bool) (s₁ : Sym) :
    ∀ n : Nat, 1 ≤ n →
      iterPureScan (n + 2) [(true, b₀), s₁] = iterPureScan n [(true, b₀), s₁]
  | 0, h => by omega
  | 1, _ => by
    obtain ⟨a₁, b₁⟩ := s₁
    revert b₀ a₁ b₁
    decide
  | n + 2, _ => by
    have ih := iterPureScan_two_period_two b₀ s₁ (n + 1) (by omega)
    show pureScan (iterPureScan (n + 1 + 2) [(true, b₀), s₁]) =
      pureScan (iterPureScan (n + 1) [(true, b₀), s₁])
    rw [ih]

/-- **4-Symbol Left-Front Period-2 Lock (`iterPureScan_four_period_two`):** for any legal 4-symbol
prefix `[(true, b₀), s₁, s₂, s₃]` and any `n ≥ 4`, `iterPureScan (n + 2) [(true, b₀), s₁, s₂, s₃] =
iterPureScan n [(true, b₀), s₁, s₂, s₃]`. -/
theorem iterPureScan_four_period_two (b₀ : Bool) (s₁ s₂ s₃ : Sym) :
    ∀ n : Nat, 4 ≤ n →
      iterPureScan (n + 2) [(true, b₀), s₁, s₂, s₃] = iterPureScan n [(true, b₀), s₁, s₂, s₃]
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, h => by omega
  | 4, _ => by
    obtain ⟨a₁, b₁⟩ := s₁; obtain ⟨a₂, b₂⟩ := s₂; obtain ⟨a₃, b₃⟩ := s₃
    revert b₀ a₁ b₁ a₂ b₂ a₃ b₃
    decide
  | n + 5, _ => by
    have ih := iterPureScan_four_period_two b₀ s₁ s₂ s₃ (n + 4) (by omega)
    show pureScan (iterPureScan (n + 4 + 2) [(true, b₀), s₁, s₂, s₃]) =
      pureScan (iterPureScan (n + 4) [(true, b₀), s₁, s₂, s₃])
    rw [ih]

/-- Indexing from the right terminal end `atDepth u (u.length - 1 - i)` equals `u.getD i (false, false)`
for all `i < u.length`. -/
theorem atDepth_rev_index : ∀ (u : List Sym) (i : Nat), i < u.length →
    atDepth u (u.length - 1 - i) = u.getD i (false, false)
  | [], _, h => by simp at h
  | s :: u, 0, _ => by
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getD_cons_zero]
    exact atDepth_cons_eq s u
  | s :: u, i + 1, h => by
    simp only [List.length_cons] at h
    have hi : i < u.length := by omega
    have hsub : (s :: u).length - 1 - (i + 1) = u.length - 1 - i := by
      simp only [List.length_cons]; omega
    rw [hsub, atDepth_cons_lt s u (u.length - 1 - i) (by omega), List.getD_cons_succ]
    exact atDepth_rev_index u i hi

/-- If `i < k`, `(u.take k).getD i d = u.getD i d`. -/
theorem getD_take_lt : ∀ (u : List Sym) (k i : Nat) (d : Sym),
    i < k → (u.take k).getD i d = u.getD i d
  | [], _, _, _, _ => by simp
  | _ :: _, 0, _, _, hik => by omega
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: u, k + 1, i + 1, d, hik => getD_take_lt u k i d (by omega)

/-- **Left-Front / Right-Terminal Causal Collision (`front_eq_terminal_FG`):** in any successful
run `run w n = some (w', tape)` of a legal frontier `w`, once `w.length + 1 ≤ n + i` (`i < w.length`),
the `i`-th symbol of the autonomous left-front trajectory `iterPureScan n w` must equal the
right-terminal scalar field `FG (window tape) (w.length + n - 1 - i) 0`. -/
theorem front_eq_terminal_FG {w w' : List Sym} {n i : Nat} {tape : List Bool}
    (hw : Legal w) (hrun : run w n = some (w', tape))
    (hi : i < w.length) (hcol : w.length + 1 ≤ n + i) :
    (iterPureScan n w).getD i (false, false) =
      FG (window tape) (w.length + n - 1 - i) 0 := by
  have hlen : w'.length = w.length + n := (run_length n w' tape hrun).1
  have htake : w'.take w.length = iterPureScan n w := by
    have h := run_take_eq_iterPureScan hrun (Nat.le_refl w.length)
    rwa [List.take_length] at h
  rw [← htake, getD_take_lt w' w.length i (false, false) hi, ← atDepth_rev_index w' i (by omega)]
  have hd_lt : w'.length - 1 - i < w'.length := by omega
  have hrec := reconstruction w w' n tape hw hrun (w'.length - 1 - i) hd_lt
  have h1 := hrec.1 (Or.inl (by omega))
  have h2 := hrec.2 (Or.inl (by omega))
  rw [show w'.length - 1 - i = w.length + n - 1 - i by omega] at h1 h2 ⊢
  exact Prod.ext h1 h2

/-- **Universal Top-Depth Scalar Field Locking (`terminal_FG_top_eq_head`):** for any legal frontier
`(true, b₀) :: rest` and any successful run `run ((true, b₀) :: rest) n = some (w', tape)` with
`rest.length + 2 ≤ n`, the scalar field `FG (window tape) (rest.length + n) 0` is permanently
locked to `(true, b₀)`. -/
theorem terminal_FG_top_eq_head {b₀ : Bool} {rest w' : List Sym} {n : Nat} {tape : List Bool}
    (hrun : run ((true, b₀) :: rest) n = some (w', tape)) (hn : rest.length + 2 ≤ n) :
    FG (window tape) (rest.length + n) 0 = (true, b₀) := by
  have hw : Legal ((true, b₀) :: rest) := rfl
  have hcol := front_eq_terminal_FG hw hrun (i := 0) (by simp) (by simp; omega)
  simp only [List.length_cons, Nat.sub_zero, show rest.length + 1 + n - 1 = rest.length + n by omega] at hcol
  rw [← hcol, ← getD_take_lt (iterPureScan n ((true, b₀) :: rest)) 1 0 (false, false) (by decide),
    iterPureScan_head_eq b₀ rest n]
  rfl

/-- **Universal Second-Depth Scalar Field Locking (`terminal_FG_second_of_false`):** for any legal
frontier `(true, false) :: s₁ :: rest` and any successful run of length `n ≥ rest.length + 2`, the
scalar field `FG (window tape) (rest.length + n) 0` is permanently locked to `(false, true)`. -/
theorem terminal_FG_second_of_false {s₁ : Sym} {rest w' : List Sym} {n : Nat} {tape : List Bool}
    (hrun : run ((true, false) :: s₁ :: rest) n = some (w', tape)) (hn : rest.length + 2 ≤ n) :
    FG (window tape) (rest.length + n) 0 = (false, true) := by
  have hw : Legal ((true, false) :: s₁ :: rest) := rfl
  have hcol := front_eq_terminal_FG hw hrun (i := 1) (by simp) (by simp; omega)
  simp only [List.length_cons, show rest.length + 1 + 1 + n - 1 - 1 = rest.length + n by omega] at hcol
  rw [← hcol, ← getD_take_lt (iterPureScan n ((true, false) :: s₁ :: rest)) 2 1 (false, false) (by decide),
    iterPureScan_two_of_false s₁ rest n (by omega)]
  rfl

/-! ## 2. Exact Isomorphism Between `pureScan` and the Rule 30 Left Diagonals `D j` -/

/-- The `k`-th symbol of the canonical `(true, true)` left-diagonal frontier at time offset `q`:
`(D (2 * k + 1) (q + k + 1), D (2 * k) (q + k))`. -/
def diagSym (q k : Nat) : Sym :=
  (D (2 * k + 1) (q + k + 1), D (2 * k) (q + k))

/-- The 3-bit scan memory entering site `k + 1` after scanning `diagSym q 0 .. diagSym q k`. -/
def diagMem (q k : Nat) : Bool × Bool × Bool :=
  (D (2 * k + 1) (q + k + 2), D (2 * k) (q + k + 1), D (2 * k + 1) (q + k + 1))

/-- Tail of the canonical left-diagonal frontier from site `k` of length `m`. -/
def diagTail (q k : Nat) : Nat → List Sym
  | 0 => []
  | m + 1 => diagSym q k :: diagTail q (k + 1) m

/-- The canonical `(true, true)` left-diagonal frontier of length `r` at time offset `q`. -/
def diagFrontier (q r : Nat) : List Sym :=
  diagTail q 0 r

/-- Length of `diagTail q k m` is `m`. -/
theorem diagTail_length (q : Nat) : ∀ (m k : Nat), (diagTail q k m).length = m
  | 0, _ => rfl
  | m + 1, k => by simp [diagTail, diagTail_length q m (k + 1)]

/-- Length of `diagFrontier q r` is `r`. -/
theorem diagFrontier_length (q r : Nat) : (diagFrontier q r).length = r :=
  diagTail_length q r 0

/-- Indexing `diagTail q k m` at `i < m` returns `diagSym q (k + i)`. -/
theorem diagTail_getD (q : Nat) : ∀ (m k i : Nat), i < m →
    (diagTail q k m).getD i (false, false) = diagSym q (k + i)
  | 0, _, _, h => by omega
  | _ + 1, k, 0, _ => by simp [diagTail]
  | m + 1, k, i + 1, h => by
    simp only [diagTail, List.getD_cons_succ, diagTail_getD q m (k + 1) i (by omega)]
    rw [show k + 1 + i = k + (i + 1) by omega]

/-- Indexing `diagFrontier q r` at `i < r` returns `diagSym q i`. -/
theorem diagFrontier_getD (q r i : Nat) (hi : i < r) :
    (diagFrontier q r).getD i (false, false) = diagSym q i := by
  simpa [diagFrontier] using diagTail_getD q r 0 i hi

/-- Every nonempty `diagFrontier q (r + 1)` is a `Legal` frontier (`a₀ = D 1 (q + 1) = true`). -/
theorem diagFrontier_legal (q r : Nat) : Legal (diagFrontier q (r + 1)) := by
  unfold diagFrontier diagTail Legal diagSym
  simp [D_one]

/-- At site `0`, `scanStep (false, false, false) (diagSym q 0)` enters state `diagMem q 0`. -/
theorem scanStep_diagSym_zero (q : Nat) :
    scanStep (false, false, false) (diagSym q 0) = diagMem q 0 := by
  unfold scanStep diagSym diagMem
  simp only [Nat.mul_zero, Nat.zero_add, D_zero, D_one]
  rfl

/-- **Exact Site-by-Site `D` Step (`scanStep_diagMem_succ`):** feeding `diagSym q (k + 1)` into
`scanStep (diagMem q k)` applies `D_step` twice to advance to `diagMem q (k + 1)`. -/
theorem scanStep_diagMem_succ (q k : Nat) :
    scanStep (diagMem q k) (diagSym q (k + 1)) = diagMem q (k + 1) := by
  unfold scanStep diagMem diagSym
  dsimp only
  have h1 := D_step (2 * k) (q + k + 1)
  have h2 := D_step (2 * k + 1) (q + k + 2)
  have e2 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by omega
  have e1 : 2 * (k + 1) = 2 * k + 2 := by omega
  have e5 : q + (k + 1) + 2 = q + k + 2 + 1 := by omega
  have e4 : q + (k + 1) + 1 = q + k + 1 + 1 := by omega
  have e3 : q + (k + 1) = q + k + 1 := by omega
  rw [e2, e1, e5, e4, e3, ← h1]
  have e6 : q + k + 1 + 1 = q + k + 2 := by omega
  have e7 : 2 * k + 2 = 2 * k + 1 + 1 := by omega
  rw [e6, e7, ← h2]

/-- Scanning `diagTail q (k + 1) m` from memory `diagMem q k` advances the time offset from `q` to `q + 1`. -/
theorem scan_diagTail (q : Nat) : ∀ (m k : Nat),
    (scan (diagMem q k) (diagTail q (k + 1) m)).1 = diagTail (q + 1) (k + 1) m
  | 0, _ => rfl
  | m + 1, k => by
    simp only [diagTail, scan, scanStep_diagMem_succ]
    rw [scan_diagTail q m (k + 1)]
    unfold diagMem diagSym
    have e1 : q + 1 + (k + 1) + 1 = q + (k + 1) + 2 := by omega
    have e2 : q + 1 + (k + 1) = q + (k + 1) + 1 := by omega
    rw [e1, e2]

/-- **Exact One-Step Conjugacy (`pureScan_diagFrontier`):** for every time offset `q : Nat` and
frontier length `r : Nat`, `pureScan (diagFrontier q r) = diagFrontier (q + 1) r`. -/
theorem pureScan_diagFrontier (q : Nat) : ∀ r : Nat,
    pureScan (diagFrontier q r) = diagFrontier (q + 1) r
  | 0 => rfl
  | r + 1 => by
    unfold pureScan diagFrontier diagTail
    simp only [scan, scanStep_diagSym_zero]
    rw [scan_diagTail q r 0]
    unfold diagMem diagSym
    simp only [Nat.mul_zero, Nat.zero_add]

/-- **Exact Multi-Step Conjugacy (`iterPureScan_diagFrontier`):** for all `n, q, r : Nat`,
`iterPureScan n (diagFrontier q r) = diagFrontier (q + n) r`. -/
theorem iterPureScan_diagFrontier : ∀ (n q r : Nat),
    iterPureScan n (diagFrontier q r) = diagFrontier (q + n) r
  | 0, q, r => by simp [iterPureScan]
  | n + 1, q, r => by
    rw [iterPureScan, iterPureScan_diagFrontier n q r, pureScan_diagFrontier,
      show q + n + 1 = q + (n + 1) by omega]

/-! ## 3. Exact Conjugacy for the `(true, false)` Branch (`diagFrontierFalse`) -/

/-- The `(k + 1)`-th symbol of the `(true, false)` left-diagonal frontier at time offset `q`:
`(D (2 * k + 2) (q + k + 2), D (2 * k + 1) (q + k + 1))`. -/
def diagSymFalse (q k : Nat) : Sym :=
  (D (2 * k + 2) (q + k + 2), D (2 * k + 1) (q + k + 1))

/-- The 3-bit scan memory after scanning `(true, false)` (`k = 0`) or `diagSymFalse q (k - 1)`:
entering site `k + 1` on the `(true, false)` branch. -/
def diagMemFalse (q k : Nat) : Bool × Bool × Bool :=
  (D (2 * k + 2) (q + k + 3), D (2 * k + 1) (q + k + 2), D (2 * k + 2) (q + k + 2))

/-- Tail of the `(true, false)` left-diagonal frontier from index `k` of length `m`. -/
def diagTailFalse (q k : Nat) : Nat → List Sym
  | 0 => []
  | m + 1 => diagSymFalse q k :: diagTailFalse q (k + 1) m

/-- The canonical `(true, false)` left-diagonal frontier of length `r + 2` at time offset `q`. -/
def diagFrontierFalse (q r : Nat) : List Sym :=
  (true, false) :: (false, true) :: diagTailFalse q 1 r

/-- **Exact Site-by-Site `D` Step on the `(true, false)` Branch (`scanStep_diagMemFalse_succ`):**
feeding `diagSymFalse q (k + 1)` into `scanStep (diagMemFalse q k)` applies `D_step` twice to
advance to `diagMemFalse q (k + 1)`. -/
theorem scanStep_diagMemFalse_succ (q k : Nat) :
    scanStep (diagMemFalse q k) (diagSymFalse q (k + 1)) = diagMemFalse q (k + 1) := by
  unfold scanStep diagMemFalse diagSymFalse
  dsimp only
  have h1 := D_step (2 * k + 1) (q + k + 2)
  have h2 := D_step (2 * k + 2) (q + k + 3)
  have e2 : 2 * (k + 1) + 2 = (2 * k + 2) + 2 := by omega
  have e1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
  have e5 : q + (k + 1) + 3 = q + k + 3 + 1 := by omega
  have e4 : q + (k + 1) + 2 = q + k + 2 + 1 := by omega
  have e3 : q + (k + 1) + 1 = q + k + 2 := by omega
  rw [e2, e1, e5, e4, e3, ← h1]
  have e6 : q + k + 2 + 1 = q + k + 3 := by omega
  have e7 : (2 * k + 1) + 2 = (2 * k + 2) + 1 := by omega
  rw [e6, e7, ← h2]

/-- Scanning `diagTailFalse q (k + 1) m` from `diagMemFalse q k` advances `q` to `q + 1`. -/
theorem scan_diagTailFalse (q : Nat) : ∀ (m k : Nat),
    (scan (diagMemFalse q k) (diagTailFalse q (k + 1) m)).1 = diagTailFalse (q + 1) (k + 1) m
  | 0, _ => rfl
  | m + 1, k => by
    simp only [diagTailFalse, scan, scanStep_diagMemFalse_succ]
    rw [scan_diagTailFalse q m (k + 1)]
    unfold diagMemFalse diagSymFalse
    have e1 : q + 1 + (k + 1) + 2 = q + (k + 1) + 3 := by omega
    have e2 : q + 1 + (k + 1) + 1 = q + (k + 1) + 2 := by omega
    rw [e1, e2]

/-- For every `t : Nat`, `D 2 (t + 2) = false`. -/
theorem D_two_succ_succ (t : Nat) : D 2 (t + 2) = false := by
  have h := D_step 0 (t + 1)
  simp only [Nat.zero_add, D_zero, D_one] at h
  rw [h]; rfl

/-- **Exact One-Step Conjugacy on the `(true, false)` Branch (`pureScan_diagFrontierFalse`):**
for all `q, r : Nat`, `pureScan (diagFrontierFalse q r) = diagFrontierFalse (q + 1) r`. -/
theorem pureScan_diagFrontierFalse (q r : Nat) :
    pureScan (diagFrontierFalse q r) = diagFrontierFalse (q + 1) r := by
  unfold pureScan diagFrontierFalse
  simp only [scan]
  have hm0 : scanStep (scanStep (false, false, false) (true, false)) (false, true) =
      diagMemFalse q 0 := by
    unfold scanStep diagMemFalse
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [D_one (q + 1), D_two_succ_succ (q + 1), D_two_succ_succ q]
    rfl
  rw [hm0, scan_diagTailFalse q r 0]
  unfold diagMemFalse
  simp only [Nat.mul_zero, Nat.zero_add, D_one (q + 1), D_two_succ_succ (q + 1)]
  rfl

/-- **Exact Multi-Step Conjugacy on the `(true, false)` Branch (`iterPureScan_diagFrontierFalse`):**
for all `n, q, r : Nat`, `iterPureScan n (diagFrontierFalse q r) = diagFrontierFalse (q + n) r`. -/
theorem iterPureScan_diagFrontierFalse : ∀ (n q r : Nat),
    iterPureScan n (diagFrontierFalse q r) = diagFrontierFalse (q + n) r
  | 0, q, r => by simp [iterPureScan]
  | n + 1, q, r => by
    rw [iterPureScan, iterPureScan_diagFrontierFalse n q r, pureScan_diagFrontierFalse,
      show q + n + 1 = q + (n + 1) by omega]

/-! ## 4. Terminal Scalar Field `FG` Forced to Equal Rule 30 Left Diagonals & Unbounded Periods -/

/-- **Terminal Scalar Field Matches Rule 30 Left Diagonals (`diagFrontier_terminal_FG`):** in any
successful run `run (diagFrontier q (r + 1)) n = some (w', tape)` with `r + 2 ≤ n + k` (`k < r + 1`),
`FG (window tape) (r + n - k) 0` equals `(D (2 * k + 1) (q + n + k + 1), D (2 * k) (q + n + k))`. -/
theorem diagFrontier_terminal_FG {q r n k : Nat} {w' : List Sym} {tape : List Bool}
    (hrun : run (diagFrontier q (r + 1)) n = some (w', tape))
    (hk : k < r + 1) (hcol : r + 2 ≤ n + k) :
    FG (window tape) (r + n - k) 0 =
      (D (2 * k + 1) (q + n + k + 1), D (2 * k) (q + n + k)) := by
  have hw := diagFrontier_legal q r
  have hlen := diagFrontier_length q (r + 1)
  have hf := front_eq_terminal_FG hw hrun (i := k) (by omega) (by omega)
  rw [hlen, show r + 1 + n - 1 - k = r + n - k by omega] at hf
  rw [← hf, iterPureScan_diagFrontier, diagFrontier_getD (q + n) (r + 1) k hk]
  rfl

/-- **Unbounded Period Exclusion in `iterPureScan` (`diagFrontier_not_evPer`):** for every `L > 0`,
there exists a site `k ≤ 2 ^ (2 * L - 1)` such that one bit of
`n ↦ (iterPureScan n (diagFrontier 0 (k + 1))).getD k (false, false)` is not eventually `L`-periodic. -/
theorem diagFrontier_not_evPer {L : Nat} (hL : 0 < L) :
    ∃ k : Nat, k ≤ 2 ^ (2 * L) ∧
      (¬ EvPer (fun n => ((iterPureScan n (diagFrontier 0 (k + 1))).getD k (false, false)).1) L ∨
       ¬ EvPer (fun n => ((iterPureScan n (diagFrontier 0 (k + 1))).getD k (false, false)).2) L) := by
  obtain ⟨j, hj, hnot⟩ := D_period_unbounded L hL
  refine ⟨j / 2, by omega, ?_⟩
  have hget : ∀ n, (iterPureScan n (diagFrontier 0 (j / 2 + 1))).getD (j / 2) (false, false) =
      (D (2 * (j / 2) + 1) (n + j / 2 + 1), D (2 * (j / 2)) (n + j / 2)) := by
    intro n
    rw [iterPureScan_diagFrontier, diagFrontier_getD _ _ _ (by omega)]
    simp [diagSym]
  rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
  · right
    have hj_eq : 2 * (j / 2) = j := by omega
    simp only [hget, hj_eq]
    intro ⟨T, hT⟩
    apply hnot
    refine ⟨T + j / 2, fun t ht => ?_⟩
    have h1 := hT (t - j / 2) (by omega)
    dsimp only at h1
    rwa [show t - j / 2 + L + j / 2 = t + L by omega,
         show t - j / 2 + j / 2 = t by omega] at h1
  · left
    have hj_eq : 2 * (j / 2) + 1 = j := by omega
    simp only [hget, hj_eq]
    intro ⟨T, hT⟩
    apply hnot
    refine ⟨T + j / 2 + 1, fun t ht => ?_⟩
    have h1 := hT (t - (j / 2 + 1)) (by omega)
    dsimp only at h1
    rwa [show t - (j / 2 + 1) + L + j / 2 + 1 = t + L by omega,
         show t - (j / 2 + 1) + j / 2 + 1 = t by omega] at h1

end Rule30SurvivalBridge
end Ruliology.CellularAutomata
