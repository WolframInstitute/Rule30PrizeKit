module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30TwoSidedInverse

/-!
# Isolated black cells recur in every nine-column strip

Silence of the spatial word 010 in a nine-by-nine rectangle forces the
three interior readings at offsets 2, 3 and 4 to agree five ticks apart.
Two of those columns would become periodic if silence persisted.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SpatialIsolates

open Rule30Jen

/-- A spatial isolated black, with the argument naming its black cell. -/
def Isolate (x : Int → Bool) (p : Int) : Prop :=
  x (p-1) = false ∧ x p = true ∧ x (p+1) = false

private structure Window where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
  g : Bool
  h : Bool
  i : Bool

private def next (x : Window) (l r : Bool) : Window :=
  ⟨rule l x.a x.b, rule x.a x.b x.c, rule x.b x.c x.d, rule x.c x.d x.e,
    rule x.d x.e x.f, rule x.e x.f x.g, rule x.f x.g x.h, rule x.g x.h x.i, rule x.h x.i r⟩

private def quiet (x : Window) : Bool :=
  let q := fun a b c : Bool => a || !b || c
  q x.a x.b x.c && q x.b x.c x.d && q x.c x.d x.e && q x.d x.e x.f &&
    q x.e x.f x.g && q x.f x.g x.h && q x.g x.h x.i

/-- Every path that satisfies the guard through its last row passes the endpoint test. -/
private def safe (guard post : Window → Bool) : Nat → Window → Bool
  | 0, x => !guard x || post x
  | k+1, x => !guard x ||
      (safe guard post k (next x false false) && safe guard post k (next x false true) &&
       safe guard post k (next x true false) && safe guard post k (next x true true))

private def same (x y : Window) := (x.c == y.c) && (x.d == y.d) && (x.e == y.e)

private def certificate := safe quiet (fun x => safe quiet (fun y => same x y ||
  safe quiet (fun _ => false) 2 y) 5 x) 1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem table : ∀ a b c d e f g h i : Bool, certificate ⟨a,b,c,d,e,f,g,h,i⟩ = true := by
  decide +kernel

private theorem safe_spec {guard : Window → Bool} (post : Window → Bool) (x : Nat → Window)
    (step : ∀ t, ∃ l r, x (t+1) = next (x t) l r) (t n : Nat)
    (hq : ∀ j, t ≤ j → j ≤ t+n → guard (x j) = true)
    (hs : safe guard post n (x t) = true) : post (x (t+n)) = true := by
  induction n generalizing t with
  | zero => simpa [safe, hq t (by omega) (by omega)] using hs
  | succ n ih =>
    simp only [safe, hq t (by omega) (by omega), Bool.not_true, Bool.false_or, Bool.and_eq_true] at hs
    obtain ⟨l,r,he⟩ := step t
    have hn : safe guard post n (x (t+1)) = true := by
      rw [he]; cases l <;> cases r
      · exact hs.1.1.1
      · exact hs.1.1.2
      · exact hs.1.2
      · exact hs.2
    simpa only [show t+1+n=t+(n+1) by omega] using
      ih (t+1) (fun j hj hj' => hq j (by omega) (by omega)) hn

private def window (x : Int → Bool) (i : Int) : Window :=
  ⟨x i, x (i+1), x (i+2), x (i+3), x (i+4), x (i+5), x (i+6), x (i+7), x (i+8)⟩

/-- If nine consecutive rows of an arbitrary evolution have no 010 in a fixed
nine-cell window, its cells 2, 3, and 4 agree between rows 1 and 6. -/
theorem strip_lag_five (z : Int → Bool) (T : Nat) (i : Int)
    (h : ∀ k : Nat, k < 9 → ∀ j : Nat, j < 7 →
      ¬ Isolate (Rule30Realization.evol z (T+k)) (i+j+1)) :
    let x := Rule30Realization.evol z
    x (T+1) (i+2) = x (T+6) (i+2) ∧
    x (T+1) (i+3) = x (T+6) (i+3) ∧ x (T+1) (i+4) = x (T+6) (i+4) := by
  let w := fun t => window (Rule30Realization.evol z t) i
  have step (t : Nat) : ∃ l r, w (t+1) = next (w t) l r := by
    refine ⟨Rule30Realization.evol z t (i-1), Rule30Realization.evol z t (i+9), ?_⟩
    simp +arith [w, window, next, Rule30Realization.evol]
  have clean (s : Nat) (lo : T ≤ s) (hi : s ≤ T+8) : quiet (w s) = true := by
    have no (j : Nat) (hj : j < 7) := h (s-T) (by omega) j hj
    simp only [show T+(s-T) = s by omega] at no
    have test (a b c : Bool) (hn : ¬(a=false ∧ b=true ∧ c=false)) : (a || !b || c) = true := by
      cases a <;> cases b <;> cases c <;> simp_all
    have q (j : Nat) (hj : j < 7) := test _ _ _ (no j hj)
    simp only [quiet, w, window, Bool.and_eq_true]
    simpa +arith using And.intro (And.intro (And.intro (And.intro (And.intro
      (And.intro (q 0 (by decide)) (q 1 (by decide))) (q 2 (by decide)))
      (q 3 (by decide))) (q 4 (by decide))) (q 5 (by decide))) (q 6 (by decide))
  have h0 : certificate (w T) = true := by
    generalize w T = x; cases x; apply table
  have h1 := safe_spec _ w step T 1 (fun s hl hh => clean s hl (by omega)) h0
  have h6 := safe_spec _ w step (T+1) 5 (fun s hl hh => clean s (by omega) (by omega)) h1
  change (same (w (T+1)) (w (T+6)) || safe quiet (fun _ => false) 2 (w (T+6))) = true at h6
  simp only [Bool.or_eq_true] at h6
  rcases h6 with good | bad
  · simpa only [same, w, window, Bool.and_eq_true, beq_iff_eq, and_assoc] using good
  · exact Bool.noConfusion (safe_spec _ w step (T+6) 2 (fun s hl hh => clean s (by omega) (by omega)) bad)

private theorem lag_of_quiet (T : Nat) (i : Int)
    (h : ∀ k : Nat, k < 9 → ∀ j : Nat, j < 7 → ¬ Isolate (cell (T+k)) (i+j+1)) :
    cell (T+1) (i+2) = cell (T+6) (i+2) ∧
    cell (T+1) (i+3) = cell (T+6) (i+3) ∧ cell (T+1) (i+4) = cell (T+6) (i+4) := by
  simpa only [Rule30Realization.evol_seed] using
    strip_lag_five Rule30Realization.seed T i (by simpa only [Isolate, Rule30Realization.evol_seed] using h)

/-- In every fixed window of nine cells, a spatial 010 occurs arbitrarily
late in the true singleton evolution. Its center is one of the seven
interior sites. -/
theorem cofinal_isolate (i : Int) (T : Nat) :
    ∃ t ≥ T, ∃ p : Int, i+1 ≤ p ∧ p ≤ i+7 ∧ Isolate (cell t) p := by
  apply Classical.byContradiction
  intro h
  have lag (s : Nat) (hs : T ≤ s) := lag_of_quiet s i (fun k _ j hj iso =>
    h ⟨s+k, by omega, i+j+1, by omega, by omega, iso⟩)
  apply jen (i+2) (i+3) (by omega)
  constructor
  · refine ⟨T+1, 5, by decide, fun t ht => ?_⟩
    simpa only [show t-1+1=t by omega, show t-1+6=t+5 by omega] using (lag (t-1) (by omega)).1.symm
  · refine ⟨T+1, 5, by decide, fun t ht => ?_⟩
    simpa only [show t-1+1=t by omega, show t-1+6=t+5 by omega] using (lag (t-1) (by omega)).2.1.symm

open Rule30TwoSidedInverse

private theorem black_behind (x : Int → Bool) (j : Int) (h : Isolate (stepLine x) j) :
    x (j-2) = true := by
  have tab : ∀ a b c d e : Bool, rule a b c=false → rule b c d=true → rule c d e=false →
      a=true := by decide +kernel
  apply tab _ (x (j-1)) (x j) (x (j+1)) (x (j+2))
  · simpa +arith [stepLine] using h.1
  · exact h.2.1
  · simpa +arith [stepLine] using h.2.2

/-- An isolate in the common observed eastern interval makes the earlier bit
at p independent of both full-line completions. -/
theorem read_west_of_isolate (x y : Int → Bool) (p j : Int) (hj : p+2 ≤ j)
    (iso : Isolate (stepLine x) j)
    (he : ∀ q, p+1 ≤ q → q ≤ j+1 → stepLine x q = stepLine y q) :
    x p = y p := by
  have iso' : Isolate (stepLine y) j := by
    unfold Isolate at *
    rw [← he (j-1) (by omega) (by omega), ← he j (by omega) (by omega),
      ← he (j+1) (by omega) (by omega)]
    exact iso
  have hx := black_behind x j iso
  have hy := black_behind y j iso'
  by_cases hp : p=j-2
  · simpa only [hp] using hx.trans hy.symm
  have lx (z : Int → Bool) (q : Int) := left_of (stepLine z) z (fun _ => rfl) q
  have base : x (j-2-1) = y (j-2-1) := by
    rw [lx x (j-2), lx y (j-2), hx, hy, he _ (by omega) (by omega)]
    simp
  have descend (k : Nat) (hk : p ≤ j-3-k) :
      x (j-3-k) = y (j-3-k) ∧ x (j-3-k+1) = y (j-3-k+1) := by
    induction k with
    | zero => simpa +arith using And.intro base (hx.trans hy.symm)
    | succ k ih =>
      obtain ⟨h1,h2⟩ := ih (by omega)
      have := lx x (j-3-k)
      rw [he _ (by omega) (by omega), h1,h2, ← lx y] at this
      simpa +arith using And.intro this h1
  simpa only [show j-3-((j-3-p).toNat:Int)=p by omega] using (descend (j-3-p).toNat (by omega)).1

/-- Arbitrarily late, the nine sites strictly east of p in the next row
suffice to read the current bit at p against every competing full-line row. -/
theorem cofinal_nine_cell_readout (p : Int) (T : Nat) :
    ∃ t ≥ T, ∀ z : Int → Bool,
      (∀ q, p+1 ≤ q → q ≤ p+9 → stepLine z q = cell (t+1) q) → z p = cell t p := by
  obtain ⟨s,hs,j,hj,hj',iso⟩ := cofinal_isolate (p+1) (T+1)
  let t := s-1
  have et : t+1=s := by dsimp [t]; omega
  refine ⟨t, by dsimp [t]; omega, fun z hz => ?_⟩
  apply Eq.symm
  apply read_west_of_isolate (cell t) z p j (by omega)
  · change Isolate (cell (t+1)) j
    simpa only [et] using iso
  · exact fun q h1 h2 => (hz q h1 (by omega)).symm

private def Lag (t : Nat) (j : Int) := cell t j = cell (t+5) j

private theorem lag_west (t n : Nat) (j : Int)
    (h : ∀ k : Nat, k ≤ n → Lag (t+k) j ∧ Lag (t+k) (j+1)) : Lag t (j-n) := by
  induction n generalizing j with
  | zero => simpa using (h 0 (by omega)).1
  | succ n ih =>
    have hh (k : Nat) (hk : k ≤ n) : Lag (t+k) (j-1) ∧ Lag (t+k) (j-1+1) := by
      obtain ⟨a,b⟩ := h k (by omega)
      have c := (h (k+1) (by omega)).1
      refine ⟨?_, by simpa using a⟩
      unfold Lag at *
      rw [cell_left (t+k), cell_left (t+k+5), a,b,
        show t+k+5+1 = t+(k+1)+5 by omega, ← c]
      rfl
    simpa +arith using ih (j-1) hh

/-- A discrepancy five ticks apart forces an isolated black strictly to the
east during an explicit twelve-row window. -/
theorem eastern_isolate_of_mismatch (p : Int) (T : Nat)
    (hm : cell (T+1) p ≠ cell (T+6) p) :
    ∃ k : Nat, k ≤ 11 ∧ ∃ j : Int, p+2 ≤ j ∧ j ≤ p+8 ∧ Isolate (cell (T+k)) j := by
  apply Classical.byContradiction
  intro no
  have h (k : Nat) (hk : k ≤ 3) := lag_of_quiet (T+k) (p+1) (fun a ha b hb iso =>
    no ⟨k+a, by omega, p+1+b+1, by omega, by omega, by simpa [Nat.add_assoc] using iso⟩)
  apply hm
  have h' := lag_west (T+1) 3 (p+3) (fun k hk => by
    simpa +arith [Lag] using And.intro (h k hk).1 (h k hk).2.1)
  simpa +arith [Lag] using h'

/-- A hypothetical period-three tail forces an isolated black in the next
fourteen rows of the nine-cell window strictly east of that column. -/
theorem period_three_eastern_isolate (p : Int) (A : Nat)
    (period : ∀ t ≥ A, cell (t+3) p = cell t p) (T : Nat) (hT : A ≤ T) :
    ∃ k : Nat, k ≤ 13 ∧ ∃ j : Int, p+2 ≤ j ∧ j ≤ p+8 ∧ Isolate (cell (T+k)) j := by
  apply Classical.byContradiction
  intro no
  have eq5 (k : Nat) (hk : k ≤ 2) : cell (T+k+1) p = cell (T+k+6) p := by
    apply Classical.byContradiction
    intro hm
    obtain ⟨u,hu,j,hl,hh,iso⟩ := eastern_isolate_of_mismatch p (T+k) hm
    exact no ⟨k+u, by omega, j, hl, hh, by simpa [Nat.add_assoc] using iso⟩
  have e0 : cell (T+1) p = cell (T+3) p := (eq5 0 (by decide)).trans (period (T+3) (by omega))
  have e1 : cell (T+2) p = cell (T+1) p :=
    (eq5 1 (by decide)).trans ((period (T+4) (by omega)).trans (period (T+1) (by omega)))
  apply Rule30Prize.no_column_eventually_constant p
  refine ⟨T+1, cell (T+1) p, ?_⟩
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    by_cases small : t ≤ T+3
    · have h : t=T+1 ∨ t=T+2 ∨ t=T+3 := by omega
      rcases h with rfl | rfl | rfl
      · rfl
      · exact e1
      · exact e0.symm
    · exact (show cell t p = cell (t-3) p by
        simpa only [show t-3+3=t by omega] using period (t-3) (by omega)).trans
        (ih (t-3) (by omega) (by omega))

private def rewind (w : Window) (s : Bool × Bool) : Bool :=
  (pstep w.a (pstep w.b (pstep w.c (pstep w.d
    (pstep w.e (pstep w.f (pstep w.g (pstep w.h s)))))))).1

private def ambiguous (w : Window) : Bool :=
  let b := rewind w (false,false)
  b != rewind w (false,true) || b != rewind w (true,false) || b != rewind w (true,true)

private def blackCheck := safe ambiguous (fun x => safe ambiguous (fun y =>
  (y.a == (x.a || x.b)) || safe ambiguous (fun _ => false) 3 y) 1 x) 1

private theorem black_table : ∀ a b c d e f g h i : Bool,
    blackCheck ⟨a,b,c,d,e,f,g,h,i⟩ = true := by decide +kernel

private theorem rewind_actual (x : Int → Bool) (p : Int) :
    rewind (window (stepLine x) (p+1)) (x (p+8), x (p+9)) = x p := by
  simp +arith [rewind, window, pstep, stepLine, rule]

private theorem readable_at (v : Int → Bool) (p : Int)
    (hr : ambiguous (window (stepLine v) (p+1)) = false) (z : Int → Bool)
    (h : ∀ q, p+1 ≤ q → q ≤ p+8 → stepLine z q = stepLine v q) : z p = v p := by
  let w := window (stepLine v) (p+1)
  have unique (a b : Bool) : rewind w (a,b) = rewind w (false,false) := by
    change ambiguous w = false at hr
    simp only [ambiguous, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hr
    cases a <;> cases b
    · rfl
    · exact hr.1.1.symm
    · exact hr.1.2.symm
    · exact hr.2.symm
  have copy (s : Bool × Bool) : rewind (window (stepLine z) (p+1)) s = rewind w s := by
    simp +arith [rewind, window, w, h _ (by omega : p+1 ≤ p+1) (by omega),
      h _ (by omega : p+1 ≤ p+2) (by omega), h _ (by omega : p+1 ≤ p+3) (by omega),
      h _ (by omega : p+1 ≤ p+4) (by omega), h _ (by omega : p+1 ≤ p+5) (by omega),
      h _ (by omega : p+1 ≤ p+6) (by omega), h _ (by omega : p+1 ≤ p+7) (by omega),
      h _ (by omega : p+1 ≤ p+8) (by omega)]
  exact (rewind_actual z p).symm.trans ((copy _).trans ((unique _ _).trans
    ((unique (v (p+8)) (v (p+9))).symm.trans (rewind_actual v p))))

/-- In any Rule 30 orbit, a black cell at T+2 guarantees a bit at that site
is readable from eight cells of its following row at some time in T through
T+5. The readable bit can have either color. -/
theorem eight_cell_readout_near_black (v : Int → Bool) (T : Nat) (p : Int)
    (black : Rule30Realization.evol v (T+2) p = true) :
    ∃ k : Nat, k ≤ 5 ∧ ∀ z : Int → Bool,
      (∀ q, p+1 ≤ q → q ≤ p+8 → stepLine z q = Rule30Realization.evol v (T+k+1) q) →
      z p = Rule30Realization.evol v (T+k) p := by
  let x := Rule30Realization.evol v
  let w := fun t => window (x t) (p+1)
  have step (t : Nat) : ∃ l r, w (t+1) = next (w t) l r := by
    refine ⟨x t p, x t (p+10), ?_⟩
    simp +arith [w, x, window, next, Rule30Realization.evol]
  have ex : ∃ k : Nat, k ≤ 5 ∧ ambiguous (w (T+k+1)) = false := by
    apply Classical.byContradiction
    intro no
    have amb (t : Nat) (hl : T+1 ≤ t) (hh : t ≤ T+6) : ambiguous (w t) = true := by
      cases h : ambiguous (w t)
      · exact False.elim (no ⟨t-(T+1), by omega, by rwa [show T+(t-(T+1))+1=t by omega]⟩)
      · rfl
    have base : blackCheck (w (T+1)) = true := by generalize w (T+1) = a; cases a; apply black_table
    have h2 := safe_spec _ w step (T+1) 1 (fun t hl hh => amb t hl (by omega)) base
    have h3 := safe_spec _ w step (T+2) 1 (fun t hl hh => amb t (by omega) (by omega)) h2
    change ((_ == _) || safe ambiguous (fun _ => false) 3 (w (T+3))) = true at h3
    simp only [Bool.or_eq_true, beq_iff_eq] at h3
    rcases h3 with bad | bad
    · have hx := left_of (x (T+3)) (x (T+2)) (fun _ => rfl) (p+1)
      change x (T+3) (p+1) = (x (T+2) (p+1) || x (T+2) (p+1+1)) at bad
      simp only [bad, Bool.xor_self, Int.add_sub_cancel] at hx
      exact Bool.noConfusion (black.symm.trans hx)
    · exact Bool.noConfusion (safe_spec _ w step (T+3) 3 (fun t hl hh => amb t (by omega) (by omega)) bad)
  obtain ⟨k,hk,hr⟩ := ex
  exact ⟨k,hk,readable_at (x (T+k)) p hr⟩

/-- The eight-cell readout occurs arbitrarily late at every singleton column. -/
theorem cofinal_eight_cell_readout (p : Int) (T : Nat) :
    ∃ t ≥ T, ∀ z : Int → Bool,
      (∀ q, p+1 ≤ q → q ≤ p+8 → stepLine z q = cell (t+1) q) → z p = cell t p := by
  have ex : ∃ s ≥ T+2, cell s p = true := by
    apply Classical.byContradiction
    intro no
    apply Rule30Prize.no_column_eventually_constant p
    refine ⟨T+2, false, fun t ht => ?_⟩
    cases e : cell t p
    · rfl
    · exact False.elim (no ⟨t, ht, e⟩)
  obtain ⟨s,hs,hb⟩ := ex
  have black : Rule30Realization.evol Rule30Realization.seed (s-2+2) p = true := by
    simpa only [Rule30Realization.evol_seed, show s-2+2=s by omega] using hb
  obtain ⟨k,_,h⟩ := eight_cell_readout_near_black _ _ _ black
  exact ⟨s-2+k, by omega, by simpa only [Rule30Realization.evol_seed] using h⟩

/-- The spatially repeating 11100 wave and its 00001 alternative parent. -/
def wave (t : Nat) (p : Int) : Bool := decide ((p+2*(t:Int)) % 5 < 3)
def other (t : Nat) (p : Int) : Bool := decide ((p+2*(t:Int)) % 5 = 4)

/-- At every time, both parents give the same entire next row, and the
alternative parent is white at every black cell of the wave. Increasing
the readout window can never certify a black reading on this orbit. -/
theorem wave_hides_every_black (t : Nat) :
    stepLine (wave t) = wave (t+1) ∧ stepLine (other t) = wave (t+1) ∧
    ∀ p, wave t p = true → other t p = false := by
  have row (p : Int) : stepLine (wave t) p = wave (t+1) p ∧
      stepLine (other t) p = wave (t+1) p := by
    let k := p+2*(t:Int)
    have h : k%5=0 ∨ k%5=1 ∨ k%5=2 ∨ k%5=3 ∨ k%5=4 := by omega
    have normal : p+2*((t+1:Nat):Int) = k+2 := by dsimp [k]; omega
    simp only [stepLine, wave, other, rule, normal,
      show p-1+2*(t:Int)=k-1 by dsimp [k]; omega,
      show p+1+2*(t:Int)=k+1 by dsimp [k]; omega]
    change (xor _ (decide (k%5 < 3) || _) = _) ∧ (xor _ (decide (k%5 = 4) || _) = _)
    rw [show (k-1)%5=(k%5+4)%5 by omega,
      show (k+1)%5=(k%5+1)%5 by omega, show (k+2)%5=(k%5+2)%5 by omega]
    rcases h with h | h | h | h | h <;>
      rw [h] <;> decide
  exact ⟨funext (fun p => (row p).1), funext (fun p => (row p).2), fun p h => by
    simp only [wave, decide_eq_true_eq] at h
    simp only [other, decide_eq_false_iff_not]; omega⟩

private def both (f : Bool → Bool) := f false && f true

private theorem both_at {f : Bool → Bool} (h : both f = true) (b : Bool) : f b = true := by
  simp only [both, Bool.and_eq_true] at h
  cases b
  · exact h.1
  · exact h.2

/-- Starting at the black tick of 001, the drives on the three outgoing
steps are black, white, white. Only the eastern input is free. -/
private def rank (x : Window) : Nat :=
  let n := x.a.toNat + 2*x.b.toNat + 4*x.c.toNat + 8*x.d.toNat +
    16*x.e.toNat + 32*x.f.toNat + 64*x.g.toNat + 128*x.h.toNat
  if (0x8000000000000000001000000000000080000000000000000000000000 : Nat).testBit n then 5
  else if (0x41008000008080000000001000000010410080000000000000000000004080 : Nat).testBit n then 4
  else if (0x804190c00000c0800000000010000002904190c200000000c002000010004080 : Nat).testBit n then 3
  else if (0x82c190c20200c08180c000001100c08290c190c200000000c2c300001000c080 : Nat).testBit n then 2
  else if ambiguous x then 1 else 0

private def rankCheck (x : Window) := decide (rank x ≤ 5) && (!ambiguous x ||
  (decide (0 < rank x) && both (fun a => both (fun b => both (fun c =>
    decide (rank (next (next (next x true a) false b) false c) < rank x))))))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem stride_table : ∀ a b c d e f g h i : Bool,
    rankCheck ⟨a,b,c,d,e,f,g,h,i⟩ = true := by decide +kernel

/-- Six samples spaced three ticks apart cannot all admit both parent
colors at the black image phase of a 001 tail. The observed past phase
is the white tick immediately before black. -/
theorem one_in_six_readable_of_001 (v : Int → Bool) (p : Int) (T : Nat)
    (clock : ∀ k : Nat, k < 5 →
      Rule30Realization.evol v (T+1+3*k) p = true ∧
      Rule30Realization.evol v (T+1+3*k+1) p = false ∧
      Rule30Realization.evol v (T+1+3*k+2) p = false) :
    ∃ k : Nat, k ≤ 5 ∧ ∀ z : Int → Bool,
      (∀ q, p+1 ≤ q → q ≤ p+8 → stepLine z q = Rule30Realization.evol v (T+3*k+1) q) →
      z p = Rule30Realization.evol v (T+3*k) p := by
  let x := Rule30Realization.evol v
  let w := fun t => window (x t) (p+1)
  have step (s : Nat) : w (s+1) = next (w s) (x s p) (x s (p+10)) := by
    simp +arith [w, x, window, next, Rule30Realization.evol]
  have ex : ∃ k : Nat, k ≤ 5 ∧ ambiguous (w (T+1+3*k)) = false := by
    apply Classical.byContradiction
    intro no
    have amb (k : Nat) (hk : k ≤ 5) : ambiguous (w (T+1+3*k)) = true := by
      cases h : ambiguous (w (T+1+3*k))
      · exact False.elim (no ⟨k,hk,h⟩)
      · rfl
    have valid (a : Window) : rankCheck a = true := by cases a; apply stride_table
    have bounds (k : Nat) (hk : k ≤ 5) :
        let a := w (T+1+3*k)
        rank a ≤ 5 ∧ 0 < rank a ∧ both (fun l => both (fun r => both (fun s =>
          decide (rank (next (next (next a true l) false r) false s) < rank a)))) = true := by
      have hv := valid (w (T+1+3*k))
      simp only [rankCheck, amb k hk, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        decide_eq_true_eq] at hv
      exact hv
    have walk (k : Nat) (hk : k ≤ 5) : rank (w (T+1+3*k)) + k ≤ 5 := by
      induction k with
      | zero => exact (bounds 0 (by omega)).1
      | succ k ih =>
        have h := ih (by omega)
        have fall := (bounds k (by omega)).2.2
        let s := T+1+3*k
        obtain ⟨ha,hb,hc⟩ := clock k (by omega)
        change x s p = true at ha
        change x (s+1) p = false at hb
        change x (s+2) p = false at hc
        rw [show T+1+3*(k+1) = s+2+1 by dsimp [s]; omega,
          step (s+2), step (s+1), step s, ha,hb,hc]
        have dec := both_at (both_at (both_at fall (x s (p+10))) (x (s+1) (p+10))) (x (s+2) (p+10))
        simp only [decide_eq_true_eq] at dec
        change rank (next (next (next (w s) true _) false _) false _) < rank (w s) at dec
        change rank (w s) + k ≤ 5 at h
        omega
    have h := walk 5 (by decide)
    have pos := (bounds 5 (by decide)).2.1
    omega
  obtain ⟨k,hk,hr⟩ := ex
  refine ⟨k,hk,readable_at (x (T+3*k)) p ?_⟩
  change ambiguous (w (T+3*k+1)) = false
  simpa only [show T+3*k+1=T+1+3*k by omega] using hr

/-- The observed eight-cell singleton word has two compatible parents that
disagree at p. Both completions are unrestricted configurations of the line. -/
def AmbiguousAt (p : Int) (s : Nat) : Prop :=
  ∃ x y : Int → Bool, x p ≠ y p ∧
    (∀ q, p+1 ≤ q → q ≤ p+8 → stepLine x q = cell s q) ∧
    (∀ q, p+1 ≤ q → q ≤ p+8 → stepLine y q = cell s q)

/-- A sufficient condition to eliminate the singleton's 001 tail up to phase:
six ambiguous snapshots at stride three, arbitrarily late on each residue. -/
theorem no_001_of_six_ambiguities (p : Int)
    (blocks : ∀ T : Nat, ∃ s ≥ T, s%3=T%3 ∧ ∀ k ≤ 5, AmbiguousAt p (s+3*k)) :
    ¬ ∃ A : Nat, ∀ k : Nat, cell (A+3*k) p = true ∧
      cell (A+3*k+1) p = false ∧ cell (A+3*k+2) p = false := by
  rintro ⟨A, clock⟩
  obtain ⟨s,hs,ph,bad⟩ := blocks (A+3)
  have base : A+3*((s-A)/3)=s := by omega
  have drive (k : Nat) (_ : k<5) := clock ((s-A)/3+k)
  have sameAge (k : Nat) : A+3*((s-A)/3+k) = s-1+1+3*k := by omega
  obtain ⟨k,hk,read⟩ := one_in_six_readable_of_001 Rule30Realization.seed p (s-1)
    (fun k hk => by simpa only [Rule30Realization.evol_seed, sameAge k] using drive k hk)
  obtain ⟨x,y,diff,hx,hy⟩ := bad k hk
  simp only [Rule30Realization.evol_seed, show s-1+3*k+1=s+3*k by omega] at read
  exact diff ((read x hx).trans (read y hy).symm)

end Ruliology.CellularAutomata.Rule30SpatialIsolates
