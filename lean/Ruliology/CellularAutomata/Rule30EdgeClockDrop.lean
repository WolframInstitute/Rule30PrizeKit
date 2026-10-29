module

public import Ruliology.CellularAutomata.Rule30FrozenRuler

/-!
# A period drop cannot follow an antiperiodic parent

This is a local, unbounded-time result for the triangular Rule 30 edge
recurrence. It does not prove period monotonicity when the two preceding
columns have the same least period. No finite search is a premise.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30EdgeClockDrop

def Periodic (x : Nat → Bool) (h : Nat) : Prop := ∀ t, x (t+h) = x t
def Antiperiodic (x : Nat → Bool) (h : Nat) : Prop := ∀ t, x (t+h) = !(x t)

private theorem hidden_flip (a b c d : Bool)
    (s : d = xor c (a || b)) (s' : d = xor c ((!a) || b)) : b = true := by
  revert s s'
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem alternating_xor_constant (v w : Nat → Bool)
    (hv : ∀ t, v (t+1) = !(v t)) (hw : ∀ t, w (t+1) = !(w t)) :
    ∀ t, xor (v t) (w t) = xor (v 0) (w 0) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [hv, hw]
      have key (a b : Bool) : xor (!a) (!b) = xor a b := by
        cases a <;> cases b <;> rfl
      rw [key, ih]

/-- If the older column repeats after h and the previous column is
complemented after h, the next column cannot repeat after h. The auxiliary
older input is arbitrary; even a white boundary is unnecessary here. -/
theorem no_drop_after_antiperiod (u v w r : Nat → Bool) (h : Nat)
    (hu : Periodic u h) (hv : Antiperiodic v h)
    (sv : ∀ t, v (t+1) = xor (v t) (u t || r t))
    (sw : ∀ t, w (t+1) = xor (w t) (v t || u t)) :
    ¬ Periodic w h := by
  intro hw
  have black : ∀ t, u t = true := by
    intro t
    have shifted := sw (t+h)
    rw [show t+h+1 = (t+1)+h by omega, hw (t+1), hw t, hv t, hu t] at shifted
    exact hidden_flip (v t) (u t) (w t) (w (t+1)) (sw t) shifted
  have av : ∀ t, v (t+1) = !(v t) := by
    intro t
    rw [sv, black]
    cases v t <;> rfl
  have aw : ∀ t, w (t+1) = !(w t) := by
    intro t
    rw [sw, black]
    cases v t <;> cases w t <;> rfl
  have eq := alternating_xor_constant v w av aw h
  have vh : v h = !(v 0) := by simpa using hv 0
  have wh : w h = w 0 := by simpa using hw 0
  rw [vh, wh] at eq
  have impossible (a b : Bool) : xor (!a) b ≠ xor a b := by
    cases a <;> cases b <;> decide
  exact impossible (v 0) (w 0) eq

/-- The triangular update written as a spacetime recurrence. -/
def Triangular (x : Nat → Nat → Bool) : Prop :=
  ∀ j t, x (j+2) (t+1) = xor (x (j+2) t) (x (j+1) t || x j t)

private theorem driver_false (a b : Bool) (eq : a = xor a b) : b = false := by
  revert eq
  cases a <;> cases b <;> decide

/-- A constant column forces every older column to be identically white.
Only the triangular recurrence and its special first-column case are used. -/
theorem constant_column_white_prefix (x : Nat → Nat → Bool)
    (hs : ∀ t, x 1 (t+1) = xor (x 1 t) (x 0 t)) (hx : Triangular x) (j : Nat) :
    (∀ t, x j t = x j 0) → ∀ i, i < j → ∀ t, x i t = false := by
  induction j with
  | zero => intro hc i hi; omega
  | succ j ih =>
      intro hc
      cases j with
      | zero =>
          intro i hi t
          have hi0 : i = 0 := by omega
          subst i
          have eq := hs t
          rw [hc (t+1), hc t] at eq
          exact driver_false _ _ eq
      | succ n =>
          have white : ∀ t, x (n+1) t = false := by
            intro t
            have eq := hx n t
            rw [hc (t+1), hc t] at eq
            have h0 := driver_false _ _ eq
            have gate (a b : Bool) (h : (a || b) = false) : a = false := by
              revert h
              cases a <;> cases b <;> decide
            exact gate _ _ h0
          have older := ih (fun t => (white t).trans (white 0).symm)
          intro i hi t
          by_cases he : i = n+1
          · subst i; exact white t
          · exact older i (by omega) t

/-- An application at every interior position of any triangular history. -/
theorem no_drop_at_step (x : Nat → Nat → Bool) (hx : Triangular x) (j h : Nat)
    (hp : Periodic (x (j+1)) h) (ha : Antiperiodic (x (j+2)) h) :
    ¬ Periodic (x (j+3)) h := by
  apply no_drop_after_antiperiod (x (j+1)) (x (j+2)) (x (j+3)) (x j) h hp ha
  · exact hx j
  · exact hx (j+1)

theorem iter_triangular (c : Nat → Bool) :
    Triangular (fun j t => Rule30FrozenRuler.iter t c j) := by
  intro j t
  rfl

/-- On the official edge map, a clock-one column has an entirely white
older prefix. In particular, a nonconstant column cannot be followed by
a constant one. -/
theorem edge_constant_column_white_prefix (c : Nat → Bool) (j : Nat)
    (hc : ∀ t, Rule30FrozenRuler.iter t c j = c j) :
    ∀ i, i < j → ∀ t, Rule30FrozenRuler.iter t c i = false := by
  apply constant_column_white_prefix (fun i t => Rule30FrozenRuler.iter t c i)
    (fun _ => rfl) (iter_triangular c) j
  exact hc

/-- On the official edge map, no period h of column j can be followed by
an antiperiod h at j+1 and then a period h at j+2. This includes the first
two nonconstant edge columns and arbitrary initial codes. -/
theorem edge_no_drop_after_antiperiod (c : Nat → Bool) (j h : Nat)
    (hp : Periodic (fun t => Rule30FrozenRuler.iter t c j) h)
    (ha : Antiperiodic (fun t => Rule30FrozenRuler.iter t c (j+1)) h) :
    ¬ Periodic (fun t => Rule30FrozenRuler.iter t c (j+2)) h := by
  cases j with
  | zero =>
      apply no_drop_after_antiperiod
        (fun t => Rule30FrozenRuler.iter t c 0)
        (fun t => Rule30FrozenRuler.iter t c 1)
        (fun t => Rule30FrozenRuler.iter t c 2)
        (fun _ => false) h hp ha
      · intro t
        change xor (Rule30FrozenRuler.iter t c 1) (Rule30FrozenRuler.iter t c 0) =
          xor (Rule30FrozenRuler.iter t c 1) (Rule30FrozenRuler.iter t c 0 || false)
        simp
      · intro t; rfl
  | succ j =>
      exact no_drop_at_step (fun j t => Rule30FrozenRuler.iter t c j)
        (iter_triangular c) j h hp ha


/-! ### Arbitrarily deep older context does not replace the white boundary

The following cyclic column words have a four-column spatial carrier. One
exit from that carrier produces adjacent least temporal periods eight and
two. Repeating the carrier supplies any desired amount of older context.
The two oldest boundary columns are free, nonconstant period-eight inputs;
these are NOT finite white-boundary edge orbits.
-/

def phaseWord (w t : Nat) : Bool := Nat.testBit w (t % 8)

def CyclicStep (s z : Nat × Nat) : Prop :=
  z.1 = s.2 ∧ ∀ t : Fin 8,
    phaseWord z.2 (t.val+1) =
      xor (phaseWord z.2 t.val) (phaseWord s.2 t.val || phaseWord s.1 t.val)

instance (s z : Nat × Nat) : Decidable (CyclicStep s z) := inferInstanceAs
  (Decidable (z.1 = s.2 ∧ ∀ t : Fin 8,
    phaseWord z.2 (t.val+1) =
      xor (phaseWord z.2 t.val) (phaseWord s.2 t.val || phaseWord s.1 t.val)))

theorem cyclic_step_all_time (s z : Nat × Nat) (h : CyclicStep s z) (t : Nat) :
    z.1 = s.2 ∧ phaseWord z.2 (t+1) =
      xor (phaseWord z.2 t) (phaseWord s.2 t || phaseWord s.1 t) := by
  refine ⟨h.1, ?_⟩
  have ht := h.2 ⟨t % 8, by omega⟩
  simpa [phaseWord, Nat.add_mod] using ht

inductive CyclicWalk : Nat → (Nat × Nat) → (Nat × Nat) → Prop
  | nil (s) : CyclicWalk 0 s s
  | cons {n s u z} : CyclicStep s u → CyclicWalk n u z → CyclicWalk (n+1) s z

theorem cyclic_walk_append {m n : Nat} {s u z : Nat × Nat}
    (a : CyclicWalk m s u) (b : CyclicWalk n u z) : CyclicWalk (m+n) s z := by
  induction a with
  | nil => simpa using b
  | @cons k s v u hs rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        CyclicWalk.cons hs (ih b)

theorem carrier_cycle : CyclicWalk 4 (86,149) (86,149) := by
  apply CyclicWalk.cons (u := (149,101)) (by decide)
  apply CyclicWalk.cons (u := (101,89)) (by decide)
  apply CyclicWalk.cons (u := (89,86)) (by decide)
  apply CyclicWalk.cons (u := (86,149)) (by decide)
  exact CyclicWalk.nil _

theorem carrier_repeat (n : Nat) : CyclicWalk (4*n) (86,149) (86,149) := by
  induction n with
  | zero => exact CyclicWalk.nil _
  | succ n ih =>
      simpa [Nat.mul_succ] using cyclic_walk_append ih carrier_cycle

theorem carrier_exit : CyclicWalk 4 (86,149) (234,170) := by
  apply CyclicWalk.cons (u := (149,154)) (by decide)
  apply CyclicWalk.cons (u := (154,21)) (by decide)
  apply CyclicWalk.cons (u := (21,234)) (by decide)
  apply CyclicWalk.cons (u := (234,170)) (by decide)
  exact CyclicWalk.nil _

/-- An unbounded family of recurrence-compatible strips, with a period
drop at their newer end. The boundary inputs are deliberately free. -/
theorem arbitrary_older_context (n : Nat) :
    CyclicWalk (4*n+4) (86,149) (234,170) :=
  cyclic_walk_append (carrier_repeat n) carrier_exit

def WordPeriod (w p : Nat) : Prop := ∀ t : Fin 8,
  phaseWord w (t.val+p) = phaseWord w t.val

instance (w p : Nat) : Decidable (WordPeriod w p) := inferInstanceAs
  (Decidable (∀ t : Fin 8, phaseWord w (t.val+p) = phaseWord w t.val))

theorem word_period_all_time (w p : Nat) (hp : WordPeriod w p) :
    Periodic (phaseWord w) p := by
  intro t
  have ht := hp ⟨t % 8, by omega⟩
  simpa [phaseWord, Nat.add_mod] using ht

def LeastPositivePeriod (x : Nat → Bool) (p : Nat) : Prop :=
  0 < p ∧ Periodic x p ∧ ∀ h, 0 < h → h < p → ¬ Periodic x h

theorem word_least_period {w p : Nat} (hpos : 0 < p) (hbound : p ≤ 8)
    (hp : WordPeriod w p)
    (hsmall : ∀ h : Fin 8, 0 < h.val → h.val < p → ¬ WordPeriod w h.val) :
    LeastPositivePeriod (phaseWord w) p := by
  refine ⟨hpos, word_period_all_time w p hp, ?_⟩
  intro h hh hlt hper
  apply hsmall ⟨h, by omega⟩ hh hlt
  intro t
  exact hper t.val

theorem exit_periods : LeastPositivePeriod (phaseWord 234) 8 ∧
    LeastPositivePeriod (phaseWord 170) 2 := by
  constructor
  · exact word_least_period (by decide) (by decide) (by decide) (by decide)
  · exact word_least_period (by decide) (by decide) (by decide) (by decide)

/-- The construction cannot be mistaken for a white or constant older boundary. -/
theorem carrier_boundary_nonconstant : phaseWord 86 0 ≠ phaseWord 86 1 := by decide

theorem arbitrary_compatible_period_drop (n : Nat) :
    CyclicWalk (4*n+4) (86,149) (234,170) ∧
      LeastPositivePeriod (phaseWord 234) 8 ∧
      LeastPositivePeriod (phaseWord 170) 2 ∧
      phaseWord 86 0 ≠ phaseWord 86 1 :=
  ⟨arbitrary_older_context n, exit_periods.1, exit_periods.2, carrier_boundary_nonconstant⟩


/-! ### Genuine finite initial codes can imitate the drop for arbitrarily long

These are finite observation statements, NOT all-time period drops.
-/

def carrierWord (j : Nat) : Nat :=
  match j % 4 with
  | 0 => 86
  | 1 => 149
  | 2 => 101
  | _ => 89

def contextWord (n j : Nat) : Nat :=
  if j < 4*n+2 then carrierWord j else
  if j = 4*n+2 then 154 else
  if j = 4*n+3 then 21 else
  if j = 4*n+4 then 234 else 170

theorem context_prefix (n j : Nat) (hj : j < 4*n+2) :
    contextWord n j = carrierWord j := by simp [contextWord, hj]

theorem context_boundary_values (n : Nat) :
    contextWord n (4*n) = 86 ∧ contextWord n (4*n+1) = 149 ∧
    contextWord n (4*n+2) = 154 ∧ contextWord n (4*n+3) = 21 ∧
    contextWord n (4*n+4) = 234 ∧ contextWord n (4*n+5) = 170 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [context_prefix n _ (by omega)]
    simp [carrierWord]
  · rw [context_prefix n _ (by omega)]
    simp [carrierWord, Nat.add_mod]
  · rw [contextWord, ite_eq_right (by omega), ite_eq_left rfl]
  · rw [contextWord, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  · rw [contextWord, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  · rw [contextWord, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem carrier_word_step (j : Nat) :
    CyclicStep (carrierWord j, carrierWord (j+1))
      (carrierWord (j+1), carrierWord (j+2)) := by
  have cert : ∀ r : Fin 4, CyclicStep (carrierWord r.val, carrierWord (r.val+1))
      (carrierWord (r.val+1), carrierWord (r.val+2)) := by decide
  simpa [carrierWord, Nat.add_mod] using cert ⟨j % 4, by omega⟩

theorem context_word_step (n j : Nat) (hj : j+2 ≤ 4*n+5) :
    CyclicStep (contextWord n j, contextWord n (j+1))
      (contextWord n (j+1), contextWord n (j+2)) := by
  by_cases hp : j+2 < 4*n+2
  · rw [context_prefix n j (by omega), context_prefix n (j+1) (by omega),
      context_prefix n (j+2) hp]
    exact carrier_word_step j
  · obtain ⟨c0,c1,c2,c3,c4,c5⟩ := context_boundary_values n
    have casesJ : j = 4*n ∨ j = 4*n+1 ∨ j = 4*n+2 ∨ j = 4*n+3 := by omega
    rcases casesJ with rfl | rfl | rfl | rfl
    · simpa only [c0,c1,c2] using (show CyclicStep (86,149) (149,154) from by decide)
    · simpa only [c1,c2,c3] using (show CyclicStep (149,154) (154,21) from by decide)
    · simpa only [c2,c3,c4] using (show CyclicStep (154,21) (21,234) from by decide)
    · simpa only [c3,c4,c5] using (show CyclicStep (21,234) (234,170) from by decide)

/-- Two cells per tick bound the influence of the older boundary. -/
theorem iter_agrees_inside (c : Nat → Bool) (x : Nat → Nat → Bool) (B : Nat)
    (hi : ∀ j, j ≤ B → x j 0 = c j)
    (hs : ∀ j, j+2 ≤ B → ∀ t,
      x (j+2) (t+1) = xor (x (j+2) t) (x (j+1) t || x j t)) :
    ∀ t j, 2*t ≤ j → j ≤ B → Rule30FrozenRuler.iter t c j = x j t := by
  intro t
  induction t with
  | zero => intro j hj hb; exact (hi j hb).symm
  | succ t ih =>
      intro j hj hb
      obtain ⟨k,rfl⟩ : ∃ k, j = k+2 := ⟨j-2, by omega⟩
      change xor (Rule30FrozenRuler.iter t c (k+2))
        (Rule30FrozenRuler.iter t c (k+1) || Rule30FrozenRuler.iter t c k) = x (k+2) (t+1)
      rw [hs k hb t, ih (k+2) (by omega) hb,
        ih (k+1) (by omega) (by omega), ih k (by omega) (by omega)]

def finiteContextSeed (n j : Nat) : Bool :=
  if j ≤ 4*n+4 then phaseWord (contextWord n (j+1)) 0 else false

/-- Finite odd edge codes imitate the period-eight/period-two pair through
time 2n+1. There is deliberately NO all-time periodicity conclusion. -/
theorem finite_seed_apparent_drop (n : Nat) :
    finiteContextSeed n 0 = true ∧
      (∀ j, 4*n+4 < j → finiteContextSeed n j = false) ∧
      ∀ t, t ≤ 2*n+1 →
        Rule30FrozenRuler.iter t (finiteContextSeed n) (4*n+3) = phaseWord 234 t ∧
        Rule30FrozenRuler.iter t (finiteContextSeed n) (4*n+4) = phaseWord 170 t := by
  refine ⟨?_, ?_, ?_⟩
  · rw [finiteContextSeed, ite_eq_left (by omega), context_prefix n 1 (by omega)]
    decide
  · intro j hj
    simp [finiteContextSeed, show ¬ j ≤ 4*n+4 by omega]
  · let x := fun j t => phaseWord (contextWord n (j+1)) t
    have hi : ∀ j, j ≤ 4*n+4 → x j 0 = finiteContextSeed n j := by
      intro j hj
      simp [x, finiteContextSeed, hj]
    have hs : ∀ j, j+2 ≤ 4*n+4 → ∀ t,
        x (j+2) (t+1) = xor (x (j+2) t) (x (j+1) t || x j t) := by
      intro j hj t
      exact (cyclic_step_all_time _ _ (context_word_step n (j+1) (by omega)) t).2
    have inside := iter_agrees_inside (finiteContextSeed n) x (4*n+4) hi hs
    obtain ⟨_,_,_,_,c4,c5⟩ := context_boundary_values n
    intro t ht
    constructor
    · have eq := inside t (4*n+3) (by omega) (by omega)
      change Rule30FrozenRuler.iter t (finiteContextSeed n) (4*n+3) =
        phaseWord (contextWord n (4*n+4)) t at eq
      simpa only [c4] using eq
    · have eq := inside t (4*n+4) (by omega) (by omega)
      change Rule30FrozenRuler.iter t (finiteContextSeed n) (4*n+4) =
        phaseWord (contextWord n (4*n+5)) t at eq
      simpa only [c5] using eq


end Ruliology.CellularAutomata.Rule30EdgeClockDrop
