module

public import Ruliology.CellularAutomata.Rule30EveryKStatement

/-!
# Scheduled inverse layers at a finite Rule 30 edge

Troy Lowry's Rule30PrizeKit PR #60 gives the reset-word and scheduled-cascade
argument. Here the driver is the preceding phase of an odd edge cycle and the
cut is the one computed by Rule30EveryKStatement.firstReset.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EveryKCascade

open Rule30EveryKStatement Rule30ZeroBoundary Rule30UniversalLeftSide

abbrev Row := Nat → Bool
abbrev Pair := Bool × Bool

/-- Advance the inverse register one physical cell towards the exterior. -/
def advance (b : Bool) (s : Pair) : Pair := (s.2, xor b (s.2 || s.1))

def pair (P : Row) (x : Nat) : Pair := (P x, P (x+1))

private theorem black_cycle (s : Pair) :
    advance true (advance true (advance true (advance true s))) = advance true s := by
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;> rfl

private theorem black_run (r : Nat → Pair) (start m : Nat)
    (h : ∀ i, i < 3*m+1 → r (start+i+1) = advance true (r (start+i))) :
    r (start+(3*m+1)) = advance true (r start) := by
  induction m with
  | zero => simpa using h 0 (by decide)
  | succ m ih =>
    let n := 3*m+1
    have h1 := h n (by dsimp [n]; omega)
    have h2 := h (n+1) (by dsimp [n]; omega)
    have h3 := h (n+2) (by dsimp [n]; omega)
    have prev := ih (fun i hi => h i (by omega))
    rw [show start+(3*(m+1)+1) = start+(n+2)+1 by dsimp [n]; omega,
      h3, show start+(n+2) = start+(n+1)+1 by omega, h2,
      show start+(n+1) = start+n+1 by omega, h1, prev, black_cycle]

private theorem finish_reset (b : Bool) (s : Pair) :
    advance b (advance false (advance true (advance false s))) = (true, !b) := by
  obtain ⟨a,c⟩ := s
  cases a <;> cases c <;> cases b <;> rfl

/-- After reading 0, 3m+1 black cells, 0 and a free symbol, the pair is
independent of its entrance state. The free symbol is read at depth base+3m+4. -/
theorem reset_closes (P O : Row) (base m : Nat)
    (h : ∀ n, base ≤ n → pair P (n+1) = advance (O (n+1)) (pair P n))
    (a : O (base+1) = false)
    (bs : ∀ i, i < 3*m+1 → O (base+2+i) = true)
    (c : O (base+3*m+3) = false) :
    pair P (base+3*m+4) = (true, !(O (base+3*m+4))) := by
  have run := black_run (pair P) (base+1) m (by
    intro i hi
    rw [h _ (by omega), show base+1+i+1 = base+2+i by omega, bs i hi])
  have last := h (base+3*m+3) (by omega)
  rw [last, h (base+3*m+2) (by omega), c,
    show base+3*m+2 = base+1+(3*m+1) by omega, run, h base (by omega), a, finish_reset]

/-- A word placed with its low bit at physical depth e, white outside. -/
def reference (e v x : Nat) : Bool := if x ≤ e then v.testBit (e-x) else false

/-- The cell rule inverted at physical depth n+1. -/
def Drives (O P : Row) (base : Nat) : Prop :=
  ∀ n, base ≤ n → pair P (n+1) = advance (O (n+1)) (pair P n)

theorem physical_drives (P : Row) (t : Nat) :
    Drives (zrow P (t+1)) (zrow P t) 0 := by
  intro n _
  exact Prod.ext rfl (zrow_inv P t n)

/-- The previous phase is a valid reference parent on the available band and
the white exterior. This does not require that the actual seed's earlier band
was already recurrent. -/
theorem reference_drives (w u e base : Nat) (he : 0 < e) (hw : e ≤ base+w) :
    Drives (reference e (bandStep w u)) (reference (e-1) u) base := by
  intro n hn
  refine Prod.ext rfl ?_
  change reference (e-1) u (n+2) = xor (reference e (bandStep w u) (n+1))
    (reference (e-1) u (n+1) || reference (e-1) u n)
  by_cases h0 : e ≤ n
  · simp [reference, show ¬ n+1 ≤ e by omega, show ¬ n+2 ≤ e-1 by omega,
      show ¬ n+1 ≤ e-1 by omega, show ¬ n ≤ e-1 by omega]
  by_cases h1 : e = n+1
  · subst e
    simp [reference, show ¬ n+2 ≤ n by omega, show ¬ n+1 ≤ n by omega, stepK_bit_zero (by omega : 0 < w)]
  by_cases h2 : e = n+2
  · subst e
    simp [reference, stepK_bit_one (by omega : 1 < w)]
  let j := e-(n+3)
  have hj : j+2 < w := by dsimp [j]; omega
  simp only [reference, ite_eq_left (show n+2 ≤ e-1 by omega), ite_eq_left (show n+1 ≤ e by omega),
    ite_eq_left (show n+1 ≤ e-1 by omega), ite_eq_left (show n ≤ e-1 by omega)]
  rw [show e-1-(n+2) = j by dsimp [j]; omega, show e-(n+1) = j+2 by dsimp [j]; omega,
    show e-1-(n+1) = j+1 by dsimp [j]; omega, show e-1-n = j+2 by dsimp [j]; omega,
    stepK_bit_step hj]
  cases u.testBit j <;> cases (u.testBit (j+1) || u.testBit (j+2)) <;> rfl


/-- The actual edge is black even if no bits remain available to the next
scan. Agreement covers every exterior cell, including an infinite tail. -/
def Matches (P : Row) (e v available : Nat) : Prop :=
  P e = true ∧ ∀ x, e < x+available → P x = reference e v x

theorem firstReset_spec {v available j : Nat} (h : firstReset v available = some j) :
    ∃ m, j+3*m+4 ≤ available ∧ resetAt v j m = true := by
  unfold firstReset at h
  have hh := List.find?_some h
  obtain ⟨m, _, hm⟩ := List.any_eq_true.mp hh
  exact ⟨m, of_decide_eq_true (Bool.and_eq_true_iff.mp hm).1, (Bool.and_eq_true_iff.mp hm).2⟩

/-- Common output from base+1 onwards propagates agreement of an inverse
pair at cut to the whole exterior. -/
private theorem agree_after {O P Q : Row} {base cut : Nat}
    (hp : Drives O P base) (hq : Drives O Q base) (hc : base ≤ cut)
    (eq : pair P cut = pair Q cut) : ∀ x, cut ≤ x → P x = Q x := by
  intro x hx
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hx
  suffices z : pair P (cut+i) = pair Q (cut+i) by exact congrArg Prod.fst z
  clear hx
  induction i with
  | zero => exact eq
  | succ i ih => rw [← Nat.add_assoc, hp _ (by omega), hq _ (by omega), ih]

/-- One successful cut of `firstReset`'s actual search fixes the next band and the
previous physical edge, including the cut j=0. -/
theorem scheduled_layer {P O : Row} {w u e available j : Nat}
    (full : available ≤ e) (width : available ≤ w)
    (drive : Drives O P 0)
    (matchOut : Matches O e (bandStep w u) available)
    (cut : firstReset (bandStep w u) available = some j) :
    Matches P (e-1) u j := by
  obtain ⟨m, bound, reset⟩ := firstReset_spec cut
  let v := bandStep w u
  let b := e-(j+3*m+4)
  have eb : e = b+j+3*m+4 := by dsimp [b]; omega
  let D := reference e v
  let Q := reference (e-1) u
  have dp : Drives D P b := by
    intro n hn
    dsimp [D, v]
    rw [← matchOut.2 (n+1) (by omega)]
    exact drive n (Nat.zero_le _)
  have dq : Drives D Q b := reference_drives w u e b (by omega) (by omega)
  obtain ⟨zeros, ones⟩ := Bool.and_eq_true_iff.mp reset
  obtain ⟨z1,z2⟩ := Bool.and_eq_true_iff.mp zeros
  have low : v.testBit (j+1) = false := by simpa using z1
  have high : v.testBit (j+3*m+3) = false := by simpa using z2
  have deep : D (b+1) = false := by
    simpa [D, reference, show b+1 ≤ e by omega, show e-(b+1) = j+3*m+3 by omega] using high
  have shallow : D (b+3*m+3) = false := by
    simpa [D, reference, show b+3*m+3 ≤ e by omega, show e-(b+3*m+3) = j+1 by omega] using low
  have run (i) (hi : i < 3*m+1) : D (b+2+i) = true := by
    have h := List.all_eq_true.mp ones (3*m-i) (List.mem_range.mpr (by omega))
    simpa [D, reference, show b+2+i ≤ e by omega,
      show e-(b+2+i) = j+2+(3*m-i) by omega] using h
  have same := (reset_closes P D b m dp deep run shallow).trans
    (reset_closes Q D b m dq deep run shallow).symm
  have tail := agree_after dp dq (by omega) same
  have exterior (x) (hx : e ≤ x) : P x = false := by
    rw [tail x (by omega)]
    simp [Q, reference, show ¬ x ≤ e-1 by omega]
  constructor
  · have h := congrArg Prod.snd (drive (e-1) (Nat.zero_le _))
    have he : e-1+1 = e := by omega
    change P (e-1+1+1) = xor (O (e-1+1)) (P (e-1+1) || P (e-1)) at h
    rw [he, matchOut.1, exterior e (by omega), exterior (e+1) (by omega)] at h
    cases hbit : P (e-1) <;> simp [hbit] at h ⊢
  · intro x hx
    exact tail x (by omega)


/-- Phase of the reference strip d inverse ticks from v. -/
def earlier (w v q d : Nat) := bandAt w v ((q - d%q)%q)

theorem earlier_step {w v q : Nat} (hq : 0 < q) (cycle : bandAt w v q = v) (d : Nat) :
    bandStep w (earlier w v q (d+1)) = earlier w v q d := by
  let r := d%q
  have hr : r < q := Nat.mod_lt _ hq
  have succmod : (d+1)%q = (r+1)%q := Nat.mod_add_mod .. |>.symm
  unfold earlier
  rw [succmod]
  change bandStep w (bandAt w v ((q-(r+1)%q)%q)) = bandAt w v ((q-r)%q)
  by_cases last : r+1 = q
  · rw [last]
    simp only [Nat.mod_self, Nat.sub_zero, rowAt]
    rw [show q-r = 1 by omega]
    by_cases one : q = 1
    · rw [one] at cycle ⊢
      simpa [rowAt] using cycle
    · rw [Nat.mod_eq_of_lt (by omega : 1 < q)]
      rfl
  · rw [Nat.mod_eq_of_lt (by omega : r+1 < q), Nat.mod_eq_of_lt (by omega : q-(r+1) < q)]
    change bandAt w v (q-(r+1)+1) = _
    rw [show q-(r+1)+1 = q-r by omega]
    by_cases zero : r = 0
    · simpa [zero, rowAt] using cycle
    · rw [Nat.mod_eq_of_lt (by omega : q-r < q)]

/-- From every physical k-tick preimage the computed schedule fixes the
edge at depth e-k and all cells beyond it. No support or trace condition is
imposed on the entrance row. -/
theorem scheduled_edge {w v q : Nat} (hq : 0 < q) (cycle : bandAt w v q = v)
    (fuel d a k e : Nat) (P : Row) (width : a ≤ w) (full : a ≤ e)
    (matched : Matches (zrow P k) e (earlier w v q d) a)
    (closed : k ≤ schedule w v q fuel d a) :
    zrow P 0 (e-k) = true ∧ ∀ x, e-k < x → zrow P 0 x = false := by
  induction fuel generalizing d a k e with
  | zero =>
    have hk : k = 0 := by simpa [schedule] using closed
    subst k
    exact ⟨matched.1, fun x hx => (matched.2 x (by omega)).trans
      (by simp [reference, show ¬ x ≤ e by omega])⟩
  | succ fuel ih =>
    cases k with
    | zero => exact ⟨matched.1, fun x hx => (matched.2 x (by omega)).trans
        (by simp [reference, show ¬ x ≤ e by omega])⟩
    | succ k =>
      simp only [schedule] at closed
      cases h : firstReset (earlier w v q d) a with
      | none =>
        unfold earlier at h
        simp only [h] at closed
        omega
      | some j =>
        have fj := h
        unfold earlier at h
        simp only [h] at closed
        obtain ⟨m, bound, _⟩ := firstReset_spec fj
        rw [← earlier_step hq cycle d] at fj matched
        have next := scheduled_layer full width (physical_drives P k) matched fj
        have result := ih (d+1) j k (e-1) (by omega) (by omega) next (by omega)
        simpa [show e-(k+1) = e-1-k by omega] using result

/-! ## Period-multiple invariance of `earlier`, `schedule`, and `phaseCapacity` -/

private theorem bandAt_eq_mod {w v q : Nat} (cycle : bandAt w v q = v) (x : Nat) :
    bandAt w v x = bandAt w v (x % q) := by
  have hdiv : x = x % q + (x / q) * q := by
    rw [Nat.mul_comm]; exact (Nat.mod_add_div x q).symm
  conv => lhs; rw [hdiv]
  exact rowAt_add_mul cycle (x % q) (x / q)

private theorem sub_mul_mod_eq (m q c r : Nat) (hq : 0 < q) (hc : c < m) (hr : r < q) :
    ((m * q - (r + q * c)) % (m * q)) % q = ((q - r) % q) % q := by
  have hqc : q * c = c * q := Nat.mul_comm q c
  by_cases hr0 : r = 0
  · subst hr0
    by_cases hc0 : c = 0
    · subst hc0
      simp
    · have hm_split : m * q = (m - c) * q + c * q := by
        rw [← Nat.add_mul, show m - c + c = m by omega]
      have hsub : m * q - (0 + q * c) = (m - c) * q := by omega
      have hlt_mq : (m - c) * q < m * q := (Nat.mul_lt_mul_right hq).mpr (by omega)
      rw [hsub, Nat.mod_eq_of_lt hlt_mq, Nat.mul_mod_left, Nat.sub_zero, Nat.mod_self, Nat.zero_mod]
  · have hm_split : m * q = (m - 1 - c) * q + q + c * q := by
      conv => lhs; rw [show m = (m - 1 - c) + 1 + c by omega, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    have hsub : m * q - (r + q * c) = (q - r) + (m - 1 - c) * q := by omega
    have hlt_mq : (q - r) + (m - 1 - c) * q < m * q := by
      have hle : (m - 1 - c) * q ≤ (m - 1 - c) * q + c * q := Nat.le_add_right _ _
      omega
    have hqr_lt : q - r < q := by omega
    rw [hsub, Nat.mod_eq_of_lt hlt_mq, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hqr_lt, Nat.mod_eq_of_lt hqr_lt]

private theorem phase_mod_mul_eq {m q : Nat} (hm : 0 < m) (hq : 0 < q) (d : Nat) :
    ((m * q - d % (m * q)) % (m * q)) % q = ((q - d % q) % q) % q := by
  have hmq : 0 < m * q := Nat.mul_pos hm hq
  have hrem_lt : d % (m * q) < m * q := Nat.mod_lt d hmq
  have hd_mod : d % q = (d % (m * q)) % q :=
    (Nat.mod_mod_of_dvd d ⟨m, Nat.mul_comm m q⟩).symm
  have hc_lt : (d % (m * q)) / q < m := by
    apply Classical.byContradiction
    intro hge
    have hbig : m * q ≤ q * ((d % (m * q)) / q) := by
      rw [Nat.mul_comm q _]
      exact Nat.mul_le_mul_right q (Nat.not_lt.mp hge)
    have hdiv := Nat.mod_add_div (d % (m * q)) q
    omega
  have hr_lt : (d % (m * q)) % q < q := Nat.mod_lt (d % (m * q)) hq
  have hdecomp : d % (m * q) = (d % (m * q)) % q + q * ((d % (m * q)) / q) :=
    (Nat.mod_add_div (d % (m * q)) q).symm
  rw [hd_mod]
  conv => lhs; rw [hdecomp]
  exact sub_mul_mod_eq m q ((d % (m * q)) / q) ((d % (m * q)) % q) hq hc_lt hr_lt

/-- **Period-Multiple Invariance of `earlier`, `schedule`, and `phaseCapacity` (`earlier_and_phaseCapacity_mul_period`):**
for any cycle period `q > 0` (`bandAt w v q = v`) and positive multiplier `m > 0`, evaluating `earlier`,
`schedule`, or `phaseCapacity` at period `m * q` is identically equal to evaluating at `q`. -/
theorem earlier_and_phaseCapacity_mul_period {w v q m : Nat}
    (hq : 0 < q) (hm : 0 < m) (cycle : bandAt w v q = v) :
    (∀ d : Nat, earlier w v (m * q) d = earlier w v q d) ∧
    (∀ fuel d avail : Nat, schedule w v (m * q) fuel d avail = schedule w v q fuel d avail) ∧
    phaseCapacity w v (m * q) = phaseCapacity w v q := by
  have hearlier : ∀ d : Nat, earlier w v (m * q) d = earlier w v q d := by
    intro d
    unfold earlier
    rw [bandAt_eq_mod cycle ((m * q - d % (m * q)) % (m * q)),
      bandAt_eq_mod cycle ((q - d % q) % q), phase_mod_mul_eq hm hq d]
  have hsched : ∀ fuel d avail : Nat,
      schedule w v (m * q) fuel d avail = schedule w v q fuel d avail := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro d avail
      simp only [schedule]
      change (match firstReset (earlier w v (m * q) d) avail with
        | none => 0 | some j => 1 + schedule w v (m * q) fuel (d + 1) j) =
        (match firstReset (earlier w v q d) avail with
        | none => 0 | some j => 1 + schedule w v q fuel (d + 1) j)
      rw [hearlier d]
      cases firstReset (earlier w v q d) avail with
      | none => rfl
      | some j => dsimp only; rw [ih (d + 1) j]
  exact ⟨hearlier, hsched, hsched w 0 w⟩

end Ruliology.CellularAutomata.Rule30EveryKCascade
