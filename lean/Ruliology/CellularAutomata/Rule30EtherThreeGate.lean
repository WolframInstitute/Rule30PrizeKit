module

public import Ruliology.CellularAutomata.Rule30EtherThreeNotAbsorption
public import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton

/-!
# The gate of `001`

`Rule30EtherThreeTrap` reduces the word `001` to `AbsorptionT t001`, that every finite right half enters one trap, and
`Rule30EtherThreeNotAbsorption` proves that false. The masked form of Jen's theorem asks only about the white ticks of the
center. On the first white tick of each `001` column `1` is eventually white if the center ends in `001`
(`skeleton_001`). The second is the one white phase left: call column `1` there the *gate*.

* `gate_of_t001`, `gate_of_fifteen`: a right half that enters `t001` at a label of the drive's phase has a gate that repeats
  `1100000` from some tick on; one that so enters `trap001fifteen` has `11000`.
* `GatePeriodic` (open): the gate of every finitely supported right half, from every phase, is eventually periodic. It
  excludes `001` as an eventual tail of the center column (`not_eventually_001_of_gatePeriodic`). It is the form for `001`
  of `Rule30Ether.Lock`, which is for period four. It follows if, from every drive phase, each finitely supported right half
  enters some checked trap of positive width for `001` (`gatePeriodic_of_some_trap`).
* `GateEntry` (open): those gates eventually repeat `1100000` or `11000`. It implies `GatePeriodic` and names no trap.

`Rule30PeriodThreeLanguage.col1_001` restricts the gate of the center's own orbit. L. Hallee (`lhallee/rule30-open`) proves
that the gate of every right half avoids `010`, `101` and `1001` from its reading `14` on (`Columns.ThreeRuns`), that entry
into some trap suffices and entry into `t001` or `trap001fifteen` fails (`Columns.Traps001`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherThreeGate

open Rule30Jen Rule30StripCertificates Rule30Ether Rule30EtherThree Rule30EtherThreeNotAbsorption

/-! ### The gate -/

/-- The gate word of the kit's `t001`: two black readings, then five white, repeated. -/
def gate7 (k : Nat) : Bool := decide (k % 7 < 2)
/-- The gate word of `trap001fifteen`: two black readings, then three white, repeated. -/
def gate5 (k : Nat) : Bool := decide (k % 5 < 2)

/-- The right half `x` driven by `001` from phase `φ`. -/
def half (x : Nat → Bool) (φ : Nat) : Nat → Nat → Bool := drv (fun t => wordAt3 w001 (t + φ)) x

/-- **The gate statement** (open; a `Prop`). Beside `001`, for every finitely supported right half and every phase, column
`1`, read on the second white tick of each `001`, eventually repeats `1100000` or `11000`. -/
def GateEntry : Prop :=
  ∀ (x : Nat → Bool) (n : Nat), (∀ p, n < p → x p = false) → ∀ φ, ∃ t1, (t1 + φ) % 3 = 1 ∧
    ((∀ k, half x φ (t1 + 3 * k) 1 = gate7 k) ∨ (∀ k, half x φ (t1 + 3 * k) 1 = gate5 k))

/-- The weaker form (open; a `Prop`): the gate of every finitely supported right half is eventually periodic. It is the form
for `001`, read on one white phase, of the first alternative of `Rule30Ether.Lock`, which is for period four. -/
def GatePeriodic : Prop :=
  ∀ (x : Nat → Bool) (n : Nat), (∀ p, n < p → x p = false) → ∀ φ, ∃ t1 m, 0 < m ∧ (t1 + φ) % 3 = 1 ∧
    ∀ k, half x φ (t1 + 3 * (k + m)) 1 = half x φ (t1 + 3 * k) 1

theorem gatePeriodic_of_gateEntry (h : GateEntry) : GatePeriodic := by
  intro x n hx φ
  obtain ⟨t1, hph, hg | hg⟩ := h x n hx φ
  · exact ⟨t1, 7, by decide, hph, fun k => by rw [hg, hg]; unfold gate7; rw [Nat.add_mod_right]⟩
  · exact ⟨t1, 5, by decide, hph, fun k => by rw [hg, hg]; unfold gate5; rw [Nat.add_mod_right]⟩

/-- **A periodic gate excludes `001`** as an eventual tail of the centre column: on the first white tick of each `001` column
`1` is eventually white (`skeleton_001`), so with a periodic gate the masked form of Jen's theorem applies. -/
theorem not_eventually_001_of_gatePeriodic (h : GatePeriodic) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T) := by
  rintro ⟨T, hT⟩
  have hc : (fun t => cell (T + t) 0) = (fun t => wordAt3 w001 (t + 0)) := by
    funext t; rw [hT (T + t) (by omega)]; congr 1; omega
  have hfin : ∀ p, T < p → (fun p : Nat => cell T (p : Int)) p = false :=
    fun p hp => Rule30Diagonals.cell_eq_false_of_gt T p (by omega)
  obtain ⟨t1, m, hm, hph, hg⟩ := h (fun p => cell T (p : Int)) T hfin 0
  have hcell : ∀ t, half (fun p => cell T (p : Int)) 0 t 1 = cell (T + t) 1 := by
    intro t
    unfold half
    rw [← hc]
    exact (cell_eq_drv T t 1).symm
  rw [Nat.add_zero] at hph
  obtain ⟨T', hT', hsk⟩ := skeleton_001 T hT
  refine Rule30MaskedJen.masked_jen_center (T := T) (P := 3 * m) (by omega) ?_ (max T' (T + t1)) ?_
  · intro t ht
    rw [hT (t + 3 * m) (by omega), hT t ht]
    unfold wordAt3
    rw [show t + 3 * m - T = (t - T) + 3 * m by omega, Nat.add_mul_mod_self_left]
  · intro t ht hw
    have ht1 : T' ≤ t := by omega
    have ht2 : T + t1 ≤ t := by omega
    rcases (by omega : (t - T) % 3 = 0 ∨ (t - T) % 3 = 1 ∨ (t - T) % 3 = 2) with h0 | h1 | h2
    · rw [hsk t ht1 h0, hsk (t + 3 * m) (by omega) (by omega)]
    · obtain ⟨k, hk⟩ : ∃ k, t = T + (t1 + 3 * k) := ⟨(t - T - t1) / 3, by omega⟩
      rw [show t + 3 * m = T + (t1 + 3 * (k + m)) by omega, hk, ← hcell, ← hcell, hg k]
    · rw [hT t (by omega)] at hw
      unfold wordAt3 at hw
      rw [h2] at hw
      exact absurd hw (by decide)

/-- **The gate statement excludes `001`** as an eventual tail of the centre column. -/
theorem not_eventually_001_of_gateEntry (h : GateEntry) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T) :=
  not_eventually_001_of_gatePeriodic (gatePeriodic_of_gateEntry h)

/-! ### The gate of a half that enters a trap -/

/-- The half `x`, driven by `001` from phase `φ`, is at some tick in a state of `C` whose label reads the drive's phase. -/
def Enters (C : PTrap) (x : Nat → Bool) (φ : Nat) : Prop :=
  ∃ t1 i, i < C.n ∧ (t1 + φ) % 3 = C.lab i % 3 ∧ EncF (half x φ) C.b t1 0 (C.st i)

/-- A half in a checked trap for `001` stays in it, the label counting the ticks, from any phase. -/
theorem stays_in {C : PTrap} (hC : C.check = true) (hw : C.w = w001) {x : Nat → Bool} {φ t1 i : Nat} (hi : i < C.n)
    (hph : (t1 + φ) % 3 = C.lab i % 3) (hr : EncF (half x φ) C.b t1 0 (C.st i)) :
    ∀ n, ∃ j, j < C.n ∧ EncF (half x φ) C.b (t1 + n) 0 (C.st j) ∧ C.lab j = (C.lab i + n) % C.m := by
  have hli : C.lab i < C.m := (PTrap.step C hC hi false).2.2.2.1
  intro n
  induction n with
  | zero => exact ⟨i, hi, hr, by rw [Nat.add_zero, Nat.mod_eq_of_lt hli]⟩
  | succ n ih =>
    obtain ⟨j, hj, hr', hl'⟩ := ih
    have hphase : (t1 + n + φ) % 3 = C.lab j % 3 := by
      rw [hl', show t1 + n + φ = (t1 + φ) + n by omega]
      exact PTrap.phase_lab C hC _ _ hph n
    have hc0 : half x φ (t1 + n) 0 = wordAt3 C.w (C.lab j % 3) := by
      unfold half; rw [drv_col0, hw]; unfold wordAt3; rw [Nat.mod_mod, hphase]
    obtain ⟨hnj, hst, hlab, -, -⟩ := PTrap.step C hC hj (half x φ (t1 + n) (0 + 1 + C.b))
    refine ⟨C.nxt j (half x φ (t1 + n) (0 + 1 + C.b)), hnj, ?_, ?_⟩
    · rw [hst, ← hc0, show t1 + (n + 1) = t1 + n + 1 by omega]
      exact encF_step (drv_isR30 _ _) hr'
    · rw [hlab, hl', Nat.mod_add_mod]; rfl

/-- In a checked trap of positive width for `001` the gate, from a tick whose label is `l0`, reads the trap's function at
`l0`, `l0 + 3`, …. -/
theorem gate_of_trap {C : PTrap} (hC : C.check = true) (hw : C.w = w001) (hb : 0 < C.b) {x : Nat → Bool} {φ : Nat}
    (h : Enters C x φ) {l0 : Nat} (hl3 : l0 % 3 = 1) :
    ∃ t1, (t1 + φ) % 3 = 1 ∧ ∀ k, half x φ (t1 + 3 * k) 1 = C.u.testBit ((l0 + 3 * k) % C.m) := by
  obtain ⟨t0, i, hi, hph, hr⟩ := h
  obtain ⟨hm, hm3, -⟩ := PTrap.facts C hC
  have hli : C.lab i < C.m := (PTrap.step C hC hi false).2.2.2.1
  have inv := stays_in hC hw hi hph hr
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hm3
  obtain ⟨n0, hn0⟩ : ∃ n0, C.lab i + n0 = l0 + C.m := ⟨l0 + C.m - C.lab i, by omega⟩
  refine ⟨t0 + n0, by omega, fun k => ?_⟩
  obtain ⟨j, hj, hr', hl'⟩ := inv (n0 + 3 * k)
  have hlab : C.lab j = (l0 + 3 * k) % C.m := by
    rw [hl', show C.lab i + (n0 + 3 * k) = (l0 + 3 * k) + C.m by omega, Nat.add_mod_right]
  obtain ⟨-, -, -, -, hu⟩ := PTrap.step C hC hj false
  have hwhite : wordAt3 C.w (C.lab j % 3) = false := by
    have : C.lab j % 3 = 1 := by
      rw [hlab, hq, Nat.mod_mul_right_mod]; omega
    rw [hw, this]; rfl
  rw [← hlab, ← hu hwhite, encF_head hr' hb]
  rw [show t0 + n0 + 3 * k = t0 + (n0 + 3 * k) by omega]

theorem t001_gate : ∀ k, k < 7 → t001.u.testBit ((19 + 3 * k) % 21) = gate7 k := by decide +kernel
theorem fifteen_gate : ∀ k, k < 5 → trap001fifteen.u.testBit ((4 + 3 * k) % 15) = gate5 k := by decide +kernel

/-- **The gate of a half that enters `t001`**: from some second white tick on it repeats `1100000`. -/
theorem gate_of_t001 {x : Nat → Bool} {φ : Nat} (h : Enters t001 x φ) :
    ∃ t1, (t1 + φ) % 3 = 1 ∧ ∀ k, half x φ (t1 + 3 * k) 1 = gate7 k := by
  obtain ⟨t1, hph, hk⟩ := gate_of_trap t001_check rfl (by decide) h (l0 := 19) (by decide)
  refine ⟨t1, hph, fun k => ?_⟩
  rw [hk k, show t001.m = 21 from rfl, show (19 + 3 * k) % 21 = (19 + 3 * (k % 7)) % 21 by omega,
    t001_gate (k % 7) (Nat.mod_lt _ (by decide))]
  unfold gate7; rw [Nat.mod_mod]

/-- **The gate of a half that enters `trap001fifteen`**: from some second white tick on it repeats `11000`. -/
theorem gate_of_fifteen {x : Nat → Bool} {φ : Nat} (h : Enters trap001fifteen x φ) :
    ∃ t1, (t1 + φ) % 3 = 1 ∧ ∀ k, half x φ (t1 + 3 * k) 1 = gate5 k := by
  obtain ⟨t1, hph, hk⟩ := gate_of_trap trap001fifteen_check rfl (by decide) h (l0 := 4) (by decide)
  refine ⟨t1, hph, fun k => ?_⟩
  rw [hk k, show trap001fifteen.m = 15 from rfl, show (4 + 3 * k) % 15 = (4 + 3 * (k % 5)) % 15 by omega,
    fifteen_gate (k % 5) (Nat.mod_lt _ (by decide))]
  unfold gate5; rw [Nat.mod_mod]

/-- **Entry into some trap gives the weaker statement.** If, from every drive phase, each finitely supported right half enters
some checked trap of positive width for `001`, which may depend on the half and the phase, then `GatePeriodic` holds. A
trap of width zero passes `PTrap.check` and is entered by every half, so the width is needed. -/
theorem gatePeriodic_of_some_trap
    (h : ∀ (x : Nat → Bool) (n : Nat), (∀ p, n < p → x p = false) → ∀ φ,
      ∃ C : PTrap, C.check = true ∧ C.w = w001 ∧ 0 < C.b ∧ Enters C x φ) : GatePeriodic := by
  intro x n hx φ
  obtain ⟨C, hC, hw, hb, he⟩ := h x n hx φ
  obtain ⟨t1, hph, hk⟩ := gate_of_trap hC hw hb he (l0 := 1) rfl
  refine ⟨t1, C.m, (PTrap.facts C hC).1, hph, fun k => ?_⟩
  rw [hk, hk, show 1 + 3 * (k + C.m) = 1 + 3 * k + C.m * 3 by omega, Nat.add_mul_mod_self_left]

end Rule30EtherThreeGate
end Ruliology.CellularAutomata
