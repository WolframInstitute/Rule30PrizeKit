module

public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThreeEntry
public import Ruliology.CellularAutomata.Rule30EtherThreeDeparture
public import Ruliology.CellularAutomata.Rule30PeriodThreeLanguage

/-!
# At period three every finite right half enters the least gate trap

Drive a right half of rule 30 by the column that repeats `001`, or `011`, from any phase (`half`). Its *gate* is column `1`
once a period: at the white tick before the black one of `001`, at the white tick of `011`. A window is the first fourteen
cells at a gate tick, as a number. A set of windows is *closed* when one period keeps it, whatever lies beyond (`Closed`).

* **The traps.** `trap001` (1,195 windows) and `trap011` (691) are closed (`closed_001`, `closed_011`), and they are the least
  nonempty closed sets: every closed set that holds any window at all holds them (`least_001`, `least_011`).
* **Entry.** A half that is white beyond cell `D` is in the trap at every gate tick from `3 D + 170` beside `001` and
  `3 D + 820` beside `011` (`finite_enters_001`, `finite_enters_011`). No bound of slope below `5/2` holds (`slope_001`,
  `slope_011`).
* **Any support.** Every right half enters, or has a constant gate from tick 26 beside `001`, a white one from tick 155 beside
  `011` (`enters_or_constant_001`, `enters_or_constant_011`).
* **The gate.** In the trap of `001` a run that begins at a change is two to four black readings or three to five white ones
  (`runs_001`). In that of `011`, after a white reading at least six gate steps from the starting sample, the next white
  reading comes three, or six to seventeen, steps later (`gaps_011`). `avoids_001`, `avoids_011`: the words never read.
* **The single cell.** If the centre follows the word for `N` ticks from age `T`, the window at age `T + N` is in the trap,
  for `N` at least `3 T + 170`, or `3 T + 820`, at a gate tick (`centre_001`, `centre_011`).
* **What is left.** `Left001` and `Left011` (both open) ask that no finite left half keep column `-1` on its pattern with
  free-phase readings that avoid the complements of the listed forbidden gate words (`words001`, `words011`); together they
  exclude an eventual period three (`no_eventual_period_three_of_left`).

At period two the statement of this form, `Rule30PeriodTwoWidth13.RD` (entry, or an eventually periodic gate), is open.
Nothing here excludes `001` or `011`, and no gate is shown to be periodic.

The proof is one table for each word, of sets of times on spatial prefixes, walked once against itself with a whole period as
the step; the mechanism is that of `Rule30TrappedRunMasks`. Outside the trap for ever are the windows of an ether alone: at
fourteen cells beside `001`, and beside `011` at thirty. A finite half cannot show an ether for long: the erosion of
`Rule30EtherThreeErosion` with white cells in place of the ether beyond.

L. Hallee proves the lower bounds of the runs of `001` for every half (`lhallee/rule30-open`, `Columns.ThreeRuns`) and computes
entry beside `011` for halves of at most sixteen cells, and reduces `001` to a left half whose free readings avoid gate words
(`Columns.ConstrainedLeft001`). The words of the centre's own orbit are in
`Rule30PeriodThreeLanguage`.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ruliology.CellularAutomata.Rule30PeriodThreeEntry
open Rule30Jen Rule30Ether Rule30EtherThree Rule30EtherThreeErosion Rule30StripCertificates
open Rule30DrivenPrefix (step step_bit)
open Rule30TrappedRunMasks (Tree subset subset_sound)
open Rule30PeriodThreeEntryTables
open Rule30EtherThreeDeparture (IsRec ten_ticks)

/-! ### The walk of a table against itself -/

theorem walk_easy {a b : Tree} (va : a.valid = true) (vb : b.valid = true) (x y k t : Nat) {colours : Nat}
    (ok : subset ((a.high <<< 1) &&& colours) b.low = true) (ha : (a.value x (k+3)).testBit t = true)
    (hc : colours.testBit (t+1) = true) : (b.value y k).testBit (t+1) = true := by
  apply (b.bounds vb _ _ _).1
  apply subset_sound ok
  have hi := (a.bounds va _ _ _).2 ha
  simp [Nat.testBit_and, Nat.testBit_shiftLeft, hi, hc]

theorem step_succ (d : Bool) (a j : Nat) :
    (step d a).testBit (j+1) = xor (a.testBit j) (a.testBit (j+1) || a.testBit (j+2)) := by
  rw [step_bit]; simp

theorem step_zero (d : Bool) (a : Nat) : (step d a).testBit 0 = xor d (a.testBit 0 || a.testBit 1) := by
  rw [step_bit]; simp

theorem walk_sound {d0 d1 d2 : Bool} (n : Nat) {a b : Tree} {colours k x t : Nat} {x1 x2 y0 y1 zm z0 : Bool}
    (ok : walk colours a b x1 x2 y0 y1 zm z0 n = true) (va : a.valid = true) (vb : b.valid = true)
    (hx1 : x1 = x.testBit (k+2)) (hx2 : x2 = x.testBit (k+3))
    (hy0 : y0 = (step d0 x).testBit (k+1)) (hy1 : y1 = (step d0 x).testBit (k+2))
    (hzm : zm = (step d1 (step d0 x)).testBit k) (hz0 : z0 = (step d1 (step d0 x)).testBit (k+1))
    (ha : (a.value x (k+4)).testBit t = true) (hc : colours.testBit (t+1) = true) :
    (b.value (per d0 d1 d2 x) (k+1)).testBit (t+1) = true := by
  induction n generalizing a b k x1 x2 y0 y1 zm z0 with
  | zero => exact walk_easy va vb x _ (k+1) t ok ha hc
  | succ n ih =>
    simp only [walk] at ok
    split at ok
    · rename_i h; exact walk_easy va vb x _ (k+1) t h ha hc
    · obtain ⟨l, r⟩ := Bool.and_eq_true_iff.mp ok
      have ey : (step d0 x).testBit (k+3) = xor x1 (x2 || x.testBit (k+4)) := by rw [hx1, hx2, step_succ]
      have ez : (step d1 (step d0 x)).testBit (k+2) = xor y0 (y1 || (step d0 x).testBit (k+3)) := by
        rw [hy0, hy1, step_succ]
      have ew : (per d0 d1 d2 x).testBit (k+1) = xor zm (z0 || (step d1 (step d0 x)).testBit (k+2)) := by
        rw [hzm, hz0, per, step_succ]
      have next : ((a.child (x.testBit (k+4))).value x (k+1+4)).testBit t = true := by
        rw [show k+1+4 = (k+4)+1 by omega, Tree.child_value]; exact ha
      have fin : ((b.child ((per d0 d1 d2 x).testBit (k+1))).value (per d0 d1 d2 x) (k+1+1)).testBit (t+1) = true := by
        cases hb : x.testBit (k+4)
        · rw [hb] at next
          rw [hb] at ey
          have ey' : (step d0 x).testBit (k+3) = xor x1 x2 := by rw [ey]; simp
          rw [ey'] at ez
          rw [ez] at ew
          rw [ew]
          exact ih l (a.child_valid va _) (b.child_valid vb _) hx2 (by rw [hb]) hy1 ey'.symm hz0 ez.symm next
        · rw [hb] at next
          rw [hb] at ey
          have ey' : (step d0 x).testBit (k+3) = !x1 := by rw [ey]; simp
          rw [ey'] at ez
          rw [ez] at ew
          rw [ew]
          exact ih r (a.child_valid va _) (b.child_valid vb _) hx2 (by rw [hb]) hy1 ey'.symm hz0 ez.symm next
      simpa only [Tree.child_value] using fin

theorem walk_start {table : Tree} {white black : Nat} {d0 d1 d2 : Bool} (ok : walkAll table white black d0 d1 d2 = true)
    (x0 x1 x2 x3 : Bool) : walkAt table white black d0 d1 d2 x0 x1 x2 x3 = true := by
  have m (b : Bool) : b ∈ [false, true] := by cases b <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp ok x0 (m _)) x1 (m _)) x2 (m _)) x3 (m _)

/-- A time of a row passes to the next time of the row one period later, when the first cell there has an allowed colour. -/
theorem walk_all {table : Tree} {white black : Nat} {d0 d1 d2 : Bool} (va : table.valid = true)
    (ok : walkAll table white black d0 d1 d2 = true) (x t : Nat) (ha : (table.value x 0).testBit t = true)
    (hc : (if (per d0 d1 d2 x).testBit 0 then black else white).testBit (t+1) = true) :
    (table.value (per d0 d1 d2 x) 0).testBit (t+1) = true := by
  have w := walk_start ok (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3)
  simp only [walkAt] at w
  have y0 : (step d0 x).testBit 0 = xor d0 (x.testBit 0 || x.testBit 1) := step_zero ..
  have y1 : (step d0 x).testBit 1 = xor (x.testBit 0) (x.testBit 1 || x.testBit 2) := step_succ ..
  have y2 : (step d0 x).testBit 2 = xor (x.testBit 1) (x.testBit 2 || x.testBit 3) := step_succ ..
  have z0 : (step d1 (step d0 x)).testBit 0 = xor d1 ((step d0 x).testBit 0 || (step d0 x).testBit 1) := step_zero ..
  have z1 : (step d1 (step d0 x)).testBit 1 = xor ((step d0 x).testBit 0) ((step d0 x).testBit 1 || (step d0 x).testBit 2) := step_succ ..
  have w0 : (per d0 d1 d2 x).testBit 0 = xor d2 ((step d1 (step d0 x)).testBit 0 || (step d1 (step d0 x)).testBit 1) := by
    rw [per, step_zero]
  rw [← y0, ← y1, ← y2, ← z0, ← z1, ← w0] at w
  have start : ((((((table.child (x.testBit 0)).child (x.testBit 1)).child (x.testBit 2)).child (x.testBit 3)).value x 4).testBit t) = true := by
    rw [show (4:Nat) = 3+1 by rfl, Tree.child_value, show (3:Nat) = 2+1 by rfl, Tree.child_value, show (2:Nat) = 1+1 by rfl,
      Tree.child_value, show (1:Nat) = 0+1 by rfl, Tree.child_value]
    exact ha
  have vc := Tree.child_valid (Tree.child_valid (Tree.child_valid (Tree.child_valid va (x.testBit 0)) (x.testBit 1)) (x.testBit 2)) (x.testBit 3)
  have fin := walk_sound (d0 := d0) (d1 := d1) (d2 := d2) (k := 0) (x := x) (t := t) 46 w vc (Tree.child_valid va _) rfl rfl rfl rfl rfl rfl start hc
  rw [← Tree.child_value table (per d0 d1 d2 x) 0]
  exact fin

/-- The rows at successive periods. -/
def rows (d0 d1 d2 : Bool) (x : Nat) : Nat → Nat
  | 0 => x
  | i+1 => per d0 d1 d2 (rows d0 d1 d2 x i)

/-- A row carries its time along a line for as long as its first cells have the line's colours. -/
theorem march {table : Tree} {white black : Nat} {d0 d1 d2 : Bool} (va : table.valid = true)
    (ok : walkAll table white black d0 d1 d2 = true) {x o n : Nat} (start : (table.value x 0).testBit o = true)
    (cols : ∀ i, i < n → (if (rows d0 d1 d2 x (i+1)).testBit 0 then black else white).testBit (o+(i+1)) = true) :
    ∀ i, i ≤ n → (table.value (rows d0 d1 d2 x i) 0).testBit (o+i) = true := by
  intro i
  induction i with
  | zero => intro _; exact start
  | succ i ih =>
    intro hi
    exact walk_all va ok _ (o+i) (ih (by omega)) (cols i (by omega))

/-! ### Reading a table -/

theorem leaves_value {p : Nat → Bool} {a : Tree} (h : leaves p a = true) (r k : Nat) : p (a.value r k) = true := by
  induction a generalizing k with
  | leaf m => exact h
  | node lo hi a b ia ib =>
    simp only [leaves, Bool.and_eq_true] at h
    simp only [Tree.value]
    split
    · exact ib h.2 _
    · exact ia h.1 _

theorem mem_codes {t : Nat} (n : Nat) {a : Tree} (va : a.valid = true) {k p r : Nat} (hp : p = r % 2^k)
    (h : (a.value r k).testBit t = true) : r % 2^(k+n) ∈ codes t a k p n := by
  induction n generalizing a k p with
  | zero =>
    have hi := (a.bounds va r k t).2 h
    simp [codes, hi, hp]
  | succ n ih =>
    have hi := (a.bounds va r k t).2 h
    simp only [codes, hi, ite_true, List.mem_append]
    have kid := Tree.child_value a r k
    have split : r % 2^(k+1) = r % 2^k + 2^k * (r / 2^k % 2) := by rw [Nat.pow_succ]; exact Nat.mod_mul ..
    have bit := Nat.testBit_eq_decide_div_mod_eq (x := r) (i := k)
    have lt : r / 2^k % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [show k+(n+1) = k+1+n by omega]
    cases hb : r.testBit k
    · left
      have z : r / 2^k % 2 = 0 := by rw [hb] at bit; simp at bit; omega
      refine ih (a.child_valid va _) (by rw [split, z, hp]; simp) ?_
      rw [hb] at kid; rw [kid]; exact h
    · right
      have z : r / 2^k % 2 = 1 := by rw [hb] at bit; simpa using bit.symm
      refine ih (a.child_valid va _) (by rw [split, z, hp]; simp) ?_
      rw [hb] at kid; rw [kid]; exact h

theorem codes_low {t : Nat} (n : Nat) {a : Tree} {k p c : Nat} (hp : p < 2^k) (hc : c ∈ codes t a k p n) : c % 2^k = p := by
  induction n generalizing a k p with
  | zero =>
    simp only [codes] at hc
    split at hc
    · rw [List.mem_singleton.mp hc]; exact Nat.mod_eq_of_lt hp
    · simp at hc
  | succ n ih =>
    simp only [codes] at hc
    split at hc
    · have two : (2:Nat)^(k+1) = 2^k + 2^k := by rw [Nat.pow_succ]; omega
      have dvd : (2:Nat)^k ∣ 2^(k+1) := ⟨2, Nat.pow_succ ..⟩
      rcases List.mem_append.mp hc with h | h
      · have e := ih (by omega) h
        rw [← Nat.mod_mod_of_dvd c dvd, e, Nat.mod_eq_of_lt hp]
      · have e := ih (by omega) h
        rw [← Nat.mod_mod_of_dvd c dvd, e, Nat.add_mod_right, Nat.mod_eq_of_lt hp]
    · simp at hc

/-- A row whose next `n` cells are those of a listed code carries the time. -/
theorem codes_bit {t : Nat} (n : Nat) {a : Tree} (va : a.valid = true) (ht : tight t a n = true) {k p c r : Nat}
    (hp : p < 2^k) (hc : c ∈ codes t a k p n) (same : ∀ i, i < n → r.testBit (k+i) = c.testBit (k+i)) :
    (a.value r k).testBit t = true := by
  have easy (hi : a.high.testBit t = true) (e : (a.high.testBit t == a.low.testBit t) = true) : (a.value r k).testBit t = true := by
    apply (a.bounds va r k t).1
    rw [← beq_iff_eq.mp e]
    exact hi
  induction n generalizing a k p with
  | zero =>
    simp only [codes] at hc
    split at hc
    · rename_i hi; exact easy hi ht
    · simp at hc
  | succ n ih =>
    simp only [codes] at hc
    split at hc
    · rename_i hi
      simp only [tight, Bool.or_eq_true, Bool.and_eq_true] at ht
      rcases ht with ht | ⟨tl, tr⟩
      · exact easy hi ht
      · have two : (2:Nat)^(k+1) = 2^k + 2^k := by rw [Nat.pow_succ]; omega
        have e0 : r.testBit k = c.testBit k := same 0 (by omega)
        have rest : ∀ i, i < n → r.testBit (k+1+i) = c.testBit (k+1+i) := fun i hi => by
          have := same (i+1) (by omega)
          rw [show k+(i+1) = k+1+i by omega] at this; exact this
        have fin (b : Bool) (tb : tight t (a.child b) n = true) (q : Nat) (hq : q < 2^(k+1))
            (h : c ∈ codes t (a.child b) (k+1) q n) (hb : c.testBit k = b) : (a.value r k).testBit t = true := by
          rw [← Tree.child_value a r k, e0, hb]
          refine ih (a.child_valid va _) tb hq h rest (fun hi e => ?_)
          apply ((a.child b).bounds (a.child_valid va _) r (k+1) t).1
          rw [← beq_iff_eq.mp e]
          exact hi
        rcases List.mem_append.mp hc with h | h
        · refine fin false tl p (by omega) h ?_
          have low := codes_low n (by omega) h
          have b := congrArg (fun v : Nat => v.testBit k) low
          simp only [Nat.testBit_mod_two_pow] at b
          rw [Nat.testBit_lt_two_pow hp] at b
          simpa using b
        · refine fin true tr (p+2^k) (by omega) h ?_
          have low := codes_low n (by omega) h
          have b := congrArg (fun v : Nat => v.testBit k) low
          simp only [Nat.testBit_mod_two_pow] at b
          rw [show p+2^k = 2^k+p from Nat.add_comm .., Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hp] at b
          simpa using b
    · simp at hc

/-! ### The three kinds of line -/

section
variable {T : Tree} {white black : Nat} {d0 d1 d2 : Bool}

theorem free_march (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true) {x o n : Nat}
    (free : freeFrom white black o n = true) (start : (T.value x 0).testBit o = true) :
    (T.value (rows d0 d1 d2 x n) 0).testBit (o+n) = true := by
  refine march va ok start (fun i hi => ?_) n (Nat.le_refl _)
  have f := List.all_eq_true.mp free i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true] at f
  split
  · exact f.2
  · exact f.1

/-- **The closed set.** Bit 0 is carried to the row one period later. -/
theorem bit_closed (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true) {x : Nat}
    (h : (T.value x 0).testBit 0 = true) : (T.value (per d0 d1 d2 x) 0).testBit 0 = true := by
  have a := free_march va ok (n := 1) free h
  have l := beq_iff_eq.mp (leaves_value wrap (per d0 d1 d2 x) 0)
  rw [← l]
  exact a

theorem bit_stays (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true) {x : Nat}
    (h : (T.value x 0).testBit 0 = true) : ∀ i, (T.value (rows d0 d1 d2 x i) 0).testBit 0 = true
  | 0 => h
  | i+1 => bit_closed va ok free wrap (bit_stays va ok free wrap h i)

/-- **Entry.** After `m + n` periods every row is in the closed set, unless after `m` it has the exceptional bit `e`. -/
theorem bit_entry (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true) {A B m n e : Nat}
    (freeA : freeFrom white black A m = true) (freeB : freeFrom white black B n = true)
    (first : T.low.testBit A = true)
    (middle : leaves (fun k => !k.testBit (A+m) || (k.testBit B || k.testBit e)) T = true)
    (last : leaves (fun k => !k.testBit (B+n) || k.testBit 0) T = true) (x : Nat) :
    (T.value (rows d0 d1 d2 x m) 0).testBit e = true ∨
      (T.value (rows d0 d1 d2 (rows d0 d1 d2 x m) n) 0).testBit 0 = true := by
  have a := free_march va ok freeA ((T.bounds va x 0 A).1 first)
  have c := leaves_value middle (rows d0 d1 d2 x m) 0
  rw [a] at c
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at c
  rcases c with b | b
  · right
    have f := free_march va ok freeB b
    have l := leaves_value last (rows d0 d1 d2 (rows d0 d1 d2 x m) n) 0
    rw [f] at l
    simpa using l
  · exact Or.inl b

theorem mem_colours (c : Bool) : c ∈ [false, true] := by cases c <;> simp

/-- **A pattern that no row of the closed set reads.** -/
theorem bit_word (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true) {o : Nat} {v : List (Option Bool)}
    (line : wordLine T white black o v = true) (pos : 0 < v.length) {x : Nat} (h : (T.value x 0).testBit 0 = true)
    (read : ∀ i, i < v.length → fits (v.getD i none) ((rows d0 d1 d2 x i).testBit 0) = true) : False := by
  simp only [wordLine, Bool.and_eq_true] at line
  obtain ⟨⟨st, cl⟩, en⟩ := line
  have kid (y : Nat) (t : Nat) (hy : (T.value y 0).testBit t = true) :
      ((T.child (y.testBit 0)).value y 1).testBit t = true := by rw [Tree.child_value T y 0]; exact hy
  have start : (T.value x 0).testBit o = true := by
    have r0 := read 0 pos
    have hd : v.headD none = v.getD 0 none := by cases v <;> rfl
    have s := List.all_eq_true.mp st _ (mem_colours (x.testBit 0))
    rw [hd] at s
    rw [show rows d0 d1 d2 x 0 = x from rfl] at r0
    rw [r0] at s
    simp only [Bool.not_true, Bool.false_or] at s
    have l := leaves_value s x 1
    rw [kid x 0 h] at l
    rw [← Tree.child_value T x 0]
    simpa using l
  have all := march (n := v.length - 1) va ok start (fun i hi => by
    have c := List.all_eq_true.mp (List.all_eq_true.mp cl i (List.mem_range.mpr hi)) _ (mem_colours ((rows d0 d1 d2 x (i+1)).testBit 0))
    rw [read (i+1) (by omega)] at c
    simpa using c) (v.length - 1) (Nat.le_refl _)
  have e := List.all_eq_true.mp en _ (mem_colours ((rows d0 d1 d2 x (v.length-1)).testBit 0))
  rw [read (v.length - 1) (by omega)] at e
  simp only [Bool.not_true, Bool.false_or] at e
  have l := leaves_value e (rows d0 d1 d2 x (v.length-1)) 1
  rw [kid _ _ all] at l
  simp at l

end

/-! ### Packed rows of an evolution -/

/-- `x` holds the first `L` cells of the half at tick `t`. -/
def Fits (F : Nat → Nat → Bool) (t x L : Nat) : Prop := ∀ j, j < L → x.testBit j = F t (j+1)

theorem Fits.mono {F : Nat → Nat → Bool} {t x L M : Nat} (h : Fits F t x L) (le : M ≤ L) : Fits F t x M :=
  fun j hj => h j (by omega)

theorem fits_step {F : Nat → Nat → Bool} (hF : IsR30 F) {t x L : Nat} {d : Bool} (h0 : F t 0 = d) (h : Fits F t x (L+1)) :
    Fits F (t+1) (step d x) L := by
  intro j hj
  rw [step_bit, hF t j, h j (by omega), h (j+1) (by omega)]
  unfold Rule30Jen.rule
  cases j with
  | zero => simp [h0]
  | succ j => simp [h j (by omega)]

theorem fits_per {F : Nat → Nat → Bool} (hF : IsR30 F) {t x L : Nat} {d0 d1 d2 : Bool} (h0 : F t 0 = d0)
    (h1 : F (t+1) 0 = d1) (h2 : F (t+2) 0 = d2) (h : Fits F t x (L+3)) : Fits F (t+3) (per d0 d1 d2 x) L :=
  fits_step hF h2 (fits_step hF h1 (fits_step hF h0 h))

/-- The drive reads `d0 d1 d2` over the `n` periods from `t`. -/
def Drive (F : Nat → Nat → Bool) (d0 d1 d2 : Bool) (t n : Nat) : Prop :=
  ∀ i, i < n → F (t+3*i) 0 = d0 ∧ F (t+3*i+1) 0 = d1 ∧ F (t+3*i+2) 0 = d2

theorem fits_rows {F : Nat → Nat → Bool} (hF : IsR30 F) {t x L n : Nat} {d0 d1 d2 : Bool} (hd : Drive F d0 d1 d2 t n)
    (h : Fits F t x (L+3*n)) : ∀ i, i ≤ n → Fits F (t+3*i) (rows d0 d1 d2 x i) (L+3*(n-i)) := by
  intro i
  induction i with
  | zero => intro _; exact h
  | succ i ih =>
    intro hi
    obtain ⟨h0, h1, h2⟩ := hd i (by omega)
    have f := ih (by omega)
    rw [show L+3*(n-i) = L+3*(n-(i+1))+3 by omega] at f
    exact fits_per hF h0 h1 h2 f

/-- The first `n` cells of the half at tick `t`, as a number, the first cell in the low bit. -/
def code (F : Nat → Nat → Bool) (t n : Nat) : Nat := encList (seg (fun j => F t (j+1)) n)

theorem prefix_bit : ∀ (n : Nat) (f : Nat → Bool) (j : Nat), (encList (seg f n)).testBit j = (decide (j < n) && f j)
  | 0, _, j => by simp [seg, encList]
  | n+1, f, 0 => by
    rw [Nat.testBit_zero]
    simp only [seg, encList]
    cases f 0 <;> simp <;> omega
  | n+1, f, j+1 => by
    rw [Nat.testBit_succ]
    change (((if f 0 then 1 else 0) + 2 * encList (seg (fun i => f (i+1)) n)) / 2).testBit j = _
    have e (a : Nat) : ((if f 0 then 1 else 0) + 2*a) / 2 = a := by cases f 0 <;> simp <;> omega
    rw [e, prefix_bit n _ j]
    simp

theorem code_bit (F : Nat → Nat → Bool) (t n j : Nat) : (code F t n).testBit j = (decide (j < n) && F t (j+1)) :=
  prefix_bit n _ j

theorem fits_code (F : Nat → Nat → Bool) (t L : Nat) : Fits F t (code F t L) L := by
  intro j hj
  rw [code_bit]
  simp [hj]

theorem code_of_fits {F : Nat → Nat → Bool} {t x L n : Nat} (h : Fits F t x L) (le : n ≤ L) : x % 2^n = code F t n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, code_bit]
  by_cases hj : j < n
  · simp [hj, h j (by omega)]
  · simp [hj]

theorem code_lt (F : Nat → Nat → Bool) (t n : Nat) : code F t n < 2^n := by
  rw [← code_of_fits (fits_code F t n) (Nat.le_refl n)]
  exact Nat.mod_lt _ (Nat.two_pow_pos n)

theorem cell_of_code {F : Nat → Nat → Bool} {t n c : Nat} (h : code F t n = c) {j : Nat} (hj : j < n) :
    F t (j+1) = c.testBit j := by
  rw [← h, code_bit]
  simp [hj]

/-! ### The trap of a table -/

/-- The first fourteen cells of the half at tick `t` are a window of the list. -/
def InTrap (trap : List Nat) (F : Nat → Nat → Bool) (t : Nat) : Prop := code F t 14 ∈ trap

section
variable {T : Tree} {trap : List Nat}

theorem trap_of_bit (va : T.valid = true) (is : isTrap T trap = true) {F : Nat → Nat → Bool} {t x L : Nat}
    (h : Fits F t x L) (le : 14 ≤ L) (hb : (T.value x 0).testBit 0 = true) : InTrap trap F t := by
  simp only [isTrap, Bool.and_eq_true] at is
  have m := mem_codes (t := 0) 14 va (k := 0) (p := 0) (r := x) (by simp [Nat.mod_one]) hb
  rw [beq_iff_eq.mp is.1, Nat.zero_add] at m
  unfold InTrap
  rw [← code_of_fits h le]
  exact m

theorem bit_of_trap (va : T.valid = true) (is : isTrap T trap = true) {F : Nat → Nat → Bool} {t x L : Nat}
    (h : Fits F t x L) (le : 14 ≤ L) (hb : InTrap trap F t) : (T.value x 0).testBit 0 = true := by
  simp only [isTrap, Bool.and_eq_true] at is
  refine codes_bit 14 va is.2 (k := 0) (p := 0) (c := code F t 14) (by decide) (by rw [beq_iff_eq.mp is.1]; exact hb)
    (fun i hi => ?_)
  rw [Nat.zero_add, code_bit, h i (by omega)]
  simp [hi]

end

/-! ### A finite half leaves the ether

`Rule30EtherThreeErosion.erosion3_fin` with white cells, in place of the ether, beyond the disturbance. -/

theorem drv_white {c R : Nat → Bool} {D : Nat} (h : ∀ p, D < p → R p = false) : ∀ t p, D + t < p → drv c R t p = false
  | 0, p, hp => by rw [drv_init c R p (by omega)]; exact h p (by omega)
  | t+1, p, hp => by
    obtain ⟨q, rfl⟩ : ∃ q, p = q+1 := ⟨p-1, by omega⟩
    rw [drv_isR30 c R t q]
    unfold Rule30Jen.rule
    rw [drv_white h t q (by omega), drv_white h t (q+1) (by omega), drv_white h t (q+2) (by omega)]
    rfl

theorem ether_black : ∀ c, c < 12 → ∀ φ, φ < 3 → ∃ i, i < 12 ∧ ether3 (c+i) φ = true := by decide

section
variable {F : Nat → Nat → Bool} {j0 s t1 B k : Nat}

/-- Beyond a finite half the ether is somewhere black: a defect within twelve columns. -/
theorem defect (hw : ∀ t p, B + t < p → F t p = false) (t : Nat) : ∃ p, p ≤ B+t+12 ∧ F t p ≠ eth j0 s p t := by
  obtain ⟨i, hi, e⟩ := ether_black ((j0+(B+t+1)) % 12) (Nat.mod_lt _ (by decide)) ((t+s) % 3) (Nat.mod_lt _ (by decide))
  refine ⟨B+t+1+i, by omega, ?_⟩
  rw [hw t _ (by omega)]
  have e' : eth j0 s (B+t+1+i) t = true := by
    unfold eth
    rw [← e]
    exact ether3_congr (by omega) (by omega)
  rw [e']
  decide

theorem front_le (hw : ∀ t p, B + t < p → F t p = false) {t D : Nat} (hD : Front F j0 s t D) : D ≤ B+t+12 := by
  obtain ⟨p, hp, ne⟩ := defect (j0 := j0) (s := s) hw t
  refine Nat.le_trans (Nat.le_of_not_lt fun h => ne (hD.1 p h)) hp

/-- A run of the bad state is short: it gains seven columns a tick on the last black cell. -/
theorem run_short (hF : IsR30 F) (h0 : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t) (hw : ∀ t p, B + t < p → F t p = false) :
    ∀ m t D, t1 ≤ t → 2 ≤ D → Front F j0 s t D → IsB F j0 s t D → B+t+12 < D + 7*m →
      ∃ n, n < m ∧ ∃ D', Front F j0 s (t+n+1) D' ∧ ¬ IsB F j0 s (t+n+1) D' := by
  intro m
  induction m with
  | zero =>
    intro t D _ _ hD _ hR
    have := front_le hw hD
    omega
  | succ m ih =>
    intro t D ht hD2 hD hB hR
    obtain ⟨p, -, ne⟩ := defect (j0 := j0) (s := s) hw (t+1)
    obtain ⟨D', hD', hle, h | h | h⟩ := front_step hF (h0 (t+1) (by omega)) hD2 hD ⟨p, ne⟩
    · exact absurd hB h.1
    · exact ⟨0, by omega, D', hD', h.2.1⟩
    · by_cases hB' : IsB F j0 s (t+1) D'
      · have c1 := isB_cls hB
        have c2 := isB_cls hB'
        unfold cls at c1 c2
        have h8 : D + 8 ≤ D' := by omega
        obtain ⟨n, hn, D'', h1, h2⟩ := ih (t+1) D' (by omega) (by omega) hD' hB' (by omega)
        refine ⟨n+1, by omega, D'', ?_, ?_⟩
        · rw [show t+(n+1)+1 = t+1+n+1 by omega]; exact h1
        · rw [show t+(n+1)+1 = t+1+n+1 by omega]; exact h2
      · exact ⟨0, by omega, D', hD', hB'⟩

/-- **A finite half leaves the ether in linear time.** -/
theorem erode (hF : IsR30 F) (hk : 1 ≤ k) (h0 : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t)
    (hw : ∀ t p, B + t < p → F t p = false) (hL : ∀ p, 1 ≤ p → p ≤ k → F t1 p = eth j0 s p t1) :
    ∃ t, t1 ≤ t ∧ t ≤ t1 + 3*(B+t1+12) + 6 ∧ ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ eth j0 s p t := by
  have hex : ∀ t, t1 ≤ t → ∃ p, F t p ≠ eth j0 s p t := fun t _ => by
    obtain ⟨p, -, ne⟩ := defect (j0 := j0) (s := s) hw t
    exact ⟨p, ne⟩
  obtain ⟨p0, hp0⟩ := hex t1 (Nat.le_refl _)
  obtain ⟨D1, hD1, hminD⟩ := exists_least (P := fun p => F t1 p ≠ eth j0 s p t1) p0 hp0
  have hfr1 : Front F j0 s t1 D1 := ⟨fun p hp => Classical.not_not.1 (hminD p hp), hD1⟩
  have hD1k : k < D1 := by
    refine Nat.lt_of_not_le fun h => hD1 ?_
    rcases Nat.eq_zero_or_pos D1 with h1 | h1
    · subst h1; exact h0 t1 (Nat.le_refl _)
    · exact hL D1 h1 h
  have hD1R := front_le hw hfr1
  have finish : ∀ t0 D0, t1 ≤ t0 → Front F j0 s t0 D0 → ¬ IsB F j0 s t0 D0 →
      ∃ t, t0 ≤ t ∧ t ≤ t0 + (5*(D0-k)+5)/2 + 1 ∧ ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ eth j0 s p t := by
    intro t0 D0 ht0 hD0 hB0
    rcases wake_good hF hk h0 hex ((5*(D0-k)+5)/2+1) t0 D0 ht0 hD0 hB0 with ⟨t', h1, h2, hp⟩ | ⟨D', hD', -, hpot⟩
    · exact ⟨t', h1, h2, hp⟩
    · have hψ := psiF_le F j0 s t0 D0
      by_cases hDk : D' ≤ k
      · refine ⟨t0 + ((5*(D0-k)+5)/2+1), by omega, by omega, D', ?_, hDk, hD'.2⟩
        refine Nat.pos_of_ne_zero fun h => hD'.2 ?_
        subst h; exact h0 _ (by omega)
      · omega
  by_cases hB1 : IsB F j0 s t1 D1
  · obtain ⟨n, hn, D0, hD0, hB0⟩ :=
      run_short hF h0 hw ((B+t1+12-D1)/7+1) t1 D1 (Nat.le_refl _) (by omega) hfr1 hB1 (by omega)
    have hD0R := front_le hw hD0
    obtain ⟨t, h1, h2, hp⟩ := finish (t1+n+1) D0 (by omega) hD0 hB0
    exact ⟨t, by omega, by omega, hp⟩
  · obtain ⟨t, h1, h2, hp⟩ := finish t1 D1 (Nat.le_refl _) hfr1 hB1
    exact ⟨t, h1, by omega, hp⟩

end

/-- The right half `R`, driven by the word `w` from phase `φ`. -/
def half (w : List Bool) (R : Nat → Bool) (φ : Nat) : Nat → Nat → Bool := drv (fun t => wordAt3 w (t+φ)) R

theorem half_isR30 (w : List Bool) (R : Nat → Bool) (φ : Nat) : IsR30 (half w R φ) := drv_isR30 _ _

theorem half_zero (w : List Bool) (R : Nat → Bool) (φ t : Nat) : half w R φ t 0 = wordAt3 w (t+φ) := drv_col0 _ _ _

/-- Columns `1` to `k` read the ether column `j0 + p` at tick `t`. -/
def EtherOn (F : Nat → Nat → Bool) (j0 φ t k : Nat) : Prop := ∀ p, 1 ≤ p → p ≤ k → F t p = eth j0 φ p t

theorem etherOn_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 φ t k : Nat} (h0 : F t 0 = eth j0 φ 0 t)
    (h : EtherOn F j0 φ t (k+1)) : EtherOn F j0 φ (t+1) k := by
  intro p hp hk
  obtain ⟨q, rfl⟩ : ∃ q, p = q+1 := ⟨p-1, by omega⟩
  rw [hF t q, eth_rule]
  have e0 : F t q = eth j0 φ q t := by
    rcases Nat.eq_zero_or_pos q with z | z
    · subst z; exact h0
    · exact h q z (by omega)
  rw [e0, h (q+1) (by omega) (by omega), h (q+2) (by omega) (by omega)]

/-- **How long a finite half can show the ether** on its first `k + 2` cells at the ticks `t1, t1 + 3, …, t1 + 3 n`. -/
theorem ether_ends {w : List Bool} {j0 : Nat} (al : ∀ ψ, ether3 j0 ψ = wordAt3 w ψ) {R : Nat → Bool} {D : Nat}
    (hR : ∀ p, D < p → R p = false) {φ t1 n k : Nat} (hk : 1 ≤ k)
    (h : ∀ i, i ≤ n → EtherOn (half w R φ) j0 φ (t1+3*i) (k+2)) : t1+3*n+2 < t1 + 3*(D+t1+12) + 7 := by
  have hF := half_isR30 w R φ
  have h0 (t : Nat) : half w R φ t 0 = eth j0 φ 0 t := by
    rw [half_zero]; unfold eth; rw [Nat.add_zero, al]
  obtain ⟨t, lo, hi, p, hp, hpk, ne⟩ := erode (j0 := j0) (s := φ) (k := k) (t1 := t1) (B := D) hF hk (fun t _ => h0 t)
    (fun t p hp => drv_white hR t p hp) (fun p hp hpk => by
      have := h 0 (by omega) p hp (by omega)
      rwa [show t1 + 3*0 = t1 by omega] at this)
  refine Nat.lt_of_not_le fun le => ne ?_
  obtain ⟨i, r, hi3, hr⟩ : ∃ i r, t = t1 + 3*i + r ∧ r < 3 := ⟨(t-t1)/3, (t-t1)%3, by omega, by omega⟩
  have base := h i (by omega)
  have one := etherOn_step hF (h0 _) base
  have two := etherOn_step hF (h0 _) one
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
  · rw [hi3]; exact base p hp (by omega)
  · rw [hi3]; exact one p hp (by omega)
  · rw [hi3]; exact two p hp hpk

/-! ### The trap is closed, and entry -/

theorem rows_add (d0 d1 d2 : Bool) (x a : Nat) : ∀ b, rows d0 d1 d2 x (a+b) = rows d0 d1 d2 (rows d0 d1 d2 x a) b
  | 0 => rfl
  | b+1 => by rw [← Nat.add_assoc]; exact congrArg _ (rows_add d0 d1 d2 x a b)

theorem Drive.mono {F : Nat → Nat → Bool} {d0 d1 d2 : Bool} {t n m : Nat} (h : Drive F d0 d1 d2 t n) (le : m ≤ n) :
    Drive F d0 d1 d2 t m := fun i hi => h i (by omega)

theorem Drive.shift {F : Nat → Nat → Bool} {d0 d1 d2 : Bool} {t n : Nat} (k : Nat) (h : Drive F d0 d1 d2 t (k+n)) :
    Drive F d0 d1 d2 (t+3*k) n := by
  intro i hi
  have := h (k+i) (by omega)
  rwa [show t+3*(k+i) = t+3*k+3*i by omega] at this

/-- The drive of a word from a tick of phase `g`. -/
theorem drive_half {w : List Bool} {R : Nat → Bool} {φ t g : Nat} (ht : (t+φ) % 3 = g % 3) (n : Nat) :
    Drive (half w R φ) (wordAt3 w g) (wordAt3 w (g+1)) (wordAt3 w (g+2)) t n := by
  intro i _
  refine ⟨?_, ?_, ?_⟩ <;> rw [half_zero] <;> unfold wordAt3 <;> congr 1 <;> omega

section
variable {T : Tree} {white black : Nat} {d0 d1 d2 : Bool} {trap : List Nat} {F : Nat → Nat → Bool}

theorem trap_row (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true)
    (is : isTrap T trap = true) (hF : IsR30 F) {t n : Nat} (hd : Drive F d0 d1 d2 t n) (h : InTrap trap F t) :
    ∃ x, (∀ i, i ≤ n → Fits F (t+3*i) (rows d0 d1 d2 x i) (14+3*(n-i))) ∧
      ∀ i, (T.value (rows d0 d1 d2 x i) 0).testBit 0 = true := by
  have f := fits_code F t (14+3*n)
  exact ⟨_, fits_rows hF hd f, bit_stays va ok free wrap (bit_of_trap va is f (by omega) h)⟩

theorem trap_stays (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true)
    (is : isTrap T trap = true) (hF : IsR30 F) {t n : Nat} (hd : Drive F d0 d1 d2 t n) (h : InTrap trap F t) :
    InTrap trap F (t+3*n) := by
  obtain ⟨x, fx, bx⟩ := trap_row va ok free wrap is hF hd h
  exact trap_of_bit va is (fx n (Nat.le_refl _)) (by omega) (bx n)

theorem trap_entry (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true) (is : isTrap T trap = true)
    {A B m n e W : Nat} {outs : List Nat} (freeA : freeFrom white black A m = true) (freeB : freeFrom white black B n = true)
    (first : T.low.testBit A = true) (middle : leaves (fun k => !k.testBit (A+m) || (k.testBit B || k.testBit e)) T = true)
    (last : leaves (fun k => !k.testBit (B+n) || k.testBit 0) T = true) (outCodes : codes e T 0 0 W = outs)
    (hF : IsR30 F) {t : Nat} (hd : Drive F d0 d1 d2 t (m+n)) : InTrap trap F (t+3*(m+n)) ∨ code F (t+3*m) W ∈ outs := by
  have f := fits_code F t (14+W+3*(m+n))
  have fx := fits_rows hF hd f
  rcases bit_entry va ok freeA freeB first middle last (code F t (14+W+3*(m+n))) with h | h
  · right
    have mem := mem_codes (t := e) W va (k := 0) (p := 0) (r := rows d0 d1 d2 (code F t (14+W+3*(m+n))) m)
      (by simp [Nat.mod_one]) h
    rw [outCodes, Nat.zero_add, code_of_fits (fx m (by omega)) (by omega)] at mem
    exact mem
  · left
    rw [← rows_add] at h
    exact trap_of_bit va is (fx (m+n) (Nat.le_refl _)) (by omega) h

/-- A half that is not in the trap at a tick was outside, and showed an exceptional window, at every earlier one. -/
theorem outside_before (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true)
    (is : isTrap T trap = true) {A B m n e W : Nat} {outs : List Nat} (freeA : freeFrom white black A m = true)
    (freeB : freeFrom white black B n = true) (first : T.low.testBit A = true)
    (middle : leaves (fun k => !k.testBit (A+m) || (k.testBit B || k.testBit e)) T = true)
    (last : leaves (fun k => !k.testBit (B+n) || k.testBit 0) T = true) (outCodes : codes e T 0 0 W = outs)
    (hF : IsR30 F) {t q : Nat} (hd : Drive F d0 d1 d2 t (m+n+q)) (no : ¬ InTrap trap F (t+3*(m+n+q))) :
    ∀ i, i ≤ q → code F (t+3*m+3*i) W ∈ outs := by
  intro i hi
  have hd' := (hd.mono (m := i+(m+n)) (by omega)).shift i
  rcases trap_entry va ok is freeA freeB first middle last outCodes hF hd' with h | h
  · exfalso
    apply no
    have tail := (hd.mono (m := (i+(m+n))+(q-i)) (by omega)).shift (i+(m+n))
    rw [show t+3*(i+(m+n)) = t+3*i+3*(m+n) by omega] at tail
    have s := trap_stays va ok free wrap is hF tail h
    rwa [show t+3*i+3*(m+n)+3*(q-i) = t+3*(m+n+q) by omega] at s
  · rwa [show t+3*i+3*m = t+3*m+3*i by omega] at h

end

/-! ### The windows that can stay outside -/

theorem image_mem {F : Nat → Nat → Bool} (hF : IsR30 F) {d0 d1 d2 : Bool} {t : Nat} (hd : Drive F d0 d1 d2 t 1) (W : Nat) :
    code F (t+3) W ∈ images d0 d1 d2 W (code F t W) := by
  obtain ⟨h0, h1, h2⟩ := hd 0 (by omega)
  have f := fits_code F t (W+3)
  have g := code_of_fits (fits_per hF h0 h1 h2 f) (Nat.le_refl W)
  refine List.mem_map.mpr ⟨code F t (W+3) / 2^W, ?_, ?_⟩
  · have lt := code_lt F t (W+3)
    rw [List.mem_range, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos W)]
    rw [Nat.pow_add] at lt
    omega
  · have m := code_of_fits (f.mono (M := W) (by omega)) (Nat.le_refl W)
    show per d0 d1 d2 (code F t W + 2^W * (code F t (W+3) / 2^W)) % 2^W = code F (t+3) W
    rw [← m, Nat.mod_add_div]
    exact g

/-- The window is in the list at `n + 1` successive periods from `t`. -/
def Among (F : Nat → Nat → Bool) (t n W : Nat) (A : List Nat) : Prop := ∀ i, i ≤ n → code F (t+3*i) W ∈ A

section
variable {F : Nat → Nat → Bool} {d0 d1 d2 : Bool}

theorem among_round (hF : IsR30 F) {t n W : Nat} {A : List Nat} (hd : Drive F d0 d1 d2 t (n+2)) (h : Among F t (n+2) W A) :
    Among F (t+3) n W (fwd d0 d1 d2 W (back d0 d1 d2 W A)) := by
  have im (i : Nat) (hi : i < n+2) : code F (t+3*(i+1)) W ∈ images d0 d1 d2 W (code F (t+3*i) W) := by
    have := image_mem hF ((hd.mono (m := i+1) (by omega)).shift i) W
    rwa [show t+3*i+3 = t+3*(i+1) by omega] at this
  have b (i : Nat) (hi : i < n+2) : code F (t+3*i) W ∈ back d0 d1 d2 W A := by
    refine List.mem_filter.mpr ⟨h i (by omega), List.any_eq_true.mpr ⟨_, im i hi, ?_⟩⟩
    exact List.contains_iff_mem.mpr (h (i+1) (by omega))
  intro i hi
  rw [show t+3+3*i = t+3*(i+1) by omega]
  refine List.mem_filter.mpr ⟨b (i+1) (by omega), List.contains_iff_mem.mpr ?_⟩
  exact List.mem_flatMap.mpr ⟨_, b i (by omega), im i (by omega)⟩

theorem among_rounds (hF : IsR30 F) {W : Nat} : ∀ (r : Nat) {t n : Nat} {A : List Nat}, Drive F d0 d1 d2 t (n+2*r) →
    Among F t (n+2*r) W A → Among F (t+3*r) n W (rounds d0 d1 d2 W r A)
  | 0, _, _, _, _, h => h
  | r+1, t, n, A, hd, h => by
    have s := among_round hF (n := n+2*r) hd h
    have d := ((hd.mono (m := 1+(n+2*r)) (by omega)).shift 1)
    have q := among_rounds hF r (t := t+3) (n := n) d s
    rwa [show t+3+3*r = t+3*(r+1) by omega] at q

theorem among_widen {t n W : Nat} {A : List Nat} (h : Among F t n W A) : Among F t n (W+1) (widen W A) := by
  intro i hi
  have a := h i hi
  rw [← code_of_fits ((fits_code F (t+3*i) (W+1)).mono (M := W) (by omega)) (Nat.le_refl W)] at a
  have lt := code_lt F (t+3*i) (W+1)
  have split := Nat.mod_add_div (code F (t+3*i) (W+1)) (2^W)
  have two : code F (t+3*i) (W+1) / 2^W < 2 := by
    apply Nat.div_lt_of_lt_mul
    rwa [Nat.pow_succ] at lt
  have either : code F (t+3*i) (W+1) / 2^W = 0 ∨ code F (t+3*i) (W+1) / 2^W = 1 := by
    revert two
    generalize code F (t+3*i) (W+1) / 2^W = d
    omega
  rw [← split]
  rcases either with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero]
    exact List.mem_append.mpr (Or.inl a)
  · rw [e, Nat.mul_one]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, a, rfl⟩))

theorem among_chase (hF : IsR30 F) : ∀ (rs : List Nat) {W t n : Nat} {A : List Nat}, Drive F d0 d1 d2 t (n+2*rs.sum) →
    Among F t (n+2*rs.sum) W A → Among F (t+3*rs.sum) n (W+rs.length) (chase d0 d1 d2 W rs A)
  | [], _, _, _, _, _, h => h
  | r :: rs, W, t, n, A, hd, h => by
    have e : n+2*(r :: rs).sum = (n+2*rs.sum)+2*r := by rw [List.sum_cons]; omega
    rw [e] at hd h
    have s := among_widen (among_rounds hF r hd h)
    have d := (hd.mono (m := r+(n+2*rs.sum)) (by omega)).shift r
    have q := among_chase hF rs d s
    have e1 : t+3*r+3*rs.sum = t+3*(r :: rs).sum := by rw [List.sum_cons]; omega
    have e2 : W+1+rs.length = W+(r :: rs).length := by rw [List.length_cons]; omega
    rwa [e1, e2] at q

end

/-! ### The two words -/

/-- The half at a gate tick shows the ether column `j0` when its code is the ether's. -/
theorem etherOn_of_code {F : Nat → Nat → Bool} {j0 φ t g W c : Nat} (ht : (t+φ) % 3 = g % 3)
    (hc : ((List.range W).all fun j => c.testBit j == ether3 (j0+(j+1)) g) = true) (h : code F t W = c) :
    EtherOn F j0 φ t W := by
  intro p hp hW
  obtain ⟨j, rfl⟩ : ∃ j, p = j+1 := ⟨p-1, by omega⟩
  rw [cell_of_code h (by omega), beq_iff_eq.mp (List.all_eq_true.mp hc j (List.mem_range.mpr (by omega)))]
  exact ether3_congr rfl ht.symm

theorem code_same {F : Nat → Nat → Bool} (hF : IsR30 F) {d0 d1 d2 : Bool} {t n W : Nat} {A : List Nat}
    (alone : (A.all fun a => A.all fun b => !(images d0 d1 d2 W a).contains b || b == a) = true)
    (hd : Drive F d0 d1 d2 t n) (h : Among F t n W A) : ∀ i, i ≤ n → code F (t+3*i) W = code F t W := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have im := image_mem hF ((hd.mono (m := i+1) (by omega)).shift i) W
    rw [show t+3*i+3 = t+3*(i+1) by omega] at im
    have c := List.all_eq_true.mp (List.all_eq_true.mp alone _ (h i (by omega))) _ (h (i+1) hi)
    rw [List.contains_iff_mem.mpr im] at c
    have c' : code F (t+3*(i+1)) W = code F (t+3*i) W := by simpa using c
    rw [c']
    exact ih (by omega)

/-- What a half shows while it is outside the trap of `001`: one ether. -/
theorem outside_001 {F : Nat → Nat → Bool} (hF : IsR30 F) {t q : Nat} (hd : Drive F false true false t (16+q))
    (no : ¬ InTrap trap001 F (t+3*(16+q))) :
    (∀ i, i ≤ q → code F (t+24+3*i) 14 = 9278) ∨ (∀ i, i ≤ q → code F (t+24+3*i) 14 = 12831) := by
  have a : Among F (t+24) q 14 outside001 := fun i hi =>
    outside_before (m := 8) (n := 8) valid001 walk001 free001 wrap001 isTrap001 freeA001 freeB001 first001 middle001 last001
      outsideCodes001 hF hd no i hi
  have s := code_same hF (A := outside001) (d0 := false) (d1 := true) (d2 := false) (by decide +kernel)
    ((hd.mono (m := 8+q) (by omega)).shift 8) a
  have z := a 0 (by omega)
  simp only [outside001, List.mem_cons, List.not_mem_nil, or_false] at z
  rcases z with z | z
  · left; intro i hi; rw [s i hi]; exact z
  · right; intro i hi; rw [s i hi]; exact z

/-- What a half shows while it is outside the trap of `011`: the ether with the white gate. -/
theorem outside_011 {F : Nat → Nat → Bool} (hF : IsR30 F) {t q : Nat} (hd : Drive F false true true t (102+q))
    (no : ¬ InTrap trap011 F (t+3*(102+q))) : ∀ i, i ≤ q → code F (t+153+3*i) 30 = 142378952 := by
  have e : 102+q = 24+24+(q+54) := by omega
  rw [e] at hd no
  have a : Among F (t+72) (q+54) 18 outside011 := fun i hi =>
    outside_before (m := 24) (n := 24) valid011 walk011 free011 wrap011 isTrap011 freeA011 freeB011 first011 middle011 last011
      outsideCodes011 hF hd no i hi
  have total : stages.sum = 24 := rfl
  have d := (hd.mono (m := 24+((q+6)+2*stages.sum)) (by rw [total]; omega)).shift 24
  have b := among_chase hF stages (n := q+6) d (by rw [total]; exact a)
  have d' := (hd.mono (m := 48+(q+2*3)) (by omega)).shift 48
  rw [total, show t+3*24+3*24 = t+3*48 by omega, show 18+stages.length = 30 from rfl] at b
  have c := among_rounds hF 3 (n := q) d' b
  rw [chase_011] at c
  intro i hi
  have m := c i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at m
  rwa [show t+3*48+3*3+3*i = t+153+3*i by omega] at m

/-! ### Every finite half enters -/

/-- **Entry beside `001`.** A right half whose cells beyond `D` are white, driven by `001` from any phase, is in the trap at
every gate tick from `3 D + 170` on. -/
theorem finite_enters_001 {R : Nat → Bool} {D : Nat} (hR : ∀ p, D < p → R p = false) {φ t : Nat} (ht : (t+φ) % 3 = 1)
    (late : 3*D+170 ≤ t) : InTrap trap001 (half w001 R φ) t := by
  apply Classical.byContradiction
  intro no
  obtain ⟨t0, q, e, small⟩ : ∃ t0 q, t = t0+3*(16+q) ∧ t0 < 3 := ⟨t%3, t/3-16, by omega, by omega⟩
  have g : (t0+φ) % 3 = 1 % 3 := by omega
  have hd : Drive (half w001 R φ) false true false t0 (16+q) := drive_half g _
  rw [e] at no
  have fin (j0 c : Nat) (al : aligned3 w001 j0 0 = true)
      (hc : ((List.range 14).all fun j => c.testBit j == ether3 (j0+(j+1)) 1) = true)
      (h : ∀ i, i ≤ q → code (half w001 R φ) (t0+24+3*i) 14 = c) : False := by
    have := ether_ends (w := w001) (j0 := j0) (φ := φ) (t1 := t0+24) (n := q) (k := 12) (aligned3_spec al) hR (by omega)
      (fun i hi => etherOn_of_code (g := 1) (by omega) hc (h i hi))
    omega
  rcases outside_001 (half_isR30 _ _ _) hd no with h | h
  · exact fin 0 _ (by decide) (by decide) h
  · exact fin 1 _ (by decide) (by decide) h

/-- **Entry beside `011`,** at every gate tick from `3 D + 820` on. -/
theorem finite_enters_011 {R : Nat → Bool} {D : Nat} (hR : ∀ p, D < p → R p = false) {φ t : Nat} (ht : (t+φ) % 3 = 0)
    (late : 3*D+820 ≤ t) : InTrap trap011 (half w011 R φ) t := by
  apply Classical.byContradiction
  intro no
  obtain ⟨t0, q, e, small⟩ : ∃ t0 q, t = t0+3*(102+q) ∧ t0 < 3 := ⟨t%3, t/3-102, by omega, by omega⟩
  have g : (t0+φ) % 3 = 0 % 3 := by omega
  have hd : Drive (half w011 R φ) false true true t0 (102+q) := drive_half g _
  rw [e] at no
  have h := outside_011 (half_isR30 _ _ _) hd no
  have := ether_ends (w := w011) (j0 := 11) (φ := φ) (t1 := t0+153) (n := q) (k := 28) (aligned3_spec (w := w011) (j0 := 11) (s := 0) (by decide)) hR (by omega)
    (fun i hi => etherOn_of_code (g := 0) (by omega) (by decide) (h i hi))
  omega

/-- **Every right half beside `001`,** of any support and from any phase, enters the trap or has a constant gate. -/
theorem enters_or_constant_001 (R : Nat → Bool) (φ : Nat) : (∃ t, (t+φ) % 3 = 1 ∧ InTrap trap001 (half w001 R φ) t) ∨
    ∃ c, ∀ t, 26 ≤ t → (t+φ) % 3 = 1 → half w001 R φ t 1 = c := by
  by_cases out : ∃ t, (t+φ) % 3 = 1 ∧ InTrap trap001 (half w001 R φ) t
  · exact Or.inl out
  right
  obtain ⟨t0, small, g⟩ : ∃ t0, t0 < 3 ∧ (t0+φ) % 3 = 1 % 3 := ⟨(4-φ%3)%3, by omega, by omega⟩
  have at_ (q : Nat) := outside_001 (half_isR30 w001 R φ) (t := t0) (q := q) (drive_half g _)
    (fun h => out ⟨_, by omega, h⟩)
  have same (q : Nat) : half w001 R φ (t0+24+3*q) 1 = half w001 R φ (t0+24) 1 := by
    rcases at_ q with h | h
    · rw [cell_of_code (h q (Nat.le_refl _)) (j := 0) (by omega), cell_of_code (h 0 (by omega)) (j := 0) (by omega)]
    · rw [cell_of_code (h q (Nat.le_refl _)) (j := 0) (by omega), cell_of_code (h 0 (by omega)) (j := 0) (by omega)]
  refine ⟨half w001 R φ (t0+24) 1, fun t ht gt => ?_⟩
  have e : t = t0+24+3*((t-t0-24)/3) := by omega
  rw [e]
  exact same _

/-- **Every right half beside `011`** enters the trap or has a white gate from tick `155` on. -/
theorem enters_or_constant_011 (R : Nat → Bool) (φ : Nat) : (∃ t, (t+φ) % 3 = 0 ∧ InTrap trap011 (half w011 R φ) t) ∨
    ∀ t, 155 ≤ t → (t+φ) % 3 = 0 → half w011 R φ t 1 = false := by
  by_cases out : ∃ t, (t+φ) % 3 = 0 ∧ InTrap trap011 (half w011 R φ) t
  · exact Or.inl out
  right
  obtain ⟨t0, small, g⟩ : ∃ t0, t0 < 3 ∧ (t0+φ) % 3 = 0 % 3 := ⟨(3-φ%3)%3, by omega, by omega⟩
  intro t ht gt
  have h := outside_011 (half_isR30 w011 R φ) (t := t0) (q := (t-t0-153)/3) (drive_half g _) (fun h => out ⟨_, by omega, h⟩)
    ((t-t0-153)/3) (Nat.le_refl _)
  rw [show t0+153+3*((t-t0-153)/3) = t by omega] at h
  rw [cell_of_code h (j := 0) (by omega)]
  decide

/-! ### The trap is closed, and what it reads -/

theorem stays_001 {R : Nat → Bool} {φ t : Nat} (ht : (t+φ) % 3 = 1) (h : InTrap trap001 (half w001 R φ) t) (n : Nat) :
    InTrap trap001 (half w001 R φ) (t+3*n) :=
  trap_stays valid001 walk001 free001 wrap001 isTrap001 (half_isR30 _ _ _) (drive_half (g := 1) (by omega) n) h

theorem stays_011 {R : Nat → Bool} {φ t : Nat} (ht : (t+φ) % 3 = 0) (h : InTrap trap011 (half w011 R φ) t) (n : Nat) :
    InTrap trap011 (half w011 R φ) (t+3*n) :=
  trap_stays valid011 walk011 free011 wrap011 isTrap011 (half_isR30 _ _ _) (drive_half (g := 0) (by omega) n) h

/-- The gate from the tick `t`: column `1` once a period. -/
def gate (F : Nat → Nat → Bool) (t k : Nat) : Bool := F (t+3*k) 1

/-- The readings from `i` on spell `v`. -/
def Spells (u : Nat → Bool) (i : Nat) (v : List Bool) : Prop := ∀ k, k < v.length → u (i+k) = v.getD k false

theorem avoids {T : Tree} {white black : Nat} {d0 d1 d2 : Bool} {trap : List Nat} {F : Nat → Nat → Bool}
    (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true) (free : freeFrom white black 0 1 = true)
    (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true) (is : isTrap T trap = true) (hF : IsR30 F) {t : Nat}
    (hd : ∀ n, Drive F d0 d1 d2 t n) (h : InTrap trap F t) {o : Nat} {v : List (Option Bool)}
    (line : wordLine T white black o v = true) (pos : 0 < v.length) (i : Nat)
    (read : ∀ k, k < v.length → fits (v.getD k none) (gate F t (i+k)) = true) : False := by
  obtain ⟨x, fx, bx⟩ := trap_row va ok free wrap is hF (hd (i+v.length)) h
  refine bit_word va ok line pos (bx i) (fun k hk => ?_)
  rw [← rows_add, fx (i+k) (by omega) 0 (by omega)]
  exact read k hk

/-- The gate words the trap of `001` excludes. -/
def words001 : List (List Bool) := [[false, true, false], [true, false, true], [true, false, false, true],
  [true, true, true, true, true], [false, false, false, false, false, false],
  [false, false, false, false, true, true, true], [false, true, true, true, false, false, false, true],
  [true, true, true, false, false, false, false, false]]
/-- The gate words the trap of `011` excludes. -/
def words011 : List (List Bool) := [[false, false], [false, true, false], [false, true, true, true, false],
  [false, true, true, true, true, false]]

theorem listed001 : (words001.all fun v => lines001.any fun l => l.2 == v.map some) = true := by decide
theorem listed011 : (words011.all fun v => lines011.any fun l => l.2 == v.map some) = true := by decide

theorem avoids_listed {T : Tree} {white black : Nat} {d0 d1 d2 : Bool} {trap : List Nat} {F : Nat → Nat → Bool}
    {lines : List (Nat × List (Option Bool))} {words : List (List Bool)}
    (va : T.valid = true) (ok : walkAll T white black d0 d1 d2 = true) (free : freeFrom white black 0 1 = true)
    (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true) (is : isTrap T trap = true)
    (wl : (lines.all fun l => wordLine T white black l.1 l.2) = true)
    (listed : (words.all fun v => lines.any fun l => l.2 == v.map some) = true) (hF : IsR30 F) {t : Nat}
    (hd : ∀ n, Drive F d0 d1 d2 t n) (h : InTrap trap F t) {v : List Bool} (hv : v ∈ words) (pos : 0 < v.length) (i : Nat) :
    ¬ Spells (gate F t) i v := by
  intro sp
  obtain ⟨l, hl, e⟩ := List.any_eq_true.mp (List.all_eq_true.mp listed v hv)
  have line := List.all_eq_true.mp wl l hl
  rw [beq_iff_eq.mp e] at line
  refine avoids va ok free wrap is hF hd h line (by simpa using pos) i (fun k hk => ?_)
  rw [List.length_map] at hk
  rw [sp k hk]
  simp [List.getD, hk, fits]

theorem words001_pos : ∀ v ∈ words001, 0 < v.length := by decide
theorem words011_pos : ∀ v ∈ words011, 0 < v.length := by decide

/-- **The gate words of the trap of `001`:** none of the eight is ever read from a tick in the trap on. -/
theorem avoids_001 {R : Nat → Bool} {φ t : Nat} (ht : (t+φ) % 3 = 1) (h : InTrap trap001 (half w001 R φ) t) {v : List Bool}
    (hv : v ∈ words001) (i : Nat) : ¬ Spells (gate (half w001 R φ) t) i v :=
  avoids_listed valid001 walk001 free001 wrap001 isTrap001 wordLines001 listed001 (half_isR30 _ _ _)
    (drive_half (g := 1) (by omega)) h hv (words001_pos v hv) i

/-- **The gate words of the trap of `011`.** -/
theorem avoids_011 {R : Nat → Bool} {φ t : Nat} (ht : (t+φ) % 3 = 0) (h : InTrap trap011 (half w011 R φ) t) {v : List Bool}
    (hv : v ∈ words011) (i : Nat) : ¬ Spells (gate (half w011 R φ) t) i v :=
  avoids_listed valid011 walk011 free011 wrap011 isTrap011 wordLines011 listed011 (half_isR30 _ _ _)
    (drive_half (g := 0) (by omega)) h hv (words011_pos v hv) i

/-! ### The runs of the gate -/

theorem is_true {b : Bool} (h : b ≠ false) : b = true := by cases b; exact absurd rfl h; rfl
theorem is_false {b : Bool} (h : b ≠ true) : b = false := by cases b; rfl; exact absurd rfl h

/-- **The runs beside `001`.** After each change of colour, a run of two to four black readings or of three to five white. -/
theorem runs_001 {R : Nat → Bool} {φ t : Nat} (ht : (t+φ) % 3 = 1) (h : InTrap trap001 (half w001 R φ) t) (i : Nat)
    (change : gate (half w001 R φ) t (i+1) ≠ gate (half w001 R φ) t i) :
    ∃ r, (if gate (half w001 R φ) t (i+1) then 2 ≤ r ∧ r ≤ 4 else 3 ≤ r ∧ r ≤ 5) ∧
      (∀ k, k < r → gate (half w001 R φ) t (i+1+k) = gate (half w001 R φ) t (i+1)) ∧
      gate (half w001 R φ) t (i+1+r) ≠ gate (half w001 R φ) t (i+1) := by
  have no (v : List Bool) (hv : v ∈ words001) (j : Nat) := avoids_001 ht h hv j
  generalize gate (half w001 R φ) t = u at *
  have n010 := no [false, true, false] (by decide)
  have n101 := no [true, false, true] (by decide)
  have n1001 := no [true, false, false, true] (by decide)
  have n11111 := no [true, true, true, true, true] (by decide)
  have n000000 := no [false, false, false, false, false, false] (by decide)
  clear no
  have s3 (a b c : Bool) (j : Nat) : Spells u j [a, b, c] ↔ u j = a ∧ u (j+1) = b ∧ u (j+2) = c := by
    constructor
    · intro s; exact ⟨s 0 (by simp), s 1 (by simp), s 2 (by simp)⟩
    · rintro ⟨x, y, z⟩ k hk
      have : k = 0 ∨ k = 1 ∨ k = 2 := by simp at hk; omega
      rcases this with rfl | rfl | rfl <;> assumption
  have s4 (a b c d : Bool) (j : Nat) : Spells u j [a, b, c, d] ↔ u j = a ∧ u (j+1) = b ∧ u (j+2) = c ∧ u (j+3) = d := by
    constructor
    · intro s; exact ⟨s 0 (by simp), s 1 (by simp), s 2 (by simp), s 3 (by simp)⟩
    · rintro ⟨x, y, z, w⟩ k hk
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by simp at hk; omega
      rcases this with rfl | rfl | rfl | rfl <;> assumption
  have s5 (a b c d e : Bool) (j : Nat) : Spells u j [a, b, c, d, e] ↔
      u j = a ∧ u (j+1) = b ∧ u (j+2) = c ∧ u (j+3) = d ∧ u (j+4) = e := by
    constructor
    · intro s; exact ⟨s 0 (by simp), s 1 (by simp), s 2 (by simp), s 3 (by simp), s 4 (by simp)⟩
    · rintro ⟨x, y, z, w, v⟩ k hk
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by simp at hk; omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> assumption
  have s6 (a b c d e f : Bool) (j : Nat) : Spells u j [a, b, c, d, e, f] ↔
      u j = a ∧ u (j+1) = b ∧ u (j+2) = c ∧ u (j+3) = d ∧ u (j+4) = e ∧ u (j+5) = f := by
    constructor
    · intro s; exact ⟨s 0 (by simp), s 1 (by simp), s 2 (by simp), s 3 (by simp), s 4 (by simp), s 5 (by simp)⟩
    · rintro ⟨x, y, z, w, v, q⟩ k hk
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by simp at hk; omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have a := n010 i
  have b := n101 i
  have c := n1001 i
  have d := n11111 (i+1)
  have e := n000000 (i+1)
  rw [s3] at a b
  rw [s4] at c
  rw [s5] at d
  rw [s6] at e
  simp only [Nat.add_assoc] at a b c d e ⊢
  have least (n : Nat) (hn : u (i+(1+n)) ≠ u (i+1)) : ∃ r, u (i+(1+r)) ≠ u (i+1) ∧ ∀ q, q < r → u (i+(1+q)) = u (i+1) := by
    obtain ⟨r, hr, m⟩ := exists_least (P := fun r => u (i+(1+r)) ≠ u (i+1)) n hn
    exact ⟨r, hr, fun q hq => Classical.not_not.mp (m q hq)⟩
  cases hc : u (i+1)
  · have hi : u i = true := by rw [hc] at change; exact is_true (Ne.symm change)
    have far : ∃ n, n ≤ 5 ∧ u (i+(1+n)) ≠ u (i+1) := by
      apply Classical.byContradiction
      intro nothing
      have w (n : Nat) (hn : n ≤ 5) : u (i+(1+n)) = false := by
        rw [← hc]; exact Classical.not_not.mp fun q => nothing ⟨n, hn, q⟩
      exact e ⟨hc, w 1 (by omega), w 2 (by omega), w 3 (by omega), w 4 (by omega), w 5 (by omega)⟩
    obtain ⟨n, hn, ne⟩ := far
    obtain ⟨r, hr, before⟩ := least n ne
    have le : r ≤ n := Nat.le_of_not_lt fun q => ne (before n q)
    refine ⟨r, ?_, fun k hk => ?_, ?_⟩
    · simp only [Bool.false_eq_true, ite_false]
      refine ⟨Nat.le_of_not_lt fun q => ?_, by omega⟩
      have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases this with rfl | rfl | rfl
      · exact hr rfl
      · rw [hc] at hr; exact b ⟨hi, hc, is_true hr⟩
      · rw [hc] at hr; exact c ⟨hi, hc, by rw [before 1 (by omega), hc], is_true hr⟩
    · rw [← hc]; exact before k hk
    · rw [← hc]; exact hr
  · have hi : u i = false := by rw [hc] at change; exact is_false (Ne.symm change)
    have far : ∃ n, n ≤ 4 ∧ u (i+(1+n)) ≠ u (i+1) := by
      apply Classical.byContradiction
      intro nothing
      have w (n : Nat) (hn : n ≤ 4) : u (i+(1+n)) = true := by
        rw [← hc]; exact Classical.not_not.mp fun q => nothing ⟨n, hn, q⟩
      exact d ⟨hc, w 1 (by omega), w 2 (by omega), w 3 (by omega), w 4 (by omega)⟩
    obtain ⟨n, hn, ne⟩ := far
    obtain ⟨r, hr, before⟩ := least n ne
    have le : r ≤ n := Nat.le_of_not_lt fun q => ne (before n q)
    refine ⟨r, ?_, fun k hk => ?_, ?_⟩
    · simp only [ite_true]
      refine ⟨Nat.le_of_not_lt fun q => ?_, by omega⟩
      have : r = 0 ∨ r = 1 := by omega
      rcases this with rfl | rfl
      · exact hr rfl
      · rw [hc] at hr; exact a ⟨hi, hc, is_false hr⟩
    · rw [← hc]; exact before k hk
    · rw [← hc]; exact hr

/-- At least six gate steps from the starting sample, no white reading is followed by seventeen black ones. -/
theorem long_011 {R : Nat → Bool} {φ t : Nat} (ht : (t+φ) % 3 = 0) (h : InTrap trap011 (half w011 R φ) t) (i : Nat)
    (hi : 6 ≤ i) (white : gate (half w011 R φ) t i = false) : ∃ g, 1 ≤ g ∧ g ≤ 17 ∧ gate (half w011 R φ) t (i+g) = false := by
  apply Classical.byContradiction
  intro nothing
  have black (g : Nat) (h1 : 1 ≤ g) (h2 : g ≤ 17) : gate (half w011 R φ) t (i+g) = true := by
    cases e : gate (half w011 R φ) t (i+g)
    · exact absurd ⟨g, h1, h2, e⟩ nothing
    · rfl
  have line := List.all_eq_true.mp wordLines011 _ (show lines011.getLast (by decide) ∈ lines011 from List.getLast_mem _)
  refine avoids valid011 walk011 free011 wrap011 isTrap011 (half_isR30 _ _ _) (drive_half (g := 0) (by omega)) h line
    (by decide) (i-6) (fun k hk => ?_)
  have len : (lines011.getLast (by decide)).2.length = 24 := by decide
  rw [len] at hk
  have table : ∀ k : Fin 24, (lines011.getLast (by decide)).2.getD k.val none =
      (if k.val < 6 then none else some (decide (6 < k.val))) := by decide
  rw [table ⟨k, hk⟩]
  by_cases k6 : k < 6
  · simp [k6, fits]
  · simp only [k6, ite_false, fits]
    rcases (by omega : k = 6 ∨ 6 < k) with rfl | k7
    · rw [show i-6+6 = i by omega, white]; rfl
    · rw [show i-6+k = i+(k-6) by omega, black (k-6) (by omega) (by omega), decide_eq_true k7]; rfl

/-- **The gaps beside `011`.** After a white reading at least six gate steps from the starting sample (index 0), the next white
reading comes three, or six to seventeen, steps later, and those between are black. -/
theorem gaps_011 {R : Nat → Bool} {φ t : Nat} (ht : (t+φ) % 3 = 0) (h : InTrap trap011 (half w011 R φ) t) (i : Nat)
    (hi : 6 ≤ i) (white : gate (half w011 R φ) t i = false) : ∃ g, (g = 3 ∨ 6 ≤ g ∧ g ≤ 17) ∧
      gate (half w011 R φ) t (i+g) = false ∧ ∀ k, 0 < k → k < g → gate (half w011 R φ) t (i+k) = true := by
  obtain ⟨g0, lo, hi17, w0⟩ := long_011 ht h i hi white
  have no (v : List Bool) (hv : v ∈ words011) (j : Nat) := avoids_011 ht h hv j
  generalize gate (half w011 R φ) t = u at *
  obtain ⟨g, ⟨g1, wg⟩, least⟩ := exists_least (P := fun g => 1 ≤ g ∧ u (i+g) = false) g0 ⟨lo, w0⟩
  have le : g ≤ g0 := Nat.le_of_not_lt fun q => least g0 q ⟨lo, w0⟩
  have black (k : Nat) (h0 : 0 < k) (hk : k < g) : u (i+k) = true := by
    cases e : u (i+k)
    · exact absurd ⟨h0, e⟩ (least k hk)
    · rfl
  refine ⟨g, ?_, wg, black⟩
  apply Classical.byContradiction
  intro bad
  have : g = 1 ∨ g = 2 ∨ g = 4 ∨ g = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · refine no [false, false] (by decide) i (fun k hk => ?_)
    have : k = 0 ∨ k = 1 := by simp at hk; omega
    rcases this with rfl | rfl
    · exact white
    · exact wg
  · refine no [false, true, false] (by decide) i (fun k hk => ?_)
    have : k = 0 ∨ k = 1 ∨ k = 2 := by simp at hk; omega
    rcases this with rfl | rfl | rfl
    · exact white
    · exact black 1 (by omega) (by omega)
    · exact wg
  · refine no [false, true, true, true, false] (by decide) i (fun k hk => ?_)
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by simp at hk; omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact white
    · exact black 1 (by omega) (by omega)
    · exact black 2 (by omega) (by omega)
    · exact black 3 (by omega) (by omega)
    · exact wg
  · refine no [false, true, true, true, true, false] (by decide) i (fun k hk => ?_)
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by simp at hk; omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact white
    · exact black 1 (by omega) (by omega)
    · exact black 2 (by omega) (by omega)
    · exact black 3 (by omega) (by omega)
    · exact black 4 (by omega) (by omega)
    · exact wg

/-! ### The single cell -/

/-- A driven half and an evolution that share a row and a drive agree for as long as the drive does. -/
theorem agree {F : Nat → Nat → Bool} (hF : IsR30 F) {c : Nat → Bool} {T N : Nat} (clock : ∀ j, j < N → F (T+j) 0 = c j) :
    ∀ j, j ≤ N → ∀ p, F (T+j) (p+1) = drv c (fun p => F T p) j (p+1) := by
  intro j
  induction j with
  | zero => intro _ p; rw [drv_init _ _ _ (by omega), Nat.add_zero]
  | succ j ih =>
    intro hj p
    rw [← Nat.add_assoc, hF (T+j) p, drv_isR30 c _ j p, ih (by omega) p, ih (by omega) (p+1)]
    congr 1
    cases p with
    | zero => rw [drv_col0]; exact clock j (by omega)
    | succ p => exact ih (by omega) p

theorem trap_congr {trap : List Nat} {F G : Nat → Nat → Bool} {t s : Nat} (h : ∀ p, F t (p+1) = G s (p+1))
    (hG : InTrap trap G s) : InTrap trap F t := by
  unfold InTrap code at *
  rw [Rule30Ether.seg_congr 14 (fun j => F t (j+1)) (fun j => G s (j+1)) (fun i _ => h i)]
  exact hG

/-- **The single cell beside `001`.** If the centre follows `001` from age `T` for `N ≥ 3 T + 170` ticks, the fourteen cells
to its right are in the trap at age `T + N`, a gate tick. -/
theorem centre_001 {T N : Nat} (clock : ∀ j, j < N → cell (T+j) 0 = wordAt3 w001 j) (hN : N % 3 = 1) (late : 3*T+170 ≤ N) :
    InTrap trap001 trueRight (T+N) := by
  have fin : ∀ p, T < p → trueRight T p = false := fun p hp => Rule30Diagonals.cell_eq_false_of_gt T p (by omega)
  refine trap_congr (fun p => ?_) (finite_enters_001 fin (φ := 0) (t := N) (by omega) late)
  exact agree trueRight_isR30 (c := fun t => wordAt3 w001 (t+0)) clock N (Nat.le_refl _) p

/-- **The single cell beside `011`.** -/
theorem centre_011 {T N : Nat} (clock : ∀ j, j < N → cell (T+j) 0 = wordAt3 w011 j) (hN : N % 3 = 0) (late : 3*T+820 ≤ N) :
    InTrap trap011 trueRight (T+N) := by
  have fin : ∀ p, T < p → trueRight T p = false := fun p hp => Rule30Diagonals.cell_eq_false_of_gt T p (by omega)
  refine trap_congr (fun p => ?_) (finite_enters_011 fin (φ := 0) (t := N) (by omega) late)
  exact agree trueRight_isR30 (c := fun t => wordAt3 w011 (t+0)) clock N (Nat.le_refl _) p

/-! ### The trap is the least nonempty closed set -/

/-- A set of windows of fourteen cells that one period of a driven half keeps, from any gate tick and whatever lies beyond. -/
def Closed (w : List Bool) (g : Nat) (C : Nat → Prop) : Prop := ∀ (R : Nat → Bool) (φ t : Nat), (t+φ) % 3 = g →
  C (code (half w R φ) t 14) → C (code (half w R φ) (t+3) 14)

theorem closed_001 : Closed w001 1 (· ∈ trap001) := fun _ _ _ ht h => stays_001 ht h 1
theorem closed_011 : Closed w011 0 (· ∈ trap011) := fun _ _ _ ht h => stays_011 ht h 1

theorem code_row (w : List Bool) (x φ L : Nat) : Fits (half w (fun p => x.testBit (p-1)) φ) 0 x L := by
  intro j _
  rw [half, drv_init _ _ _ (by omega), Nat.add_sub_cancel]

/-- In a closed set, the eight windows that follow a window. -/
theorem closed_image {w : List Bool} {g : Nat} {C : Nat → Prop} (h : Closed w g C) (hg : g < 3) {x : Nat} (hx : x < 2^14)
    (c : C x) (e : Nat) : C (per (wordAt3 w g) (wordAt3 w (g+1)) (wordAt3 w (g+2)) (x+2^14*e) % 2^14) := by
  have f := code_row w (x+2^14*e) g 17
  have a := code_of_fits f (n := 14) (by omega)
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx] at a
  obtain ⟨h0, h1, h2⟩ := drive_half (w := w) (R := fun p => (x+2^14*e).testBit (p-1)) (φ := g) (t := 0) (g := g) (by omega) 1 0
    (by omega)
  have b := code_of_fits (fits_per (half_isR30 _ _ _) h0 h1 h2 (L := 14) f) (Nat.le_refl 14)
  rw [b]
  refine h _ g 0 (by omega) ?_
  rw [← a]
  exact c

theorem bit_or {s y v : Nat} (h : (s ||| (1 <<< y)).testBit v = true) : s.testBit v = true ∨ v = y := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  exact h.imp id Eq.symm

section
variable {w : List Bool} {g : Nat} {C : Nat → Prop}

theorem tour_end (h : Closed w g C) (hg : g < 3) : ∀ (k l x seen r full : Nat),
    tour (wordAt3 w g) (wordAt3 w (g+1)) (wordAt3 w (g+2)) k l x seen r full = true → x < 2^14 → C x → C r
  | 0, _, x, seen, r, full, ok, _, c => by
    simp only [tour, Bool.and_eq_true, beq_iff_eq] at ok
    rw [← ok.1]; exact c
  | k+1, l, x, seen, r, full, ok, hx, c => by
    simp only [tour, Bool.and_eq_true] at ok
    exact tour_end h hg k (l/8) _ _ r full ok.2.2 (Nat.mod_lt _ (by decide)) (closed_image h hg hx c (l % 8))

theorem tour_all (h : Closed w g C) (hg : g < 3) : ∀ (k l x seen r full : Nat),
    tour (wordAt3 w g) (wordAt3 w (g+1)) (wordAt3 w (g+2)) k l x seen r full = true → x < 2^14 → C x →
      ∀ v, full.testBit v = true → seen.testBit v = true ∨ C v
  | 0, _, x, seen, r, full, ok, _, _, v, hv => by
    simp only [tour, Bool.and_eq_true, beq_iff_eq] at ok
    rw [ok.2]; exact Or.inl hv
  | k+1, l, x, seen, r, full, ok, hx, c, v, hv => by
    simp only [tour, Bool.and_eq_true] at ok
    have y := closed_image h hg hx c (l % 8)
    rcases tour_all h hg k (l/8) _ _ r full ok.2.2 (Nat.mod_lt _ (by decide)) y v hv with b | b
    · rcases bit_or b with b | b
      · exact Or.inl b
      · rw [b]; exact Or.inr y
    · exact Or.inr b

/-- From every window the walk meets it goes on to its end. -/
theorem tour_home (h : Closed w g C) (hg : g < 3) : ∀ (k l x seen r full : Nat),
    tour (wordAt3 w g) (wordAt3 w (g+1)) (wordAt3 w (g+2)) k l x seen r full = true →
      ∀ v, full.testBit v = true → C v → seen.testBit v = true ∨ C r
  | 0, _, x, seen, r, full, ok, v, hv, _ => by
    simp only [tour, Bool.and_eq_true, beq_iff_eq] at ok
    rw [ok.2]; exact Or.inl hv
  | k+1, l, x, seen, r, full, ok, v, hv, c => by
    simp only [tour, Bool.and_eq_true] at ok
    rcases tour_home h hg k (l/8) _ _ r full ok.2.2 v hv c with b | b
    · rcases bit_or b with b | b
      · exact Or.inl b
      · rw [b] at c
        exact Or.inr (tour_end h hg k (l/8) _ _ r full ok.2.2 (Nat.mod_lt _ (by decide)) c)
    · exact Or.inr b

end

theorem bitset_fold : ∀ (L : List Nat) (s v : Nat), (s.testBit v = true ∨ v ∈ L) →
    (L.foldl (fun s x => s ||| (1 <<< x)) s).testBit v = true
  | [], s, v, h => by simpa using h
  | a :: L, s, v, h => by
    refine bitset_fold L _ v ?_
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [List.mem_cons] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr h

theorem bitset_mem {L : List Nat} {v : Nat} (h : v ∈ L) : (bitset L).testBit v = true := bitset_fold L 0 v (Or.inr h)

/-- A closed set with one window of the trap has them all. -/
theorem whole_trap {w : List Bool} {g : Nat} {C : Nat → Prop} {trap : List Nat} {k l r : Nat}
    (ok : tour (wordAt3 w g) (wordAt3 w (g+1)) (wordAt3 w (g+2)) k l r 0 r (bitset trap) = true) (hr : r < 2^14)
    (h : Closed w g C) (hg : g < 3) {x : Nat} (hx : x ∈ trap) (c : C x) : ∀ y ∈ trap, C y := by
  intro y hy
  have home : C r := by
    rcases tour_home h hg k l r 0 r _ ok x (bitset_mem hx) c with b | b
    · simp at b
    · exact b
  rcases tour_all h hg k l r 0 r _ ok hr home y (bitset_mem hy) with b | b
  · simp at b
  · exact b

theorem closed_stays {w : List Bool} {g : Nat} {C : Nat → Prop} (h : Closed w g C) (R : Nat → Bool) {φ t : Nat}
    (ht : (t+φ) % 3 = g) (c : C (code (half w R φ) t 14)) : ∀ n, C (code (half w R φ) (t+3*n) 14)
  | 0 => c
  | n+1 => h R φ (t+3*n) (by omega) (closed_stays h R ht c n)

/-- **The trap of `001` is the least nonempty closed set:** every closed set that holds any window of fourteen cells holds all of it. -/
theorem least_001 {C : Nat → Prop} (h : Closed w001 1 C) {x : Nat} (hx : x < 2^14) (c : C x) : ∀ y ∈ trap001, C y := by
  have fin : ∀ p, 14 < p → (fun p => x.testBit (p-1)) p = false := fun p hp => by
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
  have start : code (half w001 (fun p => x.testBit (p-1)) 1) 0 14 = x := by
    rw [← code_of_fits (code_row w001 x 1 14) (Nat.le_refl 14), Nat.mod_eq_of_lt hx]
  have inT := finite_enters_001 fin (φ := 1) (t := 0+3*100) (by decide) (by omega)
  have cT := closed_stays h (fun p => x.testBit (p-1)) (φ := 1) (t := 0) (by decide) (by rw [start]; exact c) 100
  exact whole_trap tour001 (by decide) h (by decide) inT cT

/-- **The trap of `011` is the least nonempty closed set.** -/
theorem least_011 {C : Nat → Prop} (h : Closed w011 0 C) {x : Nat} (hx : x < 2^14) (c : C x) : ∀ y ∈ trap011, C y := by
  have fin : ∀ p, 14 < p → (fun p => x.testBit (p-1)) p = false := fun p hp => by
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
  have start : code (half w011 (fun p => x.testBit (p-1)) 0) 0 14 = x := by
    rw [← code_of_fits (code_row w011 x 0 14) (Nat.le_refl 14), Nat.mod_eq_of_lt hx]
  have inT := finite_enters_011 fin (φ := 0) (t := 0+3*300) (by decide) (by omega)
  have cT := closed_stays h (fun p => x.testBit (p-1)) (φ := 0) (t := 0) (by decide) (by rw [start]; exact c) 300
  exact whole_trap tour011 (by decide) h (by decide) inT cT

/-! ### No slope below five halves -/

/-- A finite row with its first ether defect at `D`. -/
def cut (j φ D p : Nat) : Bool :=
  if p < D then eth j φ p 0 else if p = D then !eth j φ p 0 else false

theorem cut_finite (j φ D : Nat) {p : Nat} (hp : D < p) : cut j φ D p = false := by
  simp [cut, show ¬p < D by omega, show p ≠ D by omega]

theorem travel {F : Nat → Nat → Bool} (hF : IsR30 F) {j φ : Nat} (clock : ∀ t, F t 0 = eth j φ 0 t) (k c t : Nat) (hc : 7 ≤ c)
    (front : Front F j φ t (4*k+c)) (hrec : IsRec F j φ t (4*k+c)) : Front F j φ (t+10*k) c := by
  induction k generalizing t with
  | zero => simpa using front
  | succ k ih =>
    obtain ⟨next, nextRec, _⟩ := ten_ticks hF (fun u _ => clock u) front hrec (by omega)
    rw [show 4*(k+1)+c-4 = 4*k+c by omega] at next nextRec
    simpa only [show t+10*(k+1) = t+10+10*k by omega] using ih (t+10) next nextRec

theorem outside_at (w : List Bool) (trap : List Nat) (j φ c n : Nat) (aligned : aligned3 w j 0 = true) (hc : 14 < c)
    (state : (j+c+4*φ)%12 = 0) (outside : code (fun _ p => ether3 (j+p) φ) 0 14 ∉ trap) :
    ¬ InTrap trap (half w (cut j φ (12*n+c)) φ) (30*n) := by
  let D := 12*n+c
  let F := half w (cut j φ D) φ
  have clock (t : Nat) : F t 0 = eth j φ 0 t := by
    rw [show F t 0 = wordAt3 w (t+φ) from half_zero ..]
    simpa [eth] using (aligned3_spec aligned (t+φ)).symm
  have initial (p : Nat) (hp : 1 ≤ p) : F 0 p = cut j φ D p := drv_init _ _ _ hp
  have first : Front F j φ 0 D := by
    constructor
    · intro p hp
      by_cases z : p = 0
      · subst p; exact clock 0
      · rw [initial p (by omega)]; simp [cut, hp]
    · rw [initial D (by dsimp [D]; omega)]
      simp [cut]
  have state' : cls j φ D 0 = 0 := by unfold cls; dsimp [D]; omega
  have hrec : IsRec F j φ 0 D := by
    unfold IsRec; rw [state']; cases ubit F j φ 0 D <;> decide
  have dEq : D = 4*(3*n)+c := by dsimp [D]; omega
  rw [dEq] at first hrec
  have late := travel (half_isR30 w (cut j φ D) φ) clock (3*n) c 0 (by omega) first hrec
  rw [show 0+10*(3*n) = 30*n by omega] at late
  have same : code F (30*n) 14 = code (fun _ p => ether3 (j+p) φ) 0 14 := by
    unfold code; congr 1
    apply Rule30Ether.seg_congr
    intro i hi
    exact (late.1 (i+1) (by omega)).trans (ether3_congr rfl (by omega))
  change code F (30*n) 14 ∉ trap
  rwa [same]

/-- At gate tick `30 n` a half that is white beyond `12 n + 20` can still be outside the trap of `001`. -/
theorem slow_001 (n : Nat) : ¬ InTrap trap001 (half w001 (cut 0 1 (12*n+20)) 1) (30*n) :=
  outside_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide +kernel)

/-- At gate tick `30 n` a half that is white beyond `12 n + 25` can still be outside the trap of `011`. -/
theorem slow_011 (n : Nat) : ¬ InTrap trap011 (half w011 (cut 11 0 (12*n+25)) 0) (30*n) :=
  outside_at _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide +kernel)

theorem slope_arith {p q r c : Nat} (h : 2*p < 5*q) : p*(12*(c*p+r)+c) + r ≤ q*(30*(c*p+r)) := by
  have a : (2*p+1)*(6*(c*p+r)) ≤ (5*q)*(6*(c*p+r)) := Nat.mul_le_mul_right _ h
  have e1 : (5*q)*(6*(c*p+r)) = q*(30*(c*p+r)) := by
    rw [Nat.mul_comm 5 q, Nat.mul_assoc, ← Nat.mul_assoc 5 6]
  have e2 : (2*p+1)*(6*(c*p+r)) = p*(12*(c*p+r)) + 6*(c*p+r) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm 2 p, Nat.mul_assoc, ← Nat.mul_assoc 2 6]
  rw [e1, e2] at a
  rw [Nat.mul_add]
  have e3 : p*c = c*p := Nat.mul_comm ..
  omega

/-- **The slope beside `001`.** If every half white beyond `D` is in the trap at every gate tick `t` with `p D + r ≤ q t`, then
`p/q` is at least `5/2`. -/
theorem slope_001 {p q r : Nat} (h : ∀ (R : Nat → Bool) (D : Nat), (∀ x, D < x → R x = false) → ∀ φ t, (t+φ) % 3 = 1 →
    p*D+r ≤ q*t → InTrap trap001 (half w001 R φ) t) : 5*q ≤ 2*p := by
  refine Nat.le_of_not_lt fun lt => slow_001 (20*p+r) ?_
  exact h _ _ (fun x hx => cut_finite 0 1 _ hx) 1 _ (by omega) (slope_arith lt)

/-- **The slope beside `011`.** -/
theorem slope_011 {p q r : Nat} (h : ∀ (R : Nat → Bool) (D : Nat), (∀ x, D < x → R x = false) → ∀ φ t, (t+φ) % 3 = 0 →
    p*D+r ≤ q*t → InTrap trap011 (half w011 R φ) t) : 5*q ≤ 2*p := by
  refine Nat.le_of_not_lt fun lt => slow_011 (25*p+r) ?_
  exact h _ _ (fun x hx => cut_finite 11 0 _ hx) 0 _ (by omega) (slope_arith lt)

/-! ### What is left of period three: the left half

`C3s001` and `C3w w011` (`Rule30EtherThreeSkeleton`, `Rule30EtherThreeLeft`) ask that no finite left half keep column `-1` on a
pattern with one free cell a period. Beside an eventual period three that free cell is the complement of the gate, and the
gate of a right half in the trap avoids `words001` or `words011`. -/

open Rule30DrivenLeft Rule30Diagonals

/-- `u` spells no word of the list from `K` on, read once in three ticks from phase `g`. -/
def Free (words : List (List Bool)) (g : Nat) (u : Nat → Bool) (K : Nat) : Prop :=
  ∀ k, K ≤ k → k % 3 = g → ∀ v ∈ words, ¬ ∀ i, i < v.length → u (k+3*i) = !v.getD i false

/-- The gate of the single cell beside an eventual `001`. -/
theorem centre_free_001 {T : Nat} (h : ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t-T)) {t : Nat} (late : 4*T+172 ≤ t)
    (ht : (t-T) % 3 = 1) {v : List Bool} (hv : v ∈ words001) : ¬ ∀ i, i < v.length → cell (t+3*i) 1 = v.getD i false := by
  intro sp
  have clock : ∀ n j, j < n → cell (T+j) 0 = wordAt3 w001 j := fun n j _ => by rw [h (T+j) (by omega)]; congr 1; omega
  have fin : ∀ p, T < p → trueRight T p = false := fun p hp => cell_eq_false_of_gt T p (by omega)
  have inT := finite_enters_001 fin (φ := 0) (t := t-T) (by omega) (by omega)
  refine avoids_001 (φ := 0) (by omega) inT hv 0 (fun i hi => ?_)
  have e := agree trueRight_isR30 (c := fun t => wordAt3 w001 (t+0)) (T := T) (N := t-T+3*i) (clock _) (t-T+3*i) (Nat.le_refl _) 0
  rw [← sp i hi]
  show half w001 (fun p => trueRight T p) 0 (t-T+3*(0+i)) 1 = cell (t+3*i) 1
  rw [show t-T+3*(0+i) = t-T+3*i by omega]
  refine e.symm.trans ?_
  show cell (T+(t-T+3*i)) ((0+1 : Nat) : Int) = cell (t+3*i) 1
  rw [show T+(t-T+3*i) = t+3*i by omega]
  rfl

/-- The gate of the single cell beside an eventual `011`. -/
theorem centre_free_011 {T : Nat} (h : ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t-T)) {t : Nat} (late : 4*T+822 ≤ t)
    (ht : (t-T) % 3 = 0) {v : List Bool} (hv : v ∈ words011) : ¬ ∀ i, i < v.length → cell (t+3*i) 1 = v.getD i false := by
  intro sp
  have clock : ∀ n j, j < n → cell (T+j) 0 = wordAt3 w011 j := fun n j _ => by rw [h (T+j) (by omega)]; congr 1; omega
  have fin : ∀ p, T < p → trueRight T p = false := fun p hp => cell_eq_false_of_gt T p (by omega)
  have inT := finite_enters_011 fin (φ := 0) (t := t-T) (by omega) (by omega)
  refine avoids_011 (φ := 0) (by omega) inT hv 0 (fun i hi => ?_)
  have e := agree trueRight_isR30 (c := fun t => wordAt3 w011 (t+0)) (T := T) (N := t-T+3*i) (clock _) (t-T+3*i) (Nat.le_refl _) 0
  rw [← sp i hi]
  show half w011 (fun p => trueRight T p) 0 (t-T+3*(0+i)) 1 = cell (t+3*i) 1
  rw [show t-T+3*(0+i) = t-T+3*i by omega]
  refine e.symm.trans ?_
  show cell (T+(t-T+3*i)) ((0+1 : Nat) : Int) = cell (t+3*i) 1
  rw [show T+(t-T+3*i) = t+3*i by omega]
  rfl

/-- **The left half for `001`** (open): no finite left half keeps column `-1` on `(0, *, 1)` with free-phase readings that avoid
the complements of `words001`. -/
def Left001 : Prop := ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false) →
  ¬ ∃ K, (∀ k, K ≤ k → fits3 colPattern001s (k % 3) (L (fun _ => false) s k (-1)) = true) ∧
    Free words001 1 (fun k => L (fun _ => false) s k (-1)) K

/-- **The left half for `011`** (open): no finite left half keeps column `-1` on `(*, 0, 1)` with free-phase readings that avoid
the complements of `words011`. -/
def Left011 : Prop := ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false) →
  ¬ ∃ K, (∀ k, K ≤ k → fits3 (colPattern3 w011) (k % 3) (L (fun k => wordAt3 (effWord3 w011) k) s k (-1)) = true) ∧
    Free words011 0 (fun k => L (fun k => wordAt3 (effWord3 w011) k) s k (-1)) K

theorem left001_of_C3s (h : C3s001) : Left001 := fun s hs ⟨K, hK, _⟩ => h s hs ⟨K, hK⟩
theorem left011_of_C3w (h : C3w w011) : Left011 := fun s hs ⟨K, hK, _⟩ => h s hs ⟨K, hK⟩

/-- **`Left001` excludes `001`** as an eventual tail of the centre column. -/
theorem not_eventually_001_of_left (hC : Left001) : ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t-T) := by
  rintro ⟨T, hT⟩
  obtain ⟨T', hT', hs⟩ := col_m1_001_skeleton T hT
  have hfun : (fun k => Rule30Prize.center (T+k) && Rule30Prize.center (T+k+1)) = fun _ => false := by
    funext k
    show (cell (T+k) 0 && cell (T+k+1) 0) = false
    rw [hT (T+k) (by omega), hT (T+k+1) (by omega), wordAt3_001, wordAt3_001, show T+k-T = k by omega,
      show T+k+1-T = k+1 by omega]
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [h, show (k+1) % 3 = 1 by omega]; rfl
    · rw [h, show (k+1) % 3 = 2 by omega]; rfl
    · rw [h, show (k+1) % 3 = 0 by omega]; rfl
  have hL : ∀ k, L (fun _ => false) (fun p => cell T p) k (-1) = cell (T+k) (-1) := by
    intro k
    have e := cell_eq_L_effective T k (-1) (by omega)
    rw [hfun] at e
    exact e
  refine hC (fun p => cell T p) ⟨T, fun p hp => cell_eq_false_of_lt T p hp⟩ ⟨(T'-T)+(3*T+172), fun k hk => ?_, ?_⟩
  · rw [hL k, fits3_001s]
    obtain ⟨s0, -, s2⟩ := hs (T+k) (by omega)
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [ite_eq_left h, s0 (by omega)]; rfl
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_left h, s2 (by omega)]; rfl
  · intro k hk hk1 v hv sp
    refine centre_free_001 hT (t := T+k) (by omega) (by omega) hv (fun i hi => ?_)
    have e := (hL (k+3*i)).symm.trans (sp i hi)
    have m := (hs (T+(k+3*i)) (by omega)).2.1 (by omega)
    rw [m] at e
    rw [show T+k+3*i = T+(k+3*i) by omega]
    simpa using e

/-- **`Left011` excludes `011`** as an eventual tail of the centre column. -/
theorem not_eventually_011_of_left (hC : Left011) : ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t-T) := by
  rintro ⟨T, hT⟩
  have hdrv : (fun k => Rule30Prize.center (T+k) && Rule30Prize.center (T+k+1)) = fun k => wordAt3 (effWord3 w011) k := by
    funext k
    rw [wordAt3_effWord3]
    show (cell (T+k) 0 && cell (T+k+1) 0) = _
    rw [hT (T+k) (by omega), hT (T+k+1) (by omega), show T+k-T = k by omega, show T+k+1-T = k+1 by omega]
  have hL : ∀ k, L (fun k => wordAt3 (effWord3 w011) k) (fun p => cell T p) k (-1) = cell (T+k) (-1) := by
    intro k
    have e := cell_eq_L_effective T k (-1) (by omega)
    rw [hdrv] at e
    exact e
  refine hC (fun p => cell T p) ⟨T, fun p hp => cell_eq_false_of_lt T p hp⟩ ⟨3*T+822, fun k hk => ?_, ?_⟩
  · rw [hL k, fits3_011]
    obtain ⟨-, s1, s2⟩ := col_m1_011 T hT (T+k) (by omega)
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_left h, s1 (by omega)]; rfl
    · rw [ite_eq_right (by omega), ite_eq_left h, s2 (by omega)]; rfl
  · intro k hk hk0 v hv sp
    refine centre_free_011 hT (t := T+k) (by omega) (by omega) hv (fun i hi => ?_)
    have e := (hL (k+3*i)).symm.trans (sp i hi)
    have m := (col_m1_011 T hT (T+(k+3*i)) (by omega)).1 (by omega)
    rw [m] at e
    rw [show T+k+3*i = T+(k+3*i) by omega]
    simpa using e

/-- **No eventual period three** follows from the two statements about finite left halves. -/
theorem no_eventual_period_three_of_left (h001 : Left001) (h011 : Left011) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t+3) = Rule30Prize.center t := by
  rintro ⟨T0, hT0⟩
  rcases normalize_period_three hT0 with ⟨T, -, h1⟩ | ⟨T, -, h2⟩
  · exact not_eventually_001_of_left h001 ⟨T, h1⟩
  · exact not_eventually_011_of_left h011 ⟨T, h2⟩

/-! ### The kit's restricted left statements -/

/-- Every word of the second list holds one of the first as a factor. -/
def covers (small large : List (List Bool)) : Bool :=
  large.all fun p => small.any fun v => (List.range (p.length+1)).any fun j =>
    decide (j+v.length ≤ p.length) && (List.range v.length).all fun i => v.getD i false == p.getD (j+i) false

theorem free_of_cover {small large : List (List Bool)} (h : covers small large = true) {g K : Nat} {u : Nat → Bool}
    (free : Free small g u K) : Free large g u K := by
  intro k hk phase p hp spells
  obtain ⟨v, hv, offsets⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
  obtain ⟨j, _, hit⟩ := List.any_eq_true.mp offsets
  obtain ⟨bound, cells⟩ := Bool.and_eq_true_iff.mp hit
  have bound' := of_decide_eq_true bound
  apply free (k+3*j) (by omega) (by omega) v hv
  intro i hi
  have eq := beq_iff_eq.mp (List.all_eq_true.mp cells i (List.mem_range.mpr hi))
  rw [show k+3*j+3*i = k+3*(j+i) by omega, spells (j+i) (by omega), eq]

/-- `Left001` follows from `Rule30PeriodThreeLanguage.C3g001`. -/
theorem left001_of_C3g (h : Rule30PeriodThreeLanguage.C3g001) : Left001 := by
  rintro s hs ⟨K, pat, free⟩
  have old := free_of_cover (large := Rule30PeriodThreeLanguage.col1Forbidden001) (by decide) free
  exact h s hs ⟨K, fun k hk => ⟨pat k hk, old k hk⟩⟩

/-- `Left011` follows from `Rule30PeriodThreeLanguage.C3r011`. -/
theorem left011_of_C3r (h : Rule30PeriodThreeLanguage.C3r011) : Left011 := by
  rintro s hs ⟨K, pat, free⟩
  have old := free_of_cover (large := Rule30PeriodThreeLanguage.col1Forbidden011) (by decide) free
  exact h s hs ⟨K, fun k hk => ⟨pat k hk, old k hk⟩⟩

end Ruliology.CellularAutomata.Rule30PeriodThreeEntry
