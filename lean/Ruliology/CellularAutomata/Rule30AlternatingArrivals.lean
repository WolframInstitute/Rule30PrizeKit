module

public import Ruliology.CellularAutomata.Rule30Certificates.AlternatingArrivals
public import Ruliology.CellularAutomata.Rule30Ether
public import Ruliology.CellularAutomata.Rule30MaskedJen
public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30DrivenPrefix
public import Ruliology.CellularAutomata.Rule30SourceArrivals

/-!
# If the centre of Rule 30 eventually alternates, Lowry's source net is aperiodic on each phase

Let `F` be a right half of rule 30, of any support, beside a column that alternates, black first (`Alt F T`). Read it at the white
ticks. The *kick* is the first cell (`gate`), the *net* the first cell exclusive-or the second (`net`), and the *black net* the first
cell without the second at the black tick after it (`blackNet`). An *odd kick* is a kick whose net is white (`oddKick`).

* **The single cell.** If its centre alternates from some time on (`AltCenter`), then none of these streams is eventually periodic:
  Lowry's net and shell on the white ticks and on the black ticks (`both_phases`), and the odd kicks (`odd_kicks_aperiodic`). The net at
  two successive white ticks is equal exactly when the second is an odd kick (`lowry_odd_return`). Whether the centre ever alternates for
  ever is open, and nothing here bears on it.
* **The local law** (`law_of_alt`), on every right half. The net is complemented at every white tick that is not a kick, and was white
  just before one. So the net at a kick is black exactly when its next kick is an even number of white ticks later (`net_of_return`), and
  two successive nets are equal exactly at an odd kick (`odd_of_equal_nets`).
* **A closed set.** `closedSet` is 777 windows of the first twelve cells at a white tick. A half in it stays in it, whatever lies beyond
  (`stays`), and its kicks then read none of ten words (`clean_of_set`): the gaps are 2 to 5, seven of the sixteen pairs do not occur,
  and 2, 2, 5 does not occur. Every right half enters it, or its kicks eventually come once in four (`every_half`, `enters_or_four`).
* **Decoding after entry.** Nine nets give every kick (`kick_of_white_nets`); two black nets, four black samples apart, give the odd kicks
  (`odd_of_black_nets`), and an odd kick is one whose next kick is three or five white ticks later (`odd_iff`). For unrestricted
  starting halves nine nets do not decide it: two finite halves read the same nine nets and differ in the kick at sample index 6
  (`nine_collision`, `no_unrestricted_nine`).
* **Periodicity.** Beside an alternating column, for every right half of any support, the kicks, the net and the odd kicks are eventually
  periodic together, and an eventually periodic black net makes the kicks eventually periodic too (`periodic_together_of_alt`;
  `four_tail` is the other branch).

The finite part is one table of sets of times on spatial prefixes, walked once against itself with a white and a black tick as the step
(the method of `Rule30TrappedRunMasks`), and two searches over words. The local law is a table of six cells. Masked Jen
(`Rule30MaskedJen`) excludes the periodic kicks of the single cell.

Known. Every gate trace in the closed set obeys AIOvernight's nine-pair gap rule, and it also avoids the gap sequence 2, 2, 5, which six
columns exclude once one full white and black period has elapsed (`Rule30PeriodTwoOnset`). That every right half eventually obeys the nine pairs or reads pure fours is AIOvernight's
`Rule30PeriodTwoWidth13`, by a rank certificate of a strip of thirteen columns. What is added is the explicit closed set and the entry
into it, the decoders, and a proof that checks in nine seconds. Lowry's net, shell and two-step identity are those of
`Rule30SourceArrivals`. Lowry's net is aperiodic there when two black ticks follow
each white one.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ruliology.CellularAutomata.Rule30AlternatingArrivals
open Rule30Jen Rule30Ether Rule30MaskedJen Rule30StripCertificates
open Rule30DrivenPrefix (step step_bit)
open Rule30PeriodTwoCoupled (altCol)
open Rule30TrappedRunMasks (Tree subset subset_sound)
open Rule30AlternatingArrivalsTables

/-! ### The walk of a table against itself -/

theorem walk_easy {a b : Tree} (va : a.valid = true) (vb : b.valid = true) (x y k t : Nat) {colours : Nat}
    (ok : subset ((a.high <<< 1) &&& colours) b.low = true) (ha : (a.value x (k+2)).testBit t = true)
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

theorem walk_sound {d0 d1 : Bool} (n : Nat) {a b : Tree} {colours k x t : Nat} {x1 x2 y0 y1 : Bool}
    (ok : walk colours a b x1 x2 y0 y1 n = true) (va : a.valid = true) (vb : b.valid = true)
    (hx1 : x1 = x.testBit (k+1)) (hx2 : x2 = x.testBit (k+2))
    (hy0 : y0 = (step d0 x).testBit k) (hy1 : y1 = (step d0 x).testBit (k+1))
    (ha : (a.value x (k+3)).testBit t = true) (hc : colours.testBit (t+1) = true) :
    (b.value (per d0 d1 x) (k+1)).testBit (t+1) = true := by
  induction n generalizing a b k x1 x2 y0 y1 with
  | zero => exact walk_easy va vb x _ (k+1) t ok ha hc
  | succ n ih =>
    simp only [walk] at ok
    split at ok
    · rename_i h; exact walk_easy va vb x _ (k+1) t h ha hc
    · obtain ⟨l, r⟩ := Bool.and_eq_true_iff.mp ok
      have ey : (step d0 x).testBit (k+2) = xor x1 (x2 || x.testBit (k+3)) := by rw [hx1, hx2, step_succ]
      have ez : (per d0 d1 x).testBit (k+1) = xor y0 (y1 || (step d0 x).testBit (k+2)) := by
        rw [hy0, hy1, per, step_succ]
      have next : ((a.child (x.testBit (k+3))).value x (k+1+3)).testBit t = true := by
        rw [show k+1+3 = (k+3)+1 by omega, Tree.child_value]; exact ha
      have fin : ((b.child ((per d0 d1 x).testBit (k+1))).value (per d0 d1 x) (k+1+1)).testBit (t+1) = true := by
        cases hb : x.testBit (k+3)
        · rw [hb] at next
          rw [hb] at ey
          have ey' : (step d0 x).testBit (k+2) = xor x1 x2 := by rw [ey]; simp
          rw [ey'] at ez
          rw [ez]
          exact ih l (a.child_valid va _) (b.child_valid vb _) hx2 (by rw [hb]) hy1 ey'.symm next
        · rw [hb] at next
          rw [hb] at ey
          have ey' : (step d0 x).testBit (k+2) = !x1 := by rw [ey]; simp
          rw [ey'] at ez
          rw [ez]
          exact ih r (a.child_valid va _) (b.child_valid vb _) hx2 (by rw [hb]) hy1 ey'.symm next
      simpa only [Tree.child_value] using fin

theorem walk_start {table : Tree} {white black : Nat} {d0 d1 : Bool} (ok : walkAll table white black d0 d1 = true)
    (x0 x1 x2 : Bool) : walkAt table white black d0 d1 x0 x1 x2 = true := by
  have m (b : Bool) : b ∈ [false, true] := by cases b <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp ok x0 (m _)) x1 (m _)) x2 (m _)

/-- A time of a row passes to the next time of the row one period later, when the first cell there has an allowed colour. -/
theorem walk_all {table : Tree} {white black : Nat} {d0 d1 : Bool} (va : table.valid = true)
    (ok : walkAll table white black d0 d1 = true) (x t : Nat) (ha : (table.value x 0).testBit t = true)
    (hc : (if (per d0 d1 x).testBit 0 then black else white).testBit (t+1) = true) :
    (table.value (per d0 d1 x) 0).testBit (t+1) = true := by
  have w := walk_start ok (x.testBit 0) (x.testBit 1) (x.testBit 2)
  simp only [walkAt] at w
  have y0 : (step d0 x).testBit 0 = xor d0 (x.testBit 0 || x.testBit 1) := step_zero ..
  have y1 : (step d0 x).testBit 1 = xor (x.testBit 0) (x.testBit 1 || x.testBit 2) := step_succ ..
  have w0 : (per d0 d1 x).testBit 0 = xor d1 ((step d0 x).testBit 0 || (step d0 x).testBit 1) := by
    rw [per, step_zero]
  rw [← y0, ← y1, ← w0] at w
  have start : ((((table.child (x.testBit 0)).child (x.testBit 1)).child (x.testBit 2)).value x 3).testBit t = true := by
    rw [show (3:Nat) = 2+1 by rfl, Tree.child_value, show (2:Nat) = 1+1 by rfl, Tree.child_value, show (1:Nat) = 0+1 by rfl,
      Tree.child_value]
    exact ha
  have vc := Tree.child_valid (Tree.child_valid (Tree.child_valid va (x.testBit 0)) (x.testBit 1)) (x.testBit 2)
  have fin := walk_sound (d0 := d0) (d1 := d1) (k := 0) (x := x) (t := t) 46 w vc (Tree.child_valid va _) rfl rfl rfl rfl start hc
  rw [← Tree.child_value table (per d0 d1 x) 0]
  exact fin

/-- The rows at successive periods. -/
def rows (d0 d1 : Bool) (x : Nat) : Nat → Nat
  | 0 => x
  | i+1 => per d0 d1 (rows d0 d1 x i)

/-- A row carries its time along a line for as long as its first cells have the line's colours. -/
theorem march {table : Tree} {white black : Nat} {d0 d1 : Bool} (va : table.valid = true)
    (ok : walkAll table white black d0 d1 = true) {x o n : Nat} (start : (table.value x 0).testBit o = true)
    (cols : ∀ i, i < n → (if (rows d0 d1 x (i+1)).testBit 0 then black else white).testBit (o+(i+1)) = true) :
    ∀ i, i ≤ n → (table.value (rows d0 d1 x i) 0).testBit (o+i) = true := by
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
variable {T : Tree} {white black : Nat} {d0 d1 : Bool}

theorem free_march (va : T.valid = true) (ok : walkAll T white black d0 d1 = true) {x o n : Nat}
    (free : freeFrom white black o n = true) (start : (T.value x 0).testBit o = true) :
    (T.value (rows d0 d1 x n) 0).testBit (o+n) = true := by
  refine march va ok start (fun i hi => ?_) n (Nat.le_refl _)
  have f := List.all_eq_true.mp free i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true] at f
  split
  · exact f.2
  · exact f.1

/-- **The closed set.** Bit 0 is carried to the row one period later. -/
theorem bit_closed (va : T.valid = true) (ok : walkAll T white black d0 d1 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true) {x : Nat}
    (h : (T.value x 0).testBit 0 = true) : (T.value (per d0 d1 x) 0).testBit 0 = true := by
  have a := free_march va ok (n := 1) free h
  have l := beq_iff_eq.mp (leaves_value wrap (per d0 d1 x) 0)
  rw [← l]
  exact a

theorem bit_stays (va : T.valid = true) (ok : walkAll T white black d0 d1 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true) {x : Nat}
    (h : (T.value x 0).testBit 0 = true) : ∀ i, (T.value (rows d0 d1 x i) 0).testBit 0 = true
  | 0 => h
  | i+1 => bit_closed va ok free wrap (bit_stays va ok free wrap h i)

/-- **Entry.** After `m + n` periods every row is in the closed set, unless after `m` it has the exceptional bit `e`. -/
theorem bit_entry (va : T.valid = true) (ok : walkAll T white black d0 d1 = true) {A B m n e : Nat}
    (freeA : freeFrom white black A m = true) (freeB : freeFrom white black B n = true)
    (first : T.low.testBit A = true)
    (middle : leaves (fun k => !k.testBit (A+m) || (k.testBit B || k.testBit e)) T = true)
    (last : leaves (fun k => !k.testBit (B+n) || k.testBit 0) T = true) (x : Nat) :
    (T.value (rows d0 d1 x m) 0).testBit e = true ∨
      (T.value (rows d0 d1 (rows d0 d1 x m) n) 0).testBit 0 = true := by
  have a := free_march va ok freeA ((T.bounds va x 0 A).1 first)
  have c := leaves_value middle (rows d0 d1 x m) 0
  rw [a] at c
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at c
  rcases c with b | b
  · right
    have f := free_march va ok freeB b
    have l := leaves_value last (rows d0 d1 (rows d0 d1 x m) n) 0
    rw [f] at l
    simpa using l
  · exact Or.inl b

theorem mem_colours (c : Bool) : c ∈ [false, true] := by cases c <;> simp

/-- **A pattern that no row of the closed set reads.** -/
theorem bit_word (va : T.valid = true) (ok : walkAll T white black d0 d1 = true) {o : Nat} {v : List (Option Bool)}
    (line : wordLine T white black o v = true) (pos : 0 < v.length) {x : Nat} (h : (T.value x 0).testBit 0 = true)
    (read : ∀ i, i < v.length → fits (v.getD i none) ((rows d0 d1 x i).testBit 0) = true) : False := by
  simp only [wordLine, Bool.and_eq_true] at line
  obtain ⟨⟨st, cl⟩, en⟩ := line
  have kid (y : Nat) (t : Nat) (hy : (T.value y 0).testBit t = true) :
      ((T.child (y.testBit 0)).value y 1).testBit t = true := by rw [Tree.child_value T y 0]; exact hy
  have start : (T.value x 0).testBit o = true := by
    have r0 := read 0 pos
    have hd : v.headD none = v.getD 0 none := by cases v <;> rfl
    have s := List.all_eq_true.mp st _ (mem_colours (x.testBit 0))
    rw [hd] at s
    rw [show rows d0 d1 x 0 = x from rfl] at r0
    rw [r0] at s
    simp only [Bool.not_true, Bool.false_or] at s
    have l := leaves_value s x 1
    rw [kid x 0 h] at l
    rw [← Tree.child_value T x 0]
    simpa using l
  have all := march (n := v.length - 1) va ok start (fun i hi => by
    have c := List.all_eq_true.mp (List.all_eq_true.mp cl i (List.mem_range.mpr hi)) _ (mem_colours ((rows d0 d1 x (i+1)).testBit 0))
    rw [read (i+1) (by omega)] at c
    simpa using c) (v.length - 1) (Nat.le_refl _)
  have e := List.all_eq_true.mp en _ (mem_colours ((rows d0 d1 x (v.length-1)).testBit 0))
  rw [read (v.length - 1) (by omega)] at e
  simp only [Bool.not_true, Bool.false_or] at e
  have l := leaves_value e (rows d0 d1 x (v.length-1)) 1
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

theorem fits_per {F : Nat → Nat → Bool} (hF : IsR30 F) {t x L : Nat} {d0 d1 : Bool} (h0 : F t 0 = d0)
    (h1 : F (t+1) 0 = d1) (h : Fits F t x (L+2)) : Fits F (t+2) (per d0 d1 x) L :=
  fits_step hF h1 (fits_step hF h0 h)

/-- The drive reads `d0 d1` over the `n` periods from `t`. -/
def Drive (F : Nat → Nat → Bool) (d0 d1 : Bool) (t n : Nat) : Prop :=
  ∀ i, i < n → F (t+2*i) 0 = d0 ∧ F (t+2*i+1) 0 = d1

theorem fits_rows {F : Nat → Nat → Bool} (hF : IsR30 F) {t x L n : Nat} {d0 d1 : Bool} (hd : Drive F d0 d1 t n)
    (h : Fits F t x (L+2*n)) : ∀ i, i ≤ n → Fits F (t+2*i) (rows d0 d1 x i) (L+2*(n-i)) := by
  intro i
  induction i with
  | zero => intro _; exact h
  | succ i ih =>
    intro hi
    obtain ⟨h0, h1⟩ := hd i (by omega)
    have f := ih (by omega)
    rw [show L+2*(n-i) = L+2*(n-(i+1))+2 by omega] at f
    exact fits_per hF h0 h1 f

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

/-- The first twelve cells of the half at tick `t` are a window of the list. -/
def InTrap (trap : List Nat) (F : Nat → Nat → Bool) (t : Nat) : Prop := code F t 12 ∈ trap

section
variable {T : Tree} {trap : List Nat}

theorem trap_of_bit (va : T.valid = true) (is : isTrap T trap = true) {F : Nat → Nat → Bool} {t x L : Nat}
    (h : Fits F t x L) (le : 12 ≤ L) (hb : (T.value x 0).testBit 0 = true) : InTrap trap F t := by
  simp only [isTrap, Bool.and_eq_true] at is
  have m := mem_codes (t := 0) 12 va (k := 0) (p := 0) (r := x) (by simp [Nat.mod_one]) hb
  rw [beq_iff_eq.mp is.1, Nat.zero_add] at m
  unfold InTrap
  rw [← code_of_fits h le]
  exact m

theorem bit_of_trap (va : T.valid = true) (is : isTrap T trap = true) {F : Nat → Nat → Bool} {t x L : Nat}
    (h : Fits F t x L) (le : 12 ≤ L) (hb : InTrap trap F t) : (T.value x 0).testBit 0 = true := by
  simp only [isTrap, Bool.and_eq_true] at is
  refine codes_bit 12 va is.2 (k := 0) (p := 0) (c := code F t 12) (by decide) (by rw [beq_iff_eq.mp is.1]; exact hb)
    (fun i hi => ?_)
  rw [Nat.zero_add, code_bit, h i (by omega)]
  simp [hi]

end

/-! ### The trap is closed, and entry -/

theorem rows_add (d0 d1 : Bool) (x a : Nat) : ∀ b, rows d0 d1 x (a+b) = rows d0 d1 (rows d0 d1 x a) b
  | 0 => rfl
  | b+1 => by rw [← Nat.add_assoc]; exact congrArg _ (rows_add d0 d1 x a b)

theorem Drive.mono {F : Nat → Nat → Bool} {d0 d1 : Bool} {t n m : Nat} (h : Drive F d0 d1 t n) (le : m ≤ n) :
    Drive F d0 d1 t m := fun i hi => h i (by omega)

theorem Drive.shift {F : Nat → Nat → Bool} {d0 d1 : Bool} {t n : Nat} (k : Nat) (h : Drive F d0 d1 t (k+n)) :
    Drive F d0 d1 (t+2*k) n := by
  intro i hi
  have := h (k+i) (by omega)
  rwa [show t+2*(k+i) = t+2*k+2*i by omega] at this

section
variable {T : Tree} {white black : Nat} {d0 d1 : Bool} {trap : List Nat} {F : Nat → Nat → Bool}

theorem trap_row (va : T.valid = true) (ok : walkAll T white black d0 d1 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true)
    (is : isTrap T trap = true) (hF : IsR30 F) {t n : Nat} (hd : Drive F d0 d1 t n) (h : InTrap trap F t) :
    ∃ x, (∀ i, i ≤ n → Fits F (t+2*i) (rows d0 d1 x i) (12+2*(n-i))) ∧
      ∀ i, (T.value (rows d0 d1 x i) 0).testBit 0 = true := by
  have f := fits_code F t (12+2*n)
  exact ⟨_, fits_rows hF hd f, bit_stays va ok free wrap (bit_of_trap va is f (by omega) h)⟩

theorem trap_stays (va : T.valid = true) (ok : walkAll T white black d0 d1 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true)
    (is : isTrap T trap = true) (hF : IsR30 F) {t n : Nat} (hd : Drive F d0 d1 t n) (h : InTrap trap F t) :
    InTrap trap F (t+2*n) := by
  obtain ⟨x, fx, bx⟩ := trap_row va ok free wrap is hF hd h
  exact trap_of_bit va is (fx n (Nat.le_refl _)) (by omega) (bx n)

theorem trap_entry (va : T.valid = true) (ok : walkAll T white black d0 d1 = true) (is : isTrap T trap = true)
    {A B m n e W : Nat} {outs : List Nat} (freeA : freeFrom white black A m = true) (freeB : freeFrom white black B n = true)
    (first : T.low.testBit A = true) (middle : leaves (fun k => !k.testBit (A+m) || (k.testBit B || k.testBit e)) T = true)
    (last : leaves (fun k => !k.testBit (B+n) || k.testBit 0) T = true) (outCodes : codes e T 0 0 W = outs)
    (hF : IsR30 F) {t : Nat} (hd : Drive F d0 d1 t (m+n)) : InTrap trap F (t+2*(m+n)) ∨ code F (t+2*m) W ∈ outs := by
  have f := fits_code F t (12+W+2*(m+n))
  have fx := fits_rows hF hd f
  rcases bit_entry va ok freeA freeB first middle last (code F t (12+W+2*(m+n))) with h | h
  · right
    have mem := mem_codes (t := e) W va (k := 0) (p := 0) (r := rows d0 d1 (code F t (12+W+2*(m+n))) m)
      (by simp [Nat.mod_one]) h
    rw [outCodes, Nat.zero_add, code_of_fits (fx m (by omega)) (by omega)] at mem
    exact mem
  · left
    rw [← rows_add] at h
    exact trap_of_bit va is (fx (m+n) (Nat.le_refl _)) (by omega) h

/-- A half that is not in the trap at a tick was outside, and showed an exceptional window, at every earlier one. -/
theorem outside_before (va : T.valid = true) (ok : walkAll T white black d0 d1 = true)
    (free : freeFrom white black 0 1 = true) (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true)
    (is : isTrap T trap = true) {A B m n e W : Nat} {outs : List Nat} (freeA : freeFrom white black A m = true)
    (freeB : freeFrom white black B n = true) (first : T.low.testBit A = true)
    (middle : leaves (fun k => !k.testBit (A+m) || (k.testBit B || k.testBit e)) T = true)
    (last : leaves (fun k => !k.testBit (B+n) || k.testBit 0) T = true) (outCodes : codes e T 0 0 W = outs)
    (hF : IsR30 F) {t q : Nat} (hd : Drive F d0 d1 t (m+n+q)) (no : ¬ InTrap trap F (t+2*(m+n+q))) :
    ∀ i, i ≤ q → code F (t+2*m+2*i) W ∈ outs := by
  intro i hi
  have hd' := (hd.mono (m := i+(m+n)) (by omega)).shift i
  rcases trap_entry va ok is freeA freeB first middle last outCodes hF hd' with h | h
  · exfalso
    apply no
    have tail := (hd.mono (m := (i+(m+n))+(q-i)) (by omega)).shift (i+(m+n))
    rw [show t+2*(i+(m+n)) = t+2*i+2*(m+n) by omega] at tail
    have s := trap_stays va ok free wrap is hF tail h
    rwa [show t+2*i+2*(m+n)+2*(q-i) = t+2*(m+n+q) by omega] at s
  · rwa [show t+2*i+2*m = t+2*m+2*i by omega] at h

end

/-! ### The windows that can stay outside -/

theorem image_mem {F : Nat → Nat → Bool} (hF : IsR30 F) {d0 d1 : Bool} {t : Nat} (hd : Drive F d0 d1 t 1) (W : Nat) :
    code F (t+2) W ∈ images d0 d1 W (code F t W) := by
  obtain ⟨h0, h1⟩ := hd 0 (by omega)
  have f := fits_code F t (W+2)
  have g := code_of_fits (fits_per hF h0 h1 f) (Nat.le_refl W)
  refine List.mem_map.mpr ⟨code F t (W+2) / 2^W, ?_, ?_⟩
  · have lt := code_lt F t (W+2)
    rw [List.mem_range, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos W)]
    rw [Nat.pow_add] at lt
    omega
  · have m := code_of_fits (f.mono (M := W) (by omega)) (Nat.le_refl W)
    show per d0 d1 (code F t W + 2^W * (code F t (W+2) / 2^W)) % 2^W = code F (t+2) W
    rw [← m, Nat.mod_add_div]
    exact g

/-- The window is in the list at `n + 1` successive periods from `t`. -/
def Among (F : Nat → Nat → Bool) (t n W : Nat) (A : List Nat) : Prop := ∀ i, i ≤ n → code F (t+2*i) W ∈ A

section
variable {F : Nat → Nat → Bool} {d0 d1 : Bool}

theorem among_round (hF : IsR30 F) {t n W : Nat} {A : List Nat} (hd : Drive F d0 d1 t (n+2)) (h : Among F t (n+2) W A) :
    Among F (t+2) n W (fwd d0 d1 W (back d0 d1 W A)) := by
  have im (i : Nat) (hi : i < n+2) : code F (t+2*(i+1)) W ∈ images d0 d1 W (code F (t+2*i) W) := by
    have := image_mem hF ((hd.mono (m := i+1) (by omega)).shift i) W
    rwa [show t+2*i+2 = t+2*(i+1) by omega] at this
  have b (i : Nat) (hi : i < n+2) : code F (t+2*i) W ∈ back d0 d1 W A := by
    refine List.mem_filter.mpr ⟨h i (by omega), List.any_eq_true.mpr ⟨_, im i hi, ?_⟩⟩
    exact List.contains_iff_mem.mpr (h (i+1) (by omega))
  intro i hi
  rw [show t+2+2*i = t+2*(i+1) by omega]
  refine List.mem_filter.mpr ⟨b (i+1) (by omega), List.contains_iff_mem.mpr ?_⟩
  exact List.mem_flatMap.mpr ⟨_, b i (by omega), im i (by omega)⟩

theorem among_rounds (hF : IsR30 F) {W : Nat} : ∀ (r : Nat) {t n : Nat} {A : List Nat}, Drive F d0 d1 t (n+2*r) →
    Among F t (n+2*r) W A → Among F (t+2*r) n W (rounds d0 d1 W r A)
  | 0, _, _, _, _, h => h
  | r+1, t, n, A, hd, h => by
    have s := among_round hF (n := n+2*r) hd h
    have d := ((hd.mono (m := 1+(n+2*r)) (by omega)).shift 1)
    have q := among_rounds hF r (t := t+2) (n := n) d s
    rwa [show t+2+2*r = t+2*(r+1) by omega] at q

theorem among_widen {t n W : Nat} {A : List Nat} (h : Among F t n W A) : Among F t n (W+1) (widen W A) := by
  intro i hi
  have a := h i hi
  rw [← code_of_fits ((fits_code F (t+2*i) (W+1)).mono (M := W) (by omega)) (Nat.le_refl W)] at a
  have lt := code_lt F (t+2*i) (W+1)
  have split := Nat.mod_add_div (code F (t+2*i) (W+1)) (2^W)
  have two : code F (t+2*i) (W+1) / 2^W < 2 := by
    apply Nat.div_lt_of_lt_mul
    rwa [Nat.pow_succ] at lt
  have either : code F (t+2*i) (W+1) / 2^W = 0 ∨ code F (t+2*i) (W+1) / 2^W = 1 := by
    revert two
    generalize code F (t+2*i) (W+1) / 2^W = d
    omega
  rw [← split]
  rcases either with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero]
    exact List.mem_append.mpr (Or.inl a)
  · rw [e, Nat.mul_one]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, a, rfl⟩))

theorem among_chase (hF : IsR30 F) : ∀ (rs : List Nat) {W t n : Nat} {A : List Nat}, Drive F d0 d1 t (n+2*rs.sum) →
    Among F t (n+2*rs.sum) W A → Among F (t+2*rs.sum) n (W+rs.length) (chase d0 d1 W rs A)
  | [], _, _, _, _, _, h => h
  | r :: rs, W, t, n, A, hd, h => by
    have e : n+2*(r :: rs).sum = (n+2*rs.sum)+2*r := by rw [List.sum_cons]; omega
    rw [e] at hd h
    have s := among_widen (among_rounds hF r hd h)
    have d := (hd.mono (m := r+(n+2*rs.sum)) (by omega)).shift r
    have q := among_chase hF rs d s
    have e1 : t+2*r+2*rs.sum = t+2*(r :: rs).sum := by rw [List.sum_cons]; omega
    have e2 : W+1+rs.length = W+(r :: rs).length := by rw [List.length_cons]; omega
    rwa [e1, e2] at q

end

/-! ### The net on a driven half obeys a local law -/

/-- Column `0` alternates from `T`: black at `T + 2k`, white at `T + 2k + 1`. -/
def Alt (F : Nat → Nat → Bool) (T : Nat) : Prop := ∀ k, F (T+2*k) 0 = true ∧ F (T+2*k+1) 0 = false

/-- The gate, or kick: the first cell at the `k`-th white tick. -/
def gate (F : Nat → Nat → Bool) (T k : Nat) : Bool := F (T+2*k+1) 1
/-- The net at the white tick: the first cell exclusive-or the second. -/
def net (F : Nat → Nat → Bool) (T k : Nat) : Bool := xor (F (T+2*k+1) 1) (F (T+2*k+1) 2)
/-- The net at the black tick after the white one: the first cell without the second. -/
def blackNet (F : Nat → Nat → Bool) (T k : Nat) : Bool := F (T+2*k+2) 1 && !F (T+2*k+2) 2

/-- The cells of a row at a white tick are those of the black row before it, whose wall is black; the two ticks after it are
those of two more. Checked on the cells of the black row before. -/
theorem localLaw : ∀ c1 c2 c3 c4 c5 c6 : Bool,
    let x := rule true c1 c2; let y := rule c1 c2 c3; let z := rule c2 c3 c4; let w := rule c3 c4 c5; let v := rule c4 c5 c6
    let x' := rule true (rule false x y) (rule x y z)
    let y' := rule (rule false x y) (rule x y z) (rule y z w)
    let z' := rule (rule x y z) (rule y z w) (rule z w v)
    let x'' := rule true (rule false x' y') (rule x' y' z')
    (x' = false → xor x' y' = !(xor x y)) ∧ (x' = true → xor x y = false) ∧ (x = true → x' = false) ∧
    (x = true → xor x y = true → (rule false x y && !rule x y z) = true → x'' = false) ∧
    ((rule false x y && !rule x y z) = true → x = true) ∧
    (x = true → xor x y = false → (rule false x y && !rule x y z) = true) := by
  decide +kernel

/-- The law of the gate `g`, the net `a` and the black net `b`. -/
structure Law (g a b : Nat → Bool) : Prop where
  toggle : ∀ k, g (k+1) = false → a (k+1) = !a k
  reset : ∀ k, g (k+1) = true → a k = false
  lone : ∀ k, g k = true → g (k+1) = false
  skip : ∀ k, g k = true → a k = true → b k = true → g (k+2) = false
  black : ∀ k, b k = true → g k = true
  odd : ∀ k, g k = true → a k = false → b k = true

theorem Law.shift {g a b : Nat → Bool} (L : Law g a b) (m : Nat) : Law (fun k => g (m+k)) (fun k => a (m+k)) (fun k => b (m+k)) where
  toggle k h := L.toggle (m+k) h
  reset k h := L.reset (m+k) h
  lone k h := L.lone (m+k) h
  skip k := L.skip (m+k)
  black k := L.black (m+k)
  odd k := L.odd (m+k)

/-- **The law.** On every right half beside an alternating column, at every white tick: at a tick that is not a kick the net is
the complement of the one before; at a kick the net before was white; kicks stand alone; and the black net sees only kicks,
every kick whose net is white, and a kick whose net is black only if the one after next is white. -/
theorem law_of_alt {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat} (h : Alt F T) : Law (gate F T) (net F T) (blackNet F T) := by
  have main (k : Nat) :
      (gate F T (k+1) = false → net F T (k+1) = !net F T k) ∧ (gate F T (k+1) = true → net F T k = false) ∧
      (gate F T k = true → gate F T (k+1) = false) ∧
      (gate F T k = true → net F T k = true → blackNet F T k = true → gate F T (k+2) = false) ∧
      (blackNet F T k = true → gate F T k = true) ∧
      (gate F T k = true → net F T k = false → blackNet F T k = true) := by
    generalize hu : T+2*k = u
    have hb : F u 0 = true := by rw [← hu]; exact (h k).1
    have hw : F (u+1) 0 = false := by rw [← hu]; exact (h k).2
    have hb' : F (u+2) 0 = true := by have := (h (k+1)).1; rwa [show T+2*(k+1) = u+2 by omega] at this
    have hw' : F (u+3) 0 = false := by have := (h (k+1)).2; rwa [show T+2*(k+1)+1 = u+3 by omega] at this
    have hb'' : F (u+4) 0 = true := by have := (h (k+2)).1; rwa [show T+2*(k+2) = u+4 by omega] at this
    have e0 : F (u+1) 1 = rule true (F u 1) (F u 2) := by rw [← hb]; exact hF u 0
    have e1 : F (u+1) 2 = rule (F u 1) (F u 2) (F u 3) := hF u 1
    have e2 : F (u+1) 3 = rule (F u 2) (F u 3) (F u 4) := hF u 2
    have e3 : F (u+1) 4 = rule (F u 3) (F u 4) (F u 5) := hF u 3
    have e4 : F (u+1) 5 = rule (F u 4) (F u 5) (F u 6) := hF u 4
    have m1 : F (u+2) 1 = rule false (F (u+1) 1) (F (u+1) 2) := by rw [← hw]; exact hF (u+1) 0
    have m2 : F (u+2) 2 = rule (F (u+1) 1) (F (u+1) 2) (F (u+1) 3) := hF (u+1) 1
    have m3 : F (u+2) 3 = rule (F (u+1) 2) (F (u+1) 3) (F (u+1) 4) := hF (u+1) 2
    have m4 : F (u+2) 4 = rule (F (u+1) 3) (F (u+1) 4) (F (u+1) 5) := hF (u+1) 3
    have n1 : F (u+3) 1 = rule true (F (u+2) 1) (F (u+2) 2) := by rw [← hb']; exact hF (u+2) 0
    have n2 : F (u+3) 2 = rule (F (u+2) 1) (F (u+2) 2) (F (u+2) 3) := hF (u+2) 1
    have n3 : F (u+3) 3 = rule (F (u+2) 2) (F (u+2) 3) (F (u+2) 4) := hF (u+2) 2
    have q1 : F (u+4) 1 = rule false (F (u+3) 1) (F (u+3) 2) := by rw [← hw']; exact hF (u+3) 0
    have q2 : F (u+4) 2 = rule (F (u+3) 1) (F (u+3) 2) (F (u+3) 3) := hF (u+3) 1
    have r1 : F (u+5) 1 = rule true (F (u+4) 1) (F (u+4) 2) := by rw [← hb'']; exact hF (u+4) 0
    have k1 : T+2*(k+1)+1 = u+3 := by omega
    have k2 : T+2*(k+2)+1 = u+5 := by omega
    have k1' : T+2*(k+1)+2 = u+4 := by omega
    simp only [gate, net, blackNet, k1, k2, show T+2*k+1 = u+1 by omega, show T+2*k+2 = u+2 by omega]
    rw [r1, q1, q2, n1, n2, n3, m1, m2, m3, m4, e0, e1, e2, e3, e4]
    have g := localLaw (F u 1) (F u 2) (F u 3) (F u 4) (F u 5) (F u 6)
    simpa only [] using g
  exact ⟨fun k => (main k).1, fun k => (main k).2.1, fun k => (main k).2.2.1, fun k => (main k).2.2.2.1,
    fun k => (main k).2.2.2.2.1, fun k => (main k).2.2.2.2.2⟩

/-- Two successive nets are equal exactly at an odd kick. -/
theorem Law.equal {g a b : Nat → Bool} (L : Law g a b) (k : Nat) : (a k == a (k+1)) = (g (k+1) && !a (k+1)) := by
  cases h : g (k+1)
  · rw [L.toggle k h]; cases a k <;> rfl
  · rw [L.reset k h]; cases a (k+1) <;> rfl

/-! ### A search over readings -/

/-- Reads `g` as the word `w` from index `i`. -/
def Spells (u : Nat → Bool) (i : Nat) (v : List Bool) : Prop := ∀ k, k < v.length → u (i+k) = v.getD k false

/-- The gate words that rule the closed set out: gap one and six or more, the seven pairs, and 2, 2, 5. -/
def banned : List (List Bool) := [
  [true, true], [false, false, false, false, false], [true, false, true, false, false, true], [true, false, false, true, false, true],
  [true, false, false, true, false, false, false, true], [true, false, false, false, true, false, true],
  [true, false, false, false, true, false, false, true], [true, false, false, false, true, false, false, false, true],
  [true, false, false, false, false, true, false, false, false, true], [true, false, true, false, true, false, false, false, false, true]]

/-- Gate, net, black net. -/
abbrev Letter := Bool × Bool × Bool

def okLetter (q : Letter) : Bool := (!q.2.2 || q.1) && (!(q.1 && !q.2.1) || q.2.2)

def okStep (p q : Letter) : Bool := (q.1 || (q.2.1 == !p.2.1)) && (!q.1 || !p.2.1) && !(p.1 && q.1)

/-- After the letters `h`, the latest first, may `q` follow? -/
def okNext : List Letter → Letter → Bool
  | [], q => okLetter q
  | [p], q => okLetter q && okStep p q
  | p :: p' :: _, q => okLetter q && okStep p q && !(p'.1 && p'.2.1 && p'.2.2 && q.1)

def ends : List Bool → List Letter → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: r, q :: h => (q.1 == c) && ends r h

def hasBanned (h : List Letter) : Bool := banned.any fun w => ends w.reverse h

def allLetters : List Letter := [(false,false,false), (false,true,false), (true,false,true), (true,true,false), (true,true,true),
  (false,false,true), (false,true,true), (true,false,false)]

def search (test : List Letter → Bool) : Nat → List Letter → Bool
  | 0, h => test h
  | n+1, h => allLetters.all fun q => !okNext h q || hasBanned (q :: h) || search test n (q :: h)

/-- The letters before index `k`, the latest first. -/
def hist (g a b : Nat → Bool) : Nat → List Letter
  | 0 => []
  | k+1 => (g k, a k, b k) :: hist g a b k

theorem mem_allLetters : ∀ q : Letter, q ∈ allLetters := by
  rintro ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

theorem ends_hist {g a b : Nat → Bool} : ∀ (r : List Bool) (k : Nat), ends r (hist g a b k) = true →
    r.length ≤ k ∧ ∀ i, i < r.length → g (k-1-i) = r.getD i false
  | [], _, _ => ⟨Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | c :: r, 0, h => by simp [hist, ends] at h
  | c :: r, k+1, h => by
    simp only [hist, ends, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨le, at_⟩ := ends_hist r k h.2
    refine ⟨by simp; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := at_ i (by simpa using hi)
      rw [show k+1-1-(i+1) = k-1-i by omega]
      simpa using this

theorem no_banned {g a b : Nat → Bool} (clean : ∀ w ∈ banned, ∀ i, ¬ Spells g i w) (k : Nat) : hasBanned (hist g a b k) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨w, hw, e⟩ := List.any_eq_true.mp h
  obtain ⟨le, at_⟩ := ends_hist _ _ e
  rw [List.length_reverse] at le at_
  refine clean w hw (k-w.length) (fun j hj => ?_)
  have := at_ (w.length-1-j) (by omega)
  rw [show k-1-(w.length-1-j) = k-w.length+j by omega] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), List.getD_eq_getElem?_getD]
  congr 2
  omega

theorem okNext_law {g a b : Nat → Bool} (L : Law g a b) : ∀ k, okNext (hist g a b k) (g k, a k, b k) = true := by
  have letter (k : Nat) : okLetter (g k, a k, b k) = true := by
    simp only [okLetter]
    cases hb : b k
    · cases hg : g k
      · cases a k <;> rfl
      · cases ha : a k
        · have := L.odd k hg ha; rw [hb] at this; cases this
        · rfl
    · rw [L.black k hb]
      cases a k <;> rfl
  have step (k : Nat) : okStep (g k, a k, b k) (g (k+1), a (k+1), b (k+1)) = true := by
    simp only [okStep]
    cases hg : g (k+1)
    · rw [L.toggle k hg]
      cases g k <;> simp
    · rw [L.reset k hg]
      have : g k = false := by
        cases h : g k
        · rfl
        · have := L.lone k h; rw [hg] at this; cases this
      rw [this]; cases a (k+1) <;> rfl
  intro k
  cases k with
  | zero => exact letter 0
  | succ k =>
    cases k with
    | zero => simp only [hist, okNext, letter, step, Bool.and_self]
    | succ k =>
      simp only [hist, okNext, letter, step, Bool.true_and, Bool.not_eq_true']
      cases hg : g (k+2)
      · simp
      · cases hg' : g k
        · simp
        · cases ha : a k
          · simp
          · cases hb : b k
            · simp
            · have := L.skip k hg' ha hb
              rw [show k+2 = k+2 from rfl, hg] at this
              cases this

theorem search_sound {g a b : Nat → Bool} (L : Law g a b) (clean : ∀ w ∈ banned, ∀ i, ¬ Spells g i w) {test : List Letter → Bool} :
    ∀ n k, search test n (hist g a b k) = true → test (hist g a b (k+n)) = true
  | 0, _, h => h
  | n+1, k, h => by
    have s := List.all_eq_true.mp h _ (mem_allLetters (g k, a k, b k))
    have nb : hasBanned (hist g a b (k+1)) = false := no_banned clean (k+1)
    change (!okNext (hist g a b k) (g k, a k, b k) || hasBanned (hist g a b (k+1)) || search test n (hist g a b (k+1))) = true at s
    rw [okNext_law L k, nb] at s
    simp only [Bool.not_true, Bool.false_or] at s
    rw [show k+(n+1) = (k+1)+n by omega]
    exact search_sound L clean n (k+1) s

/-! ### The closed set, and entry -/

/-- The first twelve cells of the half at the `k`-th white tick are a window of the closed set. -/
def InSet (F : Nat → Nat → Bool) (T k : Nat) : Prop := InTrap closedSet F (T+2*k+1)

theorem Alt.drive {F : Nat → Nat → Bool} {T : Nat} (h : Alt F T) (k n : Nat) : Drive F false true (T+2*k+1) n := by
  intro i _
  refine ⟨?_, ?_⟩
  · have := (h (k+i)).2; rwa [show T+2*(k+i)+1 = T+2*k+1+2*i by omega] at this
  · have := (h (k+i+1)).1; rwa [show T+2*(k+i+1) = T+2*k+1+2*i+1 by omega] at this

/-- **The closed set.** A half in it stays in it, whatever lies beyond. -/
theorem stays {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat} (h : Alt F T) {k : Nat} (s : InSet F T k) (n : Nat) :
    InSet F T (k+n) := by
  have := trap_stays valid01 walk01 free01 wrap01 isTrap01 hF (h.drive k n) s
  rwa [show T+2*k+1+2*n = T+2*(k+n)+1 by omega] at this

/-- The windows of thirteen cells that a half outside can show for ever. -/
def tailWindows : List Nat := [1024, 16, 3268, 2338, 2194, 769, 77, 7364, 4372, 6434]

theorem tail13 : rounds false true 13 17 (widen 12 outside01) = tailWindows := by decide +kernel

/-- Their place in the cycle of four. -/
def phase (x : Nat) : Nat :=
  if x = 77 ∨ x = 769 then 0 else if x = 4372 ∨ x = 3268 ∨ x = 7364 then 1 else if x = 2194 ∨ x = 2338 ∨ x = 6434 then 2 else 3

theorem phase_lt (x : Nat) : phase x < 4 := by unfold phase; (repeat' split) <;> decide

theorem phaseOK : (tailWindows.all fun a => (a.testBit 0 == (phase a == 0)) && tailWindows.all fun b =>
    !(images false true 13 a).contains b || phase b == (phase a + 1) % 4) = true := by decide +kernel

theorem outside_from {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat} (h : Alt F T) (out : ∀ k, ¬ InSet F T k) (k : Nat) :
    code F (T+2*(27+k)+1) 13 ∈ tailWindows := by
  have hd : Drive F false true (T+1) (10+10+(k+2*17)) := by
    have := h.drive 0 (10+10+(k+2*17)); simpa using this
  have no : ¬ InTrap closedSet F (T+1+2*(10+10+(k+2*17))) := fun s => out (20+(k+34)) (by
    unfold InSet
    rwa [show T+2*(20+(k+34))+1 = T+1+2*(10+10+(k+2*17)) by omega])
  have a : Among F (T+1+2*10) (k+2*17) 12 outside01 := fun i hi =>
    outside_before (m := 10) (n := 10) valid01 walk01 free01 wrap01 isTrap01 freeA01 freeB01 first01 middle01 last01
      outsideCodes01 hF hd no i hi
  have d : Drive F false true (T+1+2*10) (k+2*17) := (hd.mono (m := 10+(k+2*17)) (by omega)).shift 10
  have r := among_rounds hF 17 d (among_widen a)
  rw [tail13] at r
  have := r k (Nat.le_refl k)
  rwa [show T+1+2*10+2*17+2*k = T+2*(27+k)+1 by omega] at this

/-- **Every right half beside an alternating column,** of any support, enters the closed set, or from some tick on reads
a kick once in four. -/
theorem enters_or_four {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat} (h : Alt F T) :
    (∃ k, InSet F T k) ∨ ∃ φ N, ∀ k, N ≤ k → gate F T k = decide ((k+φ) % 4 = 0) := by
  by_cases e : ∃ k, InSet F T k
  · exact Or.inl e
  right
  have mem := outside_from hF h (fun k s => e ⟨k, s⟩)
  generalize hc : (fun k => code F (T+2*(27+k)+1) 13) = c at *
  have hc' (k : Nat) : c k = code F (T+2*(27+k)+1) 13 := by rw [← hc]
  have mem' (k : Nat) : c k ∈ tailWindows := by rw [hc']; exact mem k
  have step (k : Nat) : phase (c (k+1)) = (phase (c k) + 1) % 4 := by
    have im := image_mem hF (h.drive (27+k) 1) 13
    rw [show T+2*(27+k)+1+2 = T+2*(27+(k+1))+1 by omega, ← hc', ← hc'] at im
    have row := List.all_eq_true.mp phaseOK _ (mem' k)
    simp only [Bool.and_eq_true] at row
    have cell := List.all_eq_true.mp row.2 _ (mem' (k+1))
    rw [List.contains_iff_mem.mpr im] at cell
    simpa using cell
  have at_ (k : Nat) : phase (c k) = (phase (c 0) + k) % 4 := by
    induction k with
    | zero => have := phase_lt (c 0); omega
    | succ k ih => rw [step k, ih]; omega
  refine ⟨phase (c 0) + 1, 27, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = 27 + j := ⟨k-27, by omega⟩
  have row := List.all_eq_true.mp phaseOK _ (mem' j)
  simp only [Bool.and_eq_true, beq_iff_eq] at row
  have g : gate F T (27+j) = (c j).testBit 0 := by
    rw [hc', code_bit]; simp [gate]
  rw [g, row.1, at_ j]
  show decide ((phase (c 0) + j) % 4 = 0) = decide ((27 + j + (phase (c 0) + 1)) % 4 = 0)
  exact decide_eq_decide.mpr (by omega)

/-! ### What the gate of the closed set reads -/

theorem avoids {T : Tree} {white black : Nat} {d0 d1 : Bool} {trap : List Nat} {F : Nat → Nat → Bool}
    (va : T.valid = true) (ok : walkAll T white black d0 d1 = true) (free : freeFrom white black 0 1 = true)
    (wrap : leaves (fun m => m.testBit 1 == m.testBit 0) T = true) (is : isTrap T trap = true) (hF : IsR30 F) {t : Nat}
    (hd : ∀ n, Drive F d0 d1 t n) (h : InTrap trap F t) {o : Nat} {v : List (Option Bool)}
    (line : wordLine T white black o v = true) (pos : 0 < v.length) (i : Nat)
    (read : ∀ k, k < v.length → fits (v.getD k none) (F (t+2*(i+k)) 1) = true) : False := by
  obtain ⟨x, fx, bx⟩ := trap_row va ok free wrap is hF (hd (i+v.length)) h
  refine bit_word va ok line pos (bx i) (fun k hk => ?_)
  rw [← rows_add, fx (i+k) (by omega) 0 (by omega)]
  exact read k hk

theorem listed01 : (banned.all fun v => lines01.any fun l => l.2 == v.map some) = true := by decide +kernel
theorem banned_pos : ∀ v ∈ banned, 0 < v.length := by decide

/-- **The gate words of the closed set.** None of the ten is read from a white tick in it on. -/
theorem clean_of_set {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat} (h : Alt F T) {k : Nat} (s : InSet F T k) :
    ∀ w ∈ banned, ∀ i, ¬ Spells (fun j => gate F T (k+j)) i w := by
  intro w hw i sp
  obtain ⟨l, hl, e⟩ := List.any_eq_true.mp (List.all_eq_true.mp listed01 w hw)
  have line := List.all_eq_true.mp wordLines01 l hl
  rw [beq_iff_eq.mp e] at line
  refine avoids valid01 walk01 free01 wrap01 isTrap01 hF (h.drive k) s line (by simpa using banned_pos w hw) i (fun j hj => ?_)
  rw [List.length_map] at hj
  have := sp j hj
  simp only [gate] at this
  rw [show T+2*k+1+2*(i+j) = T+2*(k+(i+j))+1 by omega]
  rw [this]
  simp [List.getD, hj, fits]

/-! ### The decoders -/

/-- The six words of nine nets that a kick sits in, at the seventh place. -/
def kickWords : List (List Bool) := [
  [false,false,true,false,true,false,false,true,false], [false,false,true,false,true,false,true,false,false],
  [false,false,true,false,true,false,true,false,true], [false,true,false,false,true,false,false,true,false],
  [true,false,true,false,true,false,false,true,false], [true,false,true,false,true,false,true,false,true]]

def decode (a : Nat → Bool) : Bool :=
  kickWords.any fun w => (List.range 9).all fun i => a i == w.getD i false

theorem decode_ext {a b : Nat → Bool} (h : ∀ i, i < 9 → a i = b i) : decode a = decode b := by
  have e : ∀ w : List Bool, ((List.range 9).all fun i => a i == w.getD i false) = ((List.range 9).all fun i => b i == w.getD i false) := by
    intro w
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro q i hi
      rw [← h i (List.mem_range.mp hi)]; exact q i hi
    · intro q i hi
      rw [h i (List.mem_range.mp hi)]; exact q i hi
  exact congrArg (fun p => kickWords.any p) (funext e)

/-- A history of fourteen letters, latest first, agrees with the decoder at its seventh place. -/
def decodeTest (h : List Letter) : Bool :=
  (h.getD 7 default).1 == decode (fun i => (h.getD (13-i) default).2.1)

theorem decodeCheck : search decodeTest 14 [] = true := by decide +kernel

theorem decoder {g a b : Nat → Bool} (L : Law g a b) (clean : ∀ w ∈ banned, ∀ i, ¬ Spells g i w) : g 6 = decode a := by
  have t := search_sound L clean (test := decodeTest) 14 0 decodeCheck
  have e : hist g a b (0+14) = [(g 13,a 13,b 13),(g 12,a 12,b 12),(g 11,a 11,b 11),(g 10,a 10,b 10),(g 9,a 9,b 9),(g 8,a 8,b 8),
      (g 7,a 7,b 7),(g 6,a 6,b 6),(g 5,a 5,b 5),(g 4,a 4,b 4),(g 3,a 3,b 3),(g 2,a 2,b 2),(g 1,a 1,b 1),(g 0,a 0,b 0)] := rfl
  rw [e] at t
  simp only [decodeTest, List.getD, beq_iff_eq] at t
  have c : decode (fun i => ([(g 13,a 13,b 13),(g 12,a 12,b 12),(g 11,a 11,b 11),(g 10,a 10,b 10),(g 9,a 9,b 9),(g 8,a 8,b 8),
      (g 7,a 7,b 7),(g 6,a 6,b 6),(g 5,a 5,b 5),(g 4,a 4,b 4),(g 3,a 3,b 3),(g 2,a 2,b 2),(g 1,a 1,b 1),(g 0,a 0,b 0)][13-i]?.getD default).2.1) = decode a := by
    apply decode_ext
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [← c]
  exact t

/-- The history of eleven letters agrees with the black rule at its second place. -/
def blackTest (h : List Letter) : Bool :=
  ((h.getD 9 default).1 && !(h.getD 9 default).2.1) == ((h.getD 9 default).2.2 && !(h.getD 5 default).2.2)

theorem blackCheck : search blackTest 11 [] = true := by decide +kernel

theorem blackRule {g a b : Nat → Bool} (L : Law g a b) (clean : ∀ w ∈ banned, ∀ i, ¬ Spells g i w) :
    (g 1 && !a 1) = (b 1 && !b 5) := by
  have t := search_sound L clean (test := blackTest) 11 0 blackCheck
  have e : hist g a b (0+11) = [(g 10,a 10,b 10),(g 9,a 9,b 9),(g 8,a 8,b 8),(g 7,a 7,b 7),(g 6,a 6,b 6),(g 5,a 5,b 5),(g 4,a 4,b 4),
      (g 3,a 3,b 3),(g 2,a 2,b 2),(g 1,a 1,b 1),(g 0,a 0,b 0)] := rfl
  rw [e] at t
  simpa [blackTest, List.getD] using t

/-! ### Every right half: the decoders and the marks -/

theorem leastOf {P : Nat → Prop} (n : Nat) (hn : P n) : ∃ m, P m ∧ ∀ q, q < m → ¬ P q := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ q, q < n ∧ P q
    · obtain ⟨q, hq, pq⟩ := h; exact ih q hq pq
    · exact ⟨n, hn, fun q hq p => h ⟨q, hq, p⟩⟩

section
variable {F : Nat → Nat → Bool} {T : Nat}

/-- **Kicks from the white nets.** Nine nets, at six past white ticks, the kick and two after, tell whether a kick is there. -/
theorem kick_of_white_nets (hF : IsR30 F) (h : Alt F T) {k : Nat} (s : InSet F T k) :
    gate F T (k+6) = decode (fun i => net F T (k+i)) := by
  have d := decoder ((law_of_alt hF h).shift k) (clean_of_set hF h s)
  simpa using d

/-- **An odd kick from two nets.** The net at two successive white ticks is equal exactly at a kick whose net is white.
It needs no closed set. -/
theorem odd_of_equal_nets (hF : IsR30 F) (h : Alt F T) (k : Nat) :
    (net F T k == net F T (k+1)) = (gate F T (k+1) && !net F T (k+1)) :=
  (law_of_alt hF h).equal k

/-- **An odd kick from two black nets,** four black samples apart. -/
theorem odd_of_black_nets (hF : IsR30 F) (h : Alt F T) {k : Nat} (s : InSet F T k) :
    (gate F T (k+1) && !net F T (k+1)) = (blackNet F T (k+1) && !blackNet F T (k+5)) := by
  have d := blackRule ((law_of_alt hF h).shift k) (clean_of_set hF h s)
  simpa using d

/-- After a kick, the number of white ticks to the next one, when that number is `n`. -/
def NextKick (F : Nat → Nat → Bool) (T k n : Nat) : Prop :=
  1 ≤ n ∧ gate F T (k+n) = true ∧ ∀ i, 0 < i → i < n → gate F T (k+i) = false

theorem law_parity {g a b : Nat → Bool} (L : Law g a b) : ∀ (n k : Nat), g (k+(n+1)) = true →
    (∀ i, 0 < i → i < n+1 → g (k+i) = false) → a k = decide ((n+1) % 2 = 0)
  | 0, k, h, _ => by
    have := L.reset k h
    simpa using this
  | n+1, k, h, quiet => by
    have q := quiet 1 (by omega) (by omega)
    have ih := law_parity L n (k+1) (by rw [show k+1+(n+1) = k+(n+1+1) by omega]; exact h)
      (fun i hi hn => by rw [show k+1+i = k+(1+i) by omega]; exact quiet (1+i) (by omega) (by omega))
    have t := L.toggle k q
    rw [ih] at t
    have : a k = !decide ((n+1) % 2 = 0) := by
      cases h1 : a k <;> rw [h1] at t <;> cases h2 : decide ((n+1) % 2 = 0) <;> rw [h2] at t <;> first | rfl | cases t
    rw [this, ← decide_not]
    exact decide_eq_decide.mpr (by omega)

/-- **The net and the return.** A kick whose next kick is `n` white ticks later has net black exactly when `n` is even.
It needs no closed set. -/
theorem net_of_return (hF : IsR30 F) (h : Alt F T) {k n : Nat} (nk : NextKick F T k n) : net F T k = decide (n % 2 = 0) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by have := nk.1; omega⟩
  exact law_parity (law_of_alt hF h) n k nk.2.1 nk.2.2

/-- In the closed set every kick has a next one, two to five white ticks later. -/
theorem next_kick (hF : IsR30 F) (h : Alt F T) {k : Nat} (s : InSet F T k) (g : gate F T k = true) :
    ∃ n, 2 ≤ n ∧ n ≤ 5 ∧ NextKick F T k n := by
  have none1 := (law_of_alt hF h).lone k g
  have ex : ∃ n, 1 ≤ n ∧ n ≤ 5 ∧ gate F T (k+n) = true := by
    apply Classical.byContradiction
    intro no
    refine clean_of_set hF h s [false, false, false, false, false] (by decide) 1 (fun j hj => ?_)
    have j5 : j < 5 := by simpa using hj
    have q : gate F T (k+(1+j)) = false := by
      cases e : gate F T (k+(1+j))
      · rfl
      · exact absurd ⟨1+j, by omega, by omega, e⟩ no
    have table : ([false, false, false, false, false] : List Bool).getD j false = false := by
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
    simp only [table]
    rw [show k+(1+j) = k+(1+j) from rfl]
    exact q
  obtain ⟨n0, l0, u0, w0⟩ := ex
  -- the least kick after k
  obtain ⟨n, hn, least⟩ : ∃ n, (1 ≤ n ∧ gate F T (k+n) = true) ∧ ∀ m, (1 ≤ m ∧ gate F T (k+m) = true) → n ≤ m := by
    obtain ⟨m, hm, small⟩ := leastOf (P := fun n => 1 ≤ n ∧ gate F T (k+n) = true) n0 ⟨l0, w0⟩
    exact ⟨m, hm, fun q hq => Nat.le_of_not_lt fun l => small q l hq⟩
  have n1 : n ≠ 1 := by
    intro e; subst e; rw [none1] at hn; cases hn.2
  refine ⟨n, by omega, ?_, by omega, hn.2, fun i hi hin => ?_⟩
  · have := least n0 ⟨l0, w0⟩; omega
  · cases e : gate F T (k+i)
    · rfl
    · have := least i ⟨hi, e⟩
      omega

/-- **The odd kick.** In the closed set a kick has white net exactly when the next one is three or five white ticks later. -/
theorem odd_iff (hF : IsR30 F) (h : Alt F T) {k : Nat} (s : InSet F T k) (g : gate F T k = true) :
    net F T k = false ↔ ∃ n, (n = 3 ∨ n = 5) ∧ NextKick F T k n := by
  obtain ⟨n, l, u, nk⟩ := next_kick hF h s g
  have e := net_of_return hF h nk
  constructor
  · intro z
    rw [e] at z
    have : n = 3 ∨ n = 5 := by
      have : ¬ n % 2 = 0 := by simpa using z
      omega
    exact ⟨n, this, nk⟩
  · rintro ⟨m, hm, mk⟩
    rw [net_of_return hF h mk]
    rcases hm with rfl | rfl <;> rfl

end

/-! ### Periodicity passes between the streams -/

/-- A kick whose net is white: its next kick is an odd number of white ticks later (`odd_iff`). -/
def oddKick (F : Nat → Nat → Bool) (T k : Nat) : Bool := gate F T k && !net F T k

section
variable {F : Nat → Nat → Bool} {T : Nat}

/-- A difference that is constant under a shift repeats after twice the shift. -/
theorem periodic_of_equalities {f : Nat → Bool} (per : EventuallyPeriodic (fun k => f k == f (k+1))) : EventuallyPeriodic f := by
  obtain ⟨L, p, hp, per⟩ := per
  have flip (n : Nat) (hn : L ≤ n) : xor (f (n+1+p)) (f (n+1)) = xor (f (n+p)) (f n) := by
    have q : (f (n+p) == f (n+p+1)) = (f n == f (n+1)) := per n hn
    rw [show n+p+1 = n+1+p by omega] at q
    revert q
    cases f (n+p) <;> cases f (n+1+p) <;> cases f n <;> cases f (n+1) <;> decide
  have same (m n : Nat) (hn : L ≤ n) : xor (f (n+m+p)) (f (n+m)) = xor (f (n+p)) (f n) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      have := flip (n+m) (by omega)
      rw [show n+(m+1) = n+m+1 by omega, this, ih]
  refine ⟨L, 2*p, by omega, fun n hn => ?_⟩
  have e := same p n hn
  rw [show n+p+p = n+2*p by omega] at e
  revert e
  cases f (n+2*p) <;> cases f (n+p) <;> cases f n <;> decide

/-- If the net on the white ticks is eventually periodic, so is the gate. -/
theorem gate_periodic_of_net (hF : IsR30 F) (h : Alt F T) {K : Nat} (s : InSet F T K) (per : EventuallyPeriodic (net F T)) :
    EventuallyPeriodic (gate F T) := by
  obtain ⟨L, p, hp, per⟩ := per
  have inset (k : Nat) (hk : K ≤ k) : InSet F T k := by
    have := stays hF h s (k-K)
    rwa [show K+(k-K) = k by omega] at this
  refine ⟨K+L+6, p, hp, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j+6 := ⟨k-6, by omega⟩
  have a := kick_of_white_nets hF h (inset j (by omega))
  have b := kick_of_white_nets hF h (inset (j+p) (by omega))
  rw [show j+6+p = j+p+6 by omega, b, a]
  exact decode_ext (fun i _ => by
    rw [show j+p+i = j+i+p by omega]; exact per (j+i) (by omega))

/-- If the gate is eventually periodic, so is the net on the white ticks. -/
theorem net_periodic_of_gate (hF : IsR30 F) (h : Alt F T) {K : Nat} (s : InSet F T K) (per : EventuallyPeriodic (gate F T)) :
    EventuallyPeriodic (net F T) := by
  obtain ⟨L, p, hp, per⟩ := per
  have inset (k : Nat) (hk : K ≤ k) : InSet F T k := by
    have := stays hF h s (k-K)
    rwa [show K+(k-K) = k by omega] at this
  -- every white tick in the set has a kick at most five ticks later
  have soon (k : Nat) (hk : K ≤ k) : ∃ n, NextKick F T k n := by
    apply Classical.byContradiction
    intro no
    refine clean_of_set hF h (inset k hk) [false, false, false, false, false] (by decide) 1 (fun j hj => ?_)
    have j5 : j < 5 := by simpa using hj
    have table : ([false, false, false, false, false] : List Bool).getD j false = false := by
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
    simp only [table]
    cases e : gate F T (k+(1+j))
    · rfl
    · exfalso
      obtain ⟨m, hm, small⟩ := leastOf (P := fun n => 1 ≤ n ∧ gate F T (k+n) = true) (1+j) ⟨by omega, e⟩
      exact no ⟨m, hm.1, hm.2, fun i hi him => by
        cases g : gate F T (k+i)
        · rfl
        · exact absurd ⟨hi, g⟩ (small i him)⟩
  refine ⟨K+L, p, hp, fun k hk => ?_⟩
  obtain ⟨n, nk⟩ := soon k (by omega)
  have nk' : NextKick F T (k+p) n := by
    refine ⟨nk.1, ?_, fun i hi him => ?_⟩
    · rw [show k+p+n = k+n+p by omega, per (k+n) (by omega)]; exact nk.2.1
    · rw [show k+p+i = k+i+p by omega, per (k+i) (by omega)]; exact nk.2.2 i hi him
  rw [net_of_return hF h nk', net_of_return hF h nk]

/-- If the odd kicks are eventually periodic, so is the net on the white ticks. No closed set is needed. -/
theorem net_periodic_of_odd (hF : IsR30 F) (h : Alt F T) (per : EventuallyPeriodic (oddKick F T)) : EventuallyPeriodic (net F T) := by
  obtain ⟨L, p, hp, per⟩ := per
  apply periodic_of_equalities
  refine ⟨L, p, hp, fun k hk => ?_⟩
  simp only [odd_of_equal_nets hF h]
  rw [show k+p+1 = k+1+p by omega]
  exact per (k+1) (by omega)

/-- If the net on the white ticks is eventually periodic, so are the odd kicks. -/
theorem odd_periodic_of_net (hF : IsR30 F) (h : Alt F T) (per : EventuallyPeriodic (net F T)) : EventuallyPeriodic (oddKick F T) := by
  obtain ⟨L, p, hp, per⟩ := per
  refine ⟨L+1, p, hp, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
  rw [show j+1+p = j+p+1 by omega]
  have a := odd_of_equal_nets hF h (j+p)
  have b := odd_of_equal_nets hF h j
  show (gate F T (j+p+1) && !net F T (j+p+1)) = (gate F T (j+1) && !net F T (j+1))
  rw [← a, ← b, show j+p+1 = j+1+p by omega, per j (by omega), per (j+1) (by omega)]

/-- If the net on the black ticks is eventually periodic, so are the odd kicks. -/
theorem odd_periodic_of_black (hF : IsR30 F) (h : Alt F T) {K : Nat} (s : InSet F T K) (per : EventuallyPeriodic (blackNet F T)) :
    EventuallyPeriodic (oddKick F T) := by
  obtain ⟨L, p, hp, per⟩ := per
  have inset (k : Nat) (hk : K ≤ k) : InSet F T k := by
    have := stays hF h s (k-K)
    rwa [show K+(k-K) = k by omega] at this
  refine ⟨K+L+1, p, hp, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
  have a := odd_of_black_nets hF h (inset (j+p) (by omega))
  have b := odd_of_black_nets hF h (inset j (by omega))
  show (gate F T (j+1+p) && !net F T (j+1+p)) = (gate F T (j+1) && !net F T (j+1))
  rw [show j+1+p = j+p+1 by omega, a, b, show j+p+1 = j+1+p by omega, per (j+1) (by omega),
    show j+p+5 = j+5+p by omega, per (j+5) (by omega)]

/-- **The three streams.** Beside an alternating column every right half in the closed set has an eventually periodic gate, white
net and odd kicks together; and if its black net is eventually periodic, so are they. -/
theorem periodic_together (hF : IsR30 F) (h : Alt F T) {K : Nat} (s : InSet F T K) :
    (EventuallyPeriodic (gate F T) ↔ EventuallyPeriodic (net F T)) ∧
    (EventuallyPeriodic (net F T) ↔ EventuallyPeriodic (oddKick F T)) ∧
    (EventuallyPeriodic (blackNet F T) → EventuallyPeriodic (gate F T)) :=
  ⟨⟨net_periodic_of_gate hF h s, gate_periodic_of_net hF h s⟩, ⟨odd_periodic_of_net hF h, net_periodic_of_odd hF h⟩,
    fun per => gate_periodic_of_net hF h s (net_periodic_of_odd hF h (odd_periodic_of_black hF h s per))⟩

end

/-! ### Right halves driven from the clock -/

/-- The right half `R`, driven by the column that is black at even ticks, alternates from the start. -/
theorem alt_drv (R : Nat → Bool) : Alt (drv altCol R) 0 := by
  intro k
  rw [drv_col0, drv_col0]
  refine ⟨?_, ?_⟩
  · rw [show 0+2*k = 2*k by omega]; exact Rule30PeriodTwoSideways.altCol_even k
  · rw [show 0+2*k+1 = 2*k+1 by omega]; exact Rule30PeriodTwoSideways.altCol_odd k

/-- **Every right half,** of any support, beside the alternating column enters the closed set, or from some tick on reads
a kick once in four. -/
theorem every_half (R : Nat → Bool) : (∃ k, InSet (drv altCol R) 0 k) ∨
    ∃ φ N, ∀ k, N ≤ k → gate (drv altCol R) 0 k = decide ((k+φ) % 4 = 0) :=
  enters_or_four (drv_isR30 _ _) (alt_drv R)

/-! ### The hypothetical alternating tail of the single cell -/

/-- The centre alternates from `T`, black first. -/
def AltCenter (T : Nat) : Prop := ∀ k, cell (T+2*k) 0 = true ∧ cell (T+2*k+1) 0 = false

theorem AltCenter.alt {T : Nat} (h : AltCenter T) : Alt trueRight T := fun k => ⟨(h k).1, (h k).2⟩

/-- Masked Jen: the kicks are not eventually periodic. -/
theorem gate_not_periodic {T : Nat} (h : AltCenter T) : ¬ EventuallyPeriodic (gate trueRight T) := by
  rintro ⟨L, p, hp, per⟩
  have white (t : Nat) (ht : T ≤ t) (c : cell t 0 = false) : ∃ k, t = T+2*k+1 := by
    rcases Nat.lt_or_ge ((t-T) % 2) 1 with e | e
    · exfalso
      obtain ⟨k, rfl⟩ : ∃ k, t = T+2*k := ⟨(t-T)/2, by omega⟩
      rw [(h k).1] at c; cases c
    · exact ⟨(t-T)/2, by omega⟩
  refine masked_jen_center (T := T) (P := 2*p) (by omega) (fun t ht => ?_) (T+2*L+1) (fun t ht c => ?_)
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, t = T+2*k ∨ t = T+2*k+1 := ⟨(t-T)/2, by omega⟩
    · rw [show T+2*k+2*p = T+2*(k+p) by omega, (h _).1, (h _).1]
    · rw [show T+2*k+1+2*p = T+2*(k+p)+1 by omega, (h _).2, (h _).2]
  · obtain ⟨k, rfl⟩ := white t (by omega) c
    have := per k (by omega)
    rw [show T+2*k+1+2*p = T+2*(k+p)+1 by omega]
    exact this

/-- **Entry of the single cell.** From some white tick on, the window of the single cell is in the closed set. -/
theorem single_enters {T : Nat} (h : AltCenter T) : ∃ K, InSet trueRight T K := by
  rcases enters_or_four trueRight_isR30 h.alt with s | ⟨φ, N, f⟩
  · exact s
  · exfalso
    refine gate_not_periodic h ⟨N, 4, by omega, fun k hk => ?_⟩
    rw [f (k+4) (by omega), f k hk]
    congr 1
    apply propext
    omega

/-- **White net.** If the centre alternates for ever, the net on the white ticks is not eventually periodic. -/
theorem white_net_aperiodic {T : Nat} (h : AltCenter T) : ¬ EventuallyPeriodic (net trueRight T) := fun per => by
  obtain ⟨K, s⟩ := single_enters h
  exact gate_not_periodic h (gate_periodic_of_net trueRight_isR30 h.alt s per)

/-- **Odd kicks.** If the centre alternates for ever, the kicks whose next one is three or five white ticks later are not
eventually periodic. -/
theorem odd_kicks_aperiodic {T : Nat} (h : AltCenter T) : ¬ EventuallyPeriodic (oddKick trueRight T) := fun per =>
  white_net_aperiodic h (net_periodic_of_odd trueRight_isR30 h.alt per)

/-- **Black net.** If the centre alternates for ever, the net on the black ticks is not eventually periodic. -/
theorem black_net_aperiodic {T : Nat} (h : AltCenter T) : ¬ EventuallyPeriodic (blackNet trueRight T) := fun per => by
  obtain ⟨K, s⟩ := single_enters h
  exact odd_kicks_aperiodic h (odd_periodic_of_black trueRight_isR30 h.alt s per)

/-! ### Lowry's net and shell -/

/-- Lowry's net and shell (`Rule30SourceArrivals`). -/
abbrev lowryNet := Rule30SourceArrivals.net
abbrev lowryShell := Rule30SourceArrivals.shell

/-- On a white tick whose next tick is black, Lowry's net is the first cell exclusive-or the second. -/
theorem lowry_white (t : Nat) (w : cell t 0 = false) (b : cell (t+1) 0 = true) : lowryNet t = xor (cell t 1) (cell t 2) := by
  have step : cell (t+1) 0 = rule (cell t (-1)) (cell t 0) (cell t 1) := rfl
  have next : cell (t+1) 1 = rule (cell t 0) (cell t 1) (cell t 2) := rfl
  show xor (cell t (-1) && !cell t 0) (xor (cell t 1 && !cell t 2) (cell (t+1) 0 && !cell (t+1) 1)) = _
  rw [w] at step next
  have b' := b
  rw [step] at b'
  rw [w, b, next]
  exact (by decide : ∀ L x y : Bool, rule L false x = true → xor (L && !false) (xor (x && !y) (true && !rule false x y)) = xor x y)
    _ _ _ b'

/-- On a black tick whose next tick is white, Lowry's net is the first cell without the second. -/
theorem lowry_black (t : Nat) (b : cell t 0 = true) (w : cell (t+1) 0 = false) : lowryNet t = (cell t 1 && !cell t 2) := by
  show xor (cell t (-1) && !cell t 0) (xor (cell t 1 && !cell t 2) (cell (t+1) 0 && !cell (t+1) 1)) = _
  rw [b, w]
  cases cell t (-1) <;> cases cell t 1 <;> cases cell t 2 <;> rfl

/-- Lowry's identity at two ticks. -/
theorem two_step (t : Nat) : cell (t+2) 0 = xor (lowryShell t) (lowryNet t) := Rule30SourceArrivals.two_step t

section
variable {T : Nat}

/-- Lowry's net at the white and the black ticks of an alternating centre is the net of its right half. -/
theorem lowry_at_white (h : AltCenter T) (k : Nat) : lowryNet (T+2*k+1) = net trueRight T k := by
  have b := (h (k+1)).1
  rw [show T+2*(k+1) = T+2*k+1+1 by omega] at b
  exact lowry_white _ (h k).2 b

theorem lowry_at_black (h : AltCenter T) (k : Nat) : lowryNet (T+2*k+2) = blackNet trueRight T k := by
  have b := (h (k+1)).1
  have w := (h (k+1)).2
  rw [show T+2*(k+1) = T+2*k+2 by omega] at b
  rw [show T+2*(k+1)+1 = T+2*k+2+1 by omega] at w
  exact lowry_black _ b w

theorem shell_at_white (h : AltCenter T) (k : Nat) : lowryShell (T+2*k+1) = net trueRight T k := by
  have e := two_step (T+2*k+1)
  rw [show T+2*k+1+2 = T+2*(k+1)+1 by omega, (h (k+1)).2, lowry_at_white h k] at e
  exact (by decide : ∀ a b : Bool, false = xor a b → a = b) _ _ e

theorem shell_at_black (h : AltCenter T) (k : Nat) : lowryShell (T+2*k+2) = !blackNet trueRight T k := by
  have e := two_step (T+2*k+2)
  rw [show T+2*k+2+2 = T+2*(k+2) by omega, (h (k+2)).1, lowry_at_black h k] at e
  exact (by decide : ∀ a b : Bool, true = xor a b → a = !b) _ _ e

/-- **Both phases of Lowry's net and shell.** If the centre of the single cell alternates from `T`, black first, then Lowry's net
and his shell are not eventually periodic on the white ticks, nor on the black ones. -/
theorem both_phases (h : AltCenter T) :
    ¬ EventuallyPeriodic (fun k => lowryNet (T+2*k+1)) ∧ ¬ EventuallyPeriodic (fun k => lowryNet (T+2*k+2)) ∧
    ¬ EventuallyPeriodic (fun k => lowryShell (T+2*k+1)) ∧ ¬ EventuallyPeriodic (fun k => lowryShell (T+2*k+2)) := by
  have eqw : (fun k => lowryNet (T+2*k+1)) = net trueRight T := funext (lowry_at_white h)
  have eqb : (fun k => lowryNet (T+2*k+2)) = blackNet trueRight T := funext (lowry_at_black h)
  have eqsw : (fun k => lowryShell (T+2*k+1)) = net trueRight T := funext (shell_at_white h)
  have eqsb : (fun k => lowryShell (T+2*k+2)) = fun k => !blackNet trueRight T k := funext (shell_at_black h)
  refine ⟨by rw [eqw]; exact white_net_aperiodic h, by rw [eqb]; exact black_net_aperiodic h,
    by rw [eqsw]; exact white_net_aperiodic h, ?_⟩
  rw [eqsb]
  rintro ⟨L, p, hp, per⟩
  refine black_net_aperiodic h ⟨L, p, hp, fun k hk => ?_⟩
  have := per k hk
  cases h1 : blackNet trueRight T (k+p) <;> cases h2 : blackNet trueRight T k <;> simp_all

/-- **The return.** In the alternating tail of the single cell, Lowry's net at two successive white ticks is equal exactly when the
second is an odd kick: a kick whose next kick is three or five white ticks later. -/
theorem lowry_odd_return (h : AltCenter T) (k : Nat) :
    (lowryNet (T+2*k+1) == lowryNet (T+2*(k+1)+1)) = oddKick trueRight T (k+1) := by
  rw [lowry_at_white h, lowry_at_white h]
  exact odd_of_equal_nets trueRight_isR30 h.alt k

end

/-! ### Every right half: periodic together, and why the nine nets need the closed set -/

/-- If the gate eventually kicks once in four white samples, the white net
alternates and the odd-kick indicator vanishes on that same tail. -/
theorem four_tail {F : Nat → Nat → Bool} {T φ N : Nat} (hF : IsR30 F) (h : Alt F T)
    (four : ∀ k, N ≤ k → gate F T k = decide ((k+φ)%4 = 0)) (k : Nat) (hk : N ≤ k) :
    net F T k = decide ((k+φ)%2 = 0) ∧ oddKick F T k = false := by
  let d := 4 - (k+φ)%4
  have next : NextKick F T k d := by
    refine ⟨by dsimp [d]; omega, ?_, ?_⟩
    · rw [four (k+d) (by omega)]
      apply decide_eq_true; dsimp [d]; omega
    · intro i hi hd
      rw [four (k+i) (by omega)]
      apply decide_eq_false; dsimp [d] at hd; omega
  have parity := net_of_return hF h next
  have phase : d % 2 = (k+φ)%2 := by dsimp [d]; omega
  rw [phase] at parity
  refine ⟨parity, ?_⟩
  unfold oddKick
  rw [four k hk, parity]
  by_cases kick : (k+φ)%4 = 0
  · simp [kick, show (k+φ)%2 = 0 by omega]
  · simp [kick]

/-- For every right half under an alternating boundary, eventual periodicity
of the gate, white net and odd-kick indicator is equivalent. Periodicity of the
black net also suffices. -/
theorem periodic_together_of_alt {F : Nat → Nat → Bool} {T : Nat} (hF : IsR30 F) (h : Alt F T) :
    (EventuallyPeriodic (gate F T) ↔ EventuallyPeriodic (net F T)) ∧
    (EventuallyPeriodic (net F T) ↔ EventuallyPeriodic (oddKick F T)) ∧
    (EventuallyPeriodic (blackNet F T) → EventuallyPeriodic (gate F T)) := by
  rcases enters_or_four hF h with ⟨k, inside⟩ | ⟨φ, N, four⟩
  · exact periodic_together hF h inside
  · have G : EventuallyPeriodic (gate F T) := by
      refine ⟨N, 4, by decide, fun k hk => ?_⟩
      rw [four k hk, four (k+4) (by omega), show (k+4+φ)%4 = (k+φ)%4 by omega]
    have tail := four_tail hF h four
    have A : EventuallyPeriodic (net F T) := by
      refine ⟨N, 2, by decide, fun k hk => ?_⟩
      rw [(tail k hk).1, (tail (k+2) (by omega)).1, show (k+2+φ)%2 = (k+φ)%2 by omega]
    have O := odd_periodic_of_net hF h A
    exact ⟨⟨fun _ => A, fun _ => G⟩, ⟨fun _ => O, fun _ => A⟩, fun _ => G⟩

/-- Black-first alternating evolution from a finite row. Bit zero encodes site one. -/
def seedRun (x : Nat) := drv altCol (fun p => x.testBit (p-1))

private theorem seed_cell (x k j : Nat) :
    seedRun x (0+2*k+1) (j+1) = (rows false true (step true x) k).testBit j := by
  have rule : IsR30 (seedRun x) := drv_isR30 _ _
  have clock := alt_drv (fun p => x.testBit (p-1))
  have white : Fits (seedRun x) 1 (step true x) (j+1+2*k) := by
    apply fits_step rule (t := 0) (clock 0).1
    intro i _
    rw [seedRun, drv_init _ _ _ (by omega), Nat.add_sub_cancel]
  have f := fits_rows rule (t := 1) (n := k) (L := j+1) (clock.drive 0 k) white k (Nat.le_refl k)
  simpa only [show 0+2*k+1 = 1+2*k by omega] using (f j (by omega)).symm

/-- The two finite rows read the same nine white nets, but the kick at sample six differs. -/
theorem nine_collision :
    (∀ i : Fin 9, net (seedRun 56) 0 i = net (seedRun 9) 0 i) ∧
    gate (seedRun 56) 0 6 = false ∧ gate (seedRun 9) 0 6 = true := by
  have n (x k : Nat) : net (seedRun x) 0 k =
      xor ((rows false true (step true x) k).testBit 0) ((rows false true (step true x) k).testBit 1) := by
    unfold net
    rw [seed_cell x k 0, seed_cell x k 1]
  have g (x k : Nat) : gate (seedRun x) 0 k = (rows false true (step true x) k).testBit 0 :=
    seed_cell x k 0
  simp only [n, g]
  decide +kernel

theorem no_unrestricted_nine : ¬ ∃ read : (Fin 9 → Bool) → Bool, ∀ x,
    read (fun i => net (seedRun x) 0 i) = gate (seedRun x) 0 6 := by
  rintro ⟨read, correct⟩
  obtain ⟨same, off, on⟩ := nine_collision
  have e := congrArg read (funext same)
  rw [correct 56, correct 9, off, on] at e
  contradiction

end Ruliology.CellularAutomata.Rule30AlternatingArrivals
