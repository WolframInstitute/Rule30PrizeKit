module

public import Ruliology.CellularAutomata.Rule30Certificates.StripeMeeting

/-!
# Stripe relations and first meetings of finite Rule 30 rows

In the moving integer frame Phi(a)=a XOR((a<<1) OR(a<<2)), the center is
bit c+t at time t. Two rows are stripe-related if they are equal or share a
cut j<=c, both lower prefixes lie in 0*(1|11)(01)*, bit j+1 is white in both,
and all higher bits agree.

Stripe-related rows have identical entire center traces: the relation is
preserved after two steps, and the first two center observations agree.
Conversely, if rows become stripe-related at any finite time while all
preceding center observations agree, they were related at time zero or one.
All row sizes, center indices and finite times are quantified without bounds.

The proof connects finite certificates to arbitrary input lengths, exact
integer bit updates, typed packing, common-cut parser semantics and the
stripe grammar. It does not prove completeness for equal infinite traces,
numerical-normalizer equivalence, EdgeObservable, or a prize problem.
The component module names in some proof comments refer to the accompanying
research sources, from which these proof bodies are combined unchanged.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30StripeMeeting

theorem all_of_member {p : StateTree} {f : Nat → Bool}
    (ha : allNodes p f = true) {s : Nat} (hm : member p s = true) : f s = true := by
  induction p generalizing s with
  | nil => simp [member] at hm
  | node k l r ihl ihr =>
      have hk := (Bool.and_eq_true_iff.mp ha).1
      have hc := (Bool.and_eq_true_iff.mp ha).2
      by_cases he : s = k
      · simpa only [he] using hk
      · by_cases hl : s < k
        · apply ihl (Bool.and_eq_true_iff.mp hc).1
          simpa [member, he, hl] using hm
        · apply ihr (Bool.and_eq_true_iff.mp hc).2
          simpa [member, he, hl] using hm

theorem initial_member : member pool initial = true := (Bool.and_eq_true_iff.mp checked).1

theorem good_of_member {s : Nat} (hs : member pool s = true) : endGood s = true := by
  have all := (Bool.and_eq_true_iff.mp checked).2
  exact (Bool.and_eq_true_iff.mp (all_of_member all hs)).2

theorem step_member {s v e : Nat} (hs : member pool s = true) (hv : v < 8)
    (he : step s v = some e) : member pool e = true := by
  have all := (Bool.and_eq_true_iff.mp checked).2
  have hc := (Bool.and_eq_true_iff.mp (all_of_member all hs)).1
  have h := List.all_eq_true.mp hc v (List.mem_range.mpr hv)
  rw [he] at h
  exact h

def run (s : Nat) : List Nat → Option Nat
  | [] => some s
  | v :: vs => (step s v).bind (fun e => run e vs)

theorem run_member {word : List Nat} {s e : Nat} (hs : member pool s = true)
    (hv : ∀ v, v ∈ word → v < 8) (hr : run s word = some e) : member pool e = true := by
  induction word generalizing s with
  | nil =>
      simp only [run, Option.some.injEq] at hr
      subst hr
      exact hs
  | cons v vs ih =>
      cases hstep : step s v with
      | none => simp [run, hstep] at hr
      | some next =>
          have hnext := step_member hs (hv v (by simp)) hstep
          apply ih hnext
          · intro u hu
            exact hv u (by simp [hu])
          · simpa only [run, hstep, Option.bind_some] using hr

/-- Every length of valid input stays outside the machine's forbidden end set.
The numerical-normalization interpretation is a separate obligation. -/
theorem all_input_lengths_safe (word : List Nat)
    (hv : ∀ v, v ∈ word → v < 8) {e : Nat} (hr : run initial word = some e) :
    endGood e = true :=
  good_of_member (run_member initial_member hv hr)

def Phi (a : Nat) : Nat := a ^^^ ((a <<< 1) ||| (a <<< 2))

def before (a i k : Nat) : Bool := decide (k < i) && a.testBit (i - (k+1))

theorem Phi_testBit (a i : Nat) :
    (Phi a).testBit i = xor (a.testBit i) (before a i 0 || before a i 1) := by
  have h1 : decide (1 ≤ i) = decide (0 < i) := by
    by_cases h : 1 ≤ i
    · have h' : 0 < i := by omega
      simp [h, h']
    · have h' : ¬ 0 < i := by omega
      simp [h, h']
  have h2 : decide (2 ≤ i) = decide (1 < i) := by
    by_cases h : 2 ≤ i
    · have h' : 1 < i := by omega
      simp [h, h']
    · have h' : ¬ 1 < i := by omega
      simp [h, h']
  simp only [Phi, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, before,
    h1, h2, Nat.zero_add]

def pack4 (b0 b1 b2 b3 : Bool) : Nat :=
  b0.toNat ||| (b1.toNat <<< 1) ||| (b2.toNat <<< 2) ||| (b3.toNat <<< 3)

theorem pack4_bit0 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 0 = b0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit1 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 1 = b1 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit2 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 2 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_bit3 (b0 b1 b2 b3 : Bool) : (pack4 b0 b1 b2 b3).testBit 3 = b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_lt (b0 b1 b2 b3 : Bool) : pack4 b0 b1 b2 b3 < 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem pack4_shift (b0 b1 b2 b3 x : Bool) :
    pack4 x b0 b1 b2 = (2 * pack4 b0 b1 b2 b3 + x.toNat) % 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases x <;> decide

def history (a i : Nat) : Nat := pack4 (before a i 0) (before a i 1)
  (before a i 2) (before a i 3)

theorem history_lt (a i : Nat) : history a i < 16 := pack4_lt _ _ _ _

theorem history_bit0 (a i : Nat) : (history a i).testBit 0 = before a i 0 := pack4_bit0 _ _ _ _
theorem history_bit1 (a i : Nat) : (history a i).testBit 1 = before a i 1 := pack4_bit1 _ _ _ _
theorem history_bit2 (a i : Nat) : (history a i).testBit 2 = before a i 2 := pack4_bit2 _ _ _ _
theorem history_bit3 (a i : Nat) : (history a i).testBit 3 = before a i 3 := pack4_bit3 _ _ _ _

theorem before_succ_zero (a i : Nat) : before a (i+1) 0 = a.testBit i := by
  simp [before]

theorem before_succ_succ (a i k : Nat) : before a (i+1) (k+1) = before a i k := by
  by_cases h : k < i
  · have h' : k+1 < i+1 := by omega
    have hi : (i+1)-(k+1+1) = i-(k+1) := by omega
    simp [before, h, h', hi]
  · have h' : ¬ k+1 < i+1 := by omega
    simp [before, h, h']

theorem history_zero (a : Nat) : history a 0 = 0 := by simp [history, before, pack4]

theorem history_succ (a i : Nat) :
    history a (i+1) = (2 * history a i + (a.testBit i).toNat) % 16 := by
  unfold history
  rw [before_succ_zero, before_succ_succ a i 0, before_succ_succ a i 1,
    before_succ_succ a i 2]
  exact pack4_shift _ _ _ _ _

theorem before_of_lt (a i k : Nat) (hk : k < i) :
    before a i k = a.testBit (i-(k+1)) := by simp [before, hk]

theorem before_shift (a i k l : Nat) (hk : k < i) :
    before a (i-(k+1)) l = before a i (k+l+1) := by
  by_cases hl : l < i-(k+1)
  · have hr : k+l+1 < i := by omega
    simp only [before, hl, hr, decide_true, Bool.true_and]
    congr 1
    omega
  · have hr : ¬ k+l+1 < i := by omega
    simp [before, hl, hr]

theorem before_Phi (a i k : Nat) :
    before (Phi a) i k = xor (before a i k)
      (before a i (k+1) || before a i (k+2)) := by
  by_cases hk : k < i
  · rw [before_of_lt _ _ _ hk, Phi_testBit,
      before_shift a i k 0 hk, before_shift a i k 1 hk, before_of_lt a i k hk]
  · have h1 : ¬ k+1 < i := by omega
    have h2 : ¬ k+2 < i := by omega
    simp [before, hk, h1, h2]

theorem first_exact (a i : Nat) :
    (Phi a).testBit i = first (history a i) (a.testBit i) := by
  rw [Phi_testBit]
  simp only [first, history_bit0, history_bit1]

theorem second_exact (a i : Nat) :
    (Phi (Phi a)).testBit i = second (history a i) (a.testBit i) := by
  rw [Phi_testBit, first_exact, before_Phi, before_Phi]
  simp only [second, first, history_bit0, history_bit1, history_bit2, history_bit3,
    Nat.zero_add]

structure View where
  e0 : Nat
  e1 : Nat
  e2 : Nat
  ha : Nat
  hb : Nat
  code : Nat

def View.Valid (v : View) : Prop := v.e0 < 200 ∧ v.e1 < 200 ∧ v.e2 < 200 ∧
  v.ha < 16 ∧ v.hb < 16 ∧ v.code ≤ 4

def View.encode (v : View) : Nat := v.e0 + (v.e1 <<< 8) + (v.e2 <<< 16) +
  (v.ha <<< 24) + (v.hb <<< 28) + (v.code <<< 32)

theorem View.decode_encode (v : View) (h : v.Valid) :
    v.encode % 256 = v.e0 ∧ (v.encode >>> 8) % 256 = v.e1 ∧
    (v.encode >>> 16) % 256 = v.e2 ∧ (v.encode >>> 24) % 16 = v.ha ∧
    (v.encode >>> 28) % 16 = v.hb ∧ v.encode >>> 32 = v.code := by
  obtain ⟨h0,h1,h2,ha,hb,hc⟩ := h
  unfold View.encode
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  repeat' constructor <;> omega

def symbol (a b marker : Bool) : Nat := a.toNat + 2 * b.toNat + 4 * marker.toNat

theorem symbol_lt (a b marker : Bool) : symbol a b marker < 8 := by
  cases a <;> cases b <;> cases marker <;> decide

theorem symbol_bits (a b marker : Bool) :
    (symbol a b marker).testBit 0 = a ∧ (symbol a b marker).testBit 1 = b ∧
    (symbol a b marker).testBit 2 = marker := by
  cases a <;> cases b <;> cases marker <;> decide

theorem tailNext_lt (s : Nat) (b : Bool) : tailNext s b < 5 := by
  unfold tailNext
  split <;> decide

theorem bool_nat_le (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem relStep_lt (e : Nat) (a b allow : Bool) : relStep e a b allow < 200 := by
  let ta := tailNext ((e / 8) / 5) a
  let tb := tailNext ((e / 8) % 5) b
  let valid := (e.testBit 0 && (a == b)) || (e.testBit 1 && !a && !b)
  let pending := allow && a && b && (ta == 1 || ta == 3) && (tb == 1 || tb == 3)
  let ident := e.testBit 2 && (a == b)
  change 8 * (5 * ta + tb) + 4 * ident.toNat + 2 * pending.toNat + valid.toNat < 200
  have ht : ta < 5 := tailNext_lt _ _
  have hu : tb < 5 := tailNext_lt _ _
  have hi := bool_nat_le ident
  have hp := bool_nat_le pending
  have hv := bool_nat_le valid
  omega

def nextCode (old : Nat) (marker : Bool) : Nat :=
  if marker then 1 else if old == 0 then 0 else min 4 (old+1)

theorem nextCode_le (old : Nat) (marker : Bool) : nextCode old marker ≤ 4 := by
  unfold nextCode
  split
  · decide
  · split
    · decide
    · exact Nat.min_le_left _ _

def View.advance (v : View) (a b marker : Bool) : Option View :=
  if marker && v.code != 0 then none else
  let code := nextCode v.code marker
  let a1 := first v.ha a
  let b1 := first v.hb b
  if (code == 1 && a != b) || (code == 2 && a1 != b1) then none else
  some ⟨relStep v.e0 a b (code == 0 || code ≤ 1),
    relStep v.e1 a1 b1 (code == 0 || code ≤ 2),
    relStep v.e2 (second v.ha a) (second v.hb b) (code == 0 || code ≤ 3),
    (2 * v.ha + a.toNat) % 16, (2 * v.hb + b.toNat) % 16, code⟩

theorem View.encode_advance (v : View) (hv : v.Valid) (a b marker : Bool) :
    step v.encode (symbol a b marker) = (v.advance a b marker).map View.encode := by
  obtain ⟨h0,h1,h2,ha,hb,hc⟩ := v.decode_encode hv
  obtain ⟨s0,s1,s2⟩ := symbol_bits a b marker
  have hcode : (if marker then 1 else if v.code == 0 then 0 else min 4 (v.code+1)) =
      nextCode v.code marker := rfl
  simp only [step, View.advance, h0,h1,h2,ha,hb,hc,s0,s1,s2,hcode]
  split
  · rfl
  · split <;> rfl

theorem View.advance_valid {v w : View} {a b marker : Bool}
    (h : v.advance a b marker = some w) : w.Valid := by
  unfold View.advance at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · have he := Option.some.inj h
      subst w
      exact ⟨relStep_lt _ _ _ _, relStep_lt _ _ _ _, relStep_lt _ _ _ _,
        Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), nextCode_le _ _⟩

structure Letter where
  a : Bool
  b : Bool
  marker : Bool

def Letter.val (x : Letter) : Nat := symbol x.a x.b x.marker

def View.run (v : View) : List Letter → Option View
  | [] => some v
  | x :: xs => (v.advance x.a x.b x.marker).bind (fun w => w.run xs)

theorem View.run_encode (v : View) (hv : v.Valid) (xs : List Letter) :
    Ruliology.CellularAutomata.Rule30StripeMeeting.run v.encode (xs.map Letter.val) = (v.run xs).map View.encode := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, Ruliology.CellularAutomata.Rule30StripeMeeting.run, View.run, Letter.val]
      rw [v.encode_advance hv]
      cases h : v.advance x.a x.b x.marker with
      | none => simp only [Option.map_none, Option.bind_none]
      | some w =>
          simp only [Option.map_some, Option.bind_some]
          exact ih w (View.advance_valid h)

def initialView : View := ⟨4,4,4,0,0,0⟩

theorem initialView_valid : initialView.Valid := by unfold View.Valid initialView; decide
theorem initialView_encode : initialView.encode = initial := by decide

theorem safe_after_input (xs : List Letter) {v : View} (h : initialView.run xs = some v) :
    endGood v.encode = true := by
  have hr : Ruliology.CellularAutomata.Rule30StripeMeeting.run initial (xs.map Letter.val) = some v.encode := by
    rw [← initialView_encode, initialView.run_encode initialView_valid, h]
    rfl
  apply all_input_lengths_safe (xs.map Letter.val) _ hr
  intro u hu
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hu
  exact symbol_lt x.a x.b x.marker

def centerCode (c n : Nat) : Nat := if n ≤ c then 0 else min 4 (n-c)

theorem centerCode_zero (c : Nat) : centerCode c 0 = 0 := by simp [centerCode]

theorem centerCode_succ (c n : Nat) :
    nextCode (centerCode c n) (decide (n = c)) = centerCode c (n+1) := by
  by_cases he : n = c
  · subst n
    simp [nextCode, centerCode]
  · by_cases hl : n < c
    · have hn : n ≤ c := by omega
      have hs : n+1 ≤ c := by omega
      simp [nextCode, centerCode, he, hn, hs]
    · have hn : ¬ n ≤ c := by omega
      have hs : ¬ n+1 ≤ c := by omega
      have hp : 0 < min 4 (n-c) := by omega
      simp only [nextCode, he, decide_false, Bool.false_eq_true, ↓reduceIte,
        centerCode, hn, hs]
      have hz : (min 4 (n-c) == 0) = false := by simp; omega
      rw [hz]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

theorem centerCode_marker (c n : Nat) :
    (decide (n = c) && centerCode c n != 0) = false := by
  by_cases he : n = c
  · subst n; simp [centerCode]
  · simp [he]

theorem centerCode_one (c n : Nat) : centerCode c (n+1) = 1 ↔ n = c := by
  unfold centerCode
  split <;> omega

theorem centerCode_two (c n : Nat) : centerCode c (n+1) = 2 ↔ n = c+1 := by
  unfold centerCode
  split <;> omega

theorem centerCode_allow (c n t : Nat) (ht : t < 3) :
    (centerCode c (n+1) == 0 || centerCode c (n+1) ≤ t+1) = decide (n ≤ c+t) := by
  unfold centerCode
  split
  · simp only [Nat.reduceBEq, Bool.true_or]
    have h : n ≤ c+t := by omega
    simp [h]
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    omega

def relationRun (a b c : Nat) : Nat → Nat
  | 0 => 4
  | n+1 => relStep (relationRun a b c n) (a.testBit n) (b.testBit n) (decide (n ≤ c))

def actualView (a b c n : Nat) : View :=
  ⟨relationRun a b c n, relationRun (Phi a) (Phi b) (c+1) n,
    relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) n,
    history a n, history b n, centerCode c n⟩

def actualLetter (a b c n : Nat) : Letter :=
  ⟨a.testBit n, b.testBit n, decide (n = c)⟩

theorem actualView_zero (a b c : Nat) : actualView a b c 0 = initialView := by
  simp [actualView, relationRun, history_zero, centerCode_zero, initialView]

theorem actualView_advance (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    (actualView a b c n).advance (a.testBit n) (b.testBit n) (decide (n = c)) =
      some (actualView a b c (n+1)) := by
  have g0 : (centerCode c (n+1) == 1 && a.testBit n != b.testBit n) = false := by
    by_cases hc : centerCode c (n+1) = 1
    · have hn := (centerCode_one c n).mp hc
      subst n
      simp [h0]
    · simp [hc]
  have g1 : (centerCode c (n+1) == 2 &&
      (Phi a).testBit n != (Phi b).testBit n) = false := by
    by_cases hc : centerCode c (n+1) = 2
    · have hn := (centerCode_two c n).mp hc
      subst n
      simp [h1]
    · simp [hc]
  simp only [View.advance, actualView, centerCode_marker, Bool.false_eq_true,
    ↓reduceIte, centerCode_succ, ← first_exact, g0, g1, Bool.false_or,
    ← second_exact, centerCode_allow c n 0 (by decide),
    centerCode_allow c n 1 (by decide), centerCode_allow c n 2 (by decide),
    Nat.add_zero, history_succ, relationRun]

def actualInput (a b c : Nat) (n : Nat) : List Letter :=
  (List.range n).map (actualLetter a b c)

theorem View.run_append (v : View) (xs ys : List Letter) :
    v.run (xs ++ ys) = (v.run xs).bind (fun w => w.run ys) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, View.run]
      cases h : v.advance x.a x.b x.marker with
      | none => rfl
      | some w => simpa only [Option.bind_some] using ih w

theorem actualInput_run (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    initialView.run (actualInput a b c n) = some (actualView a b c n) := by
  induction n with
  | zero => simp [actualInput, View.run, actualView_zero]
  | succ n ih =>
      simp only [actualInput, List.range_succ, List.map_append, List.map_singleton,
        View.run_append] at *
      rw [ih]
      simp only [Option.bind_some, View.run, actualLetter]
      rw [actualView_advance a b c n h0 h1]
      rfl

/-- The checked end condition applies to actual rows of every integer size,
provided the two relevant center observations agree. This does not yet state
the corresponding normalization implication. -/
theorem actual_input_safe (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    endGood (actualView a b c n).encode = true :=
  safe_after_input _ (actualInput_run a b c n h0 h1)

def relCode (ta tb : Nat) (ident pending valid : Bool) : Nat :=
  8 * (5 * ta + tb) + 4 * ident.toNat + 2 * pending.toNat + valid.toNat

theorem relCode_decode (ta tb : Nat) (ht : tb < 5) (ident pending valid : Bool) :
    (relCode ta tb ident pending valid / 8) / 5 = ta ∧
    (relCode ta tb ident pending valid / 8) % 5 = tb ∧
    (relCode ta tb ident pending valid).testBit 0 = valid ∧
    (relCode ta tb ident pending valid).testBit 1 = pending ∧
    (relCode ta tb ident pending valid).testBit 2 = ident := by
  cases ident <;> cases pending <;> cases valid <;>
    simp [relCode, Nat.testBit_eq_decide_div_mod_eq] <;> omega

def tailRun (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => tailNext (tailRun a n) (a.testBit n)

theorem tailRun_lt (a n : Nat) : tailRun a n < 5 := by
  cases n with
  | zero => simp [tailRun]
  | succ n => exact tailNext_lt _ _

def identAt (a b : Nat) : Nat → Bool
  | 0 => true
  | n+1 => identAt a b n && (a.testBit n == b.testBit n)

def pendingAt (a b c : Nat) : Nat → Bool
  | 0 => false
  | n+1 => decide (n ≤ c) && a.testBit n && b.testBit n &&
      (tailRun a (n+1) == 1 || tailRun a (n+1) == 3) &&
      (tailRun b (n+1) == 1 || tailRun b (n+1) == 3)

def validAt (a b c : Nat) : Nat → Bool
  | 0 => false
  | n+1 => (validAt a b c n && (a.testBit n == b.testBit n)) ||
      (pendingAt a b c n && !a.testBit n && !b.testBit n)

theorem relationRun_code (a b c n : Nat) :
    relationRun a b c n = relCode (tailRun a n) (tailRun b n)
      (identAt a b n) (pendingAt a b c n) (validAt a b c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨hta,htb,hv,hp,hi⟩ := relCode_decode (tailRun a n) (tailRun b n)
        (tailRun_lt b n) (identAt a b n) (pendingAt a b c n) (validAt a b c n)
      rw [relationRun, ih]
      simp only [relStep, hta, htb, hv, hp, hi]
      rfl

def PrefixEq (a b n : Nat) : Prop := ∀ i, i < n → a.testBit i = b.testBit i

theorem identAt_iff (a b n : Nat) : identAt a b n = true ↔ PrefixEq a b n := by
  induction n with
  | zero => simp [identAt, PrefixEq]
  | succ n ih =>
      simp only [identAt, Bool.and_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ⟨h,he⟩ i hi
        by_cases hin : i < n
        · exact h i hin
        · have hn : i = n := by omega
          simpa [hn] using he
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

def EligibleCut (a b c j : Nat) : Prop :=
  j ≤ c ∧ a.testBit j = true ∧ b.testBit j = true ∧
    (tailRun a (j+1) = 1 ∨ tailRun a (j+1) = 3) ∧
    (tailRun b (j+1) = 1 ∨ tailRun b (j+1) = 3)

theorem pendingAt_iff (a b c n : Nat) : pendingAt a b c n = true ↔
    ∃ j, n = j+1 ∧ EligibleCut a b c j := by
  cases n with
  | zero => simp [pendingAt]
  | succ n => simp [pendingAt, EligibleCut, and_assoc]

def CutWitness (a b c n : Nat) : Prop := ∃ j, j+1 < n ∧ EligibleCut a b c j ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → i < n → a.testBit i = b.testBit i

theorem cutWitness_succ (a b c n : Nat) : CutWitness a b c (n+1) ↔
    (CutWitness a b c n ∧ a.testBit n = b.testBit n) ∨
    (pendingAt a b c n = true ∧ a.testBit n = false ∧ b.testBit n = false) := by
  constructor
  · rintro ⟨j,hj,he,hza,hzb,hs⟩
    by_cases hjn : j+1 < n
    · left
      exact ⟨⟨j,hjn,he,hza,hzb,fun i hi hn => hs i hi (by omega)⟩,
        hs n hjn (by omega)⟩
    · have hn : n = j+1 := by omega
      right
      exact ⟨(pendingAt_iff a b c n).mpr ⟨j,hn,he⟩, hn ▸ hza, hn ▸ hzb⟩
  · rintro (⟨⟨j,hj,he,hza,hzb,hs⟩,hn⟩ | ⟨hp,hza,hzb⟩)
    · refine ⟨j,by omega,he,hza,hzb,?_⟩
      intro i hi hin
      by_cases hh : i < n
      · exact hs i hi hh
      · have hi : i = n := by omega
        simpa [hi] using hn
    · obtain ⟨j,hn,he⟩ := (pendingAt_iff a b c n).mp hp
      refine ⟨j,by omega,he,?_,?_,?_⟩
      · simpa only [hn] using hza
      · simpa only [hn] using hzb
      · intro i hi hin
        omega

theorem validAt_iff (a b c n : Nat) : validAt a b c n = true ↔ CutWitness a b c n := by
  induction n with
  | zero => simp [validAt, CutWitness]
  | succ n ih =>
      rw [cutWitness_succ]
      simp [validAt, ih, and_assoc]

def relAccept (e : Nat) : Bool := e.testBit 0 || e.testBit 2

theorem relationRun_accept_iff (a b c n : Nat) :
    relAccept (relationRun a b c n) = true ↔ PrefixEq a b n ∨ CutWitness a b c n := by
  rw [relationRun_code]
  obtain ⟨_,_,hv,_,hi⟩ := relCode_decode (tailRun a n) (tailRun b n)
    (tailRun_lt b n) (identAt a b n) (pendingAt a b c n) (validAt a b c n)
  simp only [relAccept, hv, hi, Bool.or_eq_true, identAt_iff, validAt_iff, or_comm]

def ZerosFrom (a n : Nat) : Prop := ∀ i, n ≤ i → a.testBit i = false

theorem ZerosFrom.mono {a n m : Nat} (h : ZerosFrom a n) (hn : n ≤ m) : ZerosFrom a m :=
  fun i hi => h i (by omega)

theorem zerosFrom_large (a n : Nat) (ha : a ≤ n) : ZerosFrom a n := by
  intro i hi
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_le_of_lt (by omega) Nat.lt_two_pow_self

theorem ZerosFrom.phi {a n : Nat} (h : ZerosFrom a n) : ZerosFrom (Phi a) (n+2) := by
  intro i hi
  rw [Phi_testBit, before_of_lt a i 0 (by omega), before_of_lt a i 1 (by omega)]
  simp only [h i (by omega), h (i-(0+1)) (by omega), h (i-(1+1)) (by omega)]
  rfl

theorem relationRun_lt (a b c n : Nat) : relationRun a b c n < 200 := by
  cases n with
  | zero => simp [relationRun]
  | succ n => exact relStep_lt _ _ _ _

theorem actualView_valid (a b c n : Nat) : (actualView a b c n).Valid := by
  refine ⟨relationRun_lt _ _ _ _, relationRun_lt _ _ _ _, relationRun_lt _ _ _ _,
    history_lt _ _, history_lt _ _, ?_⟩
  change centerCode c n ≤ 4
  unfold centerCode
  split <;> omega

theorem relAccept_mod (e : Nat) : relAccept (e % 256) = relAccept e := by
  change relAccept (e % 2^8) = relAccept e
  simp only [relAccept, Nat.testBit_mod_two_pow, Nat.reduceLT, decide_true, Bool.true_and]

theorem View.accept_encode (v : View) (hv : v.Valid) :
    accept v.encode 0 = relAccept v.e0 ∧ accept v.encode 1 = relAccept v.e1 ∧
    accept v.encode 2 = relAccept v.e2 := by
  obtain ⟨h0,h1,h2,_,_,_⟩ := v.decode_encode hv
  have a0 := congrArg relAccept h0
  have a1 := congrArg relAccept h1
  have a2 := congrArg relAccept h2
  simp only [relAccept_mod] at a0 a1 a2
  exact ⟨a0,a1,a2⟩

theorem step_actual_zero (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (ha : a.testBit n = false) (hb : b.testBit n = false) (hc : n ≠ c) :
    step (actualView a b c n).encode 0 = some (actualView a b c (n+1)).encode := by
  have h := (actualView a b c n).encode_advance (actualView_valid a b c n)
    (a.testBit n) (b.testBit n) (decide (n = c))
  rw [actualView_advance a b c n h0 h1] at h
  simpa only [ha,hb,hc,decide_false,symbol,Bool.toNat_false,Nat.mul_zero,
    Nat.add_zero,Option.map_some] using h

theorem flush_actual (a b c n k : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (ha : ZerosFrom a n) (hb : ZerosFrom b n) (hc : c < n) :
    flush k (actualView a b c n).encode = some (actualView a b c (n+k)).encode := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [flush, step_actual_zero a b c n h0 h1 (ha n (by omega)) (hb n (by omega)) (by omega)]
      simp only [Option.bind_some]
      have h := ih (n+1) (ha.mono (by omega)) (hb.mono (by omega)) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h

def RowRelated (a b c : Nat) : Prop := a = b ∨ ∃ j, EligibleCut a b c j ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → a.testBit i = b.testBit i

theorem prefixEq_eq {a b n : Nat} (ha : ZerosFrom a n) (hb : ZerosFrom b n)
    (h : PrefixEq a b n) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h i hi
  · rw [ha i (by omega), hb i (by omega)]

theorem relationRun_full_iff (a b c n : Nat) (ha : ZerosFrom a n) (hb : ZerosFrom b n)
    (hc : c+1 < n) : relAccept (relationRun a b c n) = true ↔ RowRelated a b c := by
  rw [relationRun_accept_iff]
  constructor
  · rintro (he | ⟨j,hj,he,hza,hzb,hs⟩)
    · exact Or.inl (prefixEq_eq ha hb he)
    · right
      refine ⟨j,he,hza,hzb,?_⟩
      intro i hi
      by_cases hin : i < n
      · exact hs i hi hin
      · rw [ha i (by omega), hb i (by omega)]
  · rintro (he | ⟨j,he,hza,hzb,hs⟩)
    · left
      subst b
      intro i hi
      rfl
    · exact Or.inr ⟨j,by have hj := he.1; omega,he,hza,hzb,fun i hi _ => hs i hi⟩

/-- No pair of finite rows can first acquire the common-cut relation after
two steps if its two preceding center observations agree. The common-cut
relation's stripe language is interpreted in TailLanguageResearch;
numerical-normalizer equivalence remains open. -/
theorem two_step_common_cut (a b c : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (h2 : RowRelated (Phi (Phi a)) (Phi (Phi b)) (c+2)) :
    RowRelated a b c ∨ RowRelated (Phi a) (Phi b) (c+1) := by
  let n := a+b+c+1
  have ha : ZerosFrom a n := zerosFrom_large a n (by dsimp [n]; omega)
  have hb : ZerosFrom b n := zerosFrom_large b n (by dsimp [n]; omega)
  have hc : c < n := by dsimp [n]; omega
  have hp : (n+2)+2 ≤ n+5 := by omega
  have ha2 := ha.phi.phi.mono hp
  have hb2 := hb.phi.phi.mono hp
  have r2 := (relationRun_full_iff (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5)
    ha2 hb2 (by omega)).mpr h2
  have hgood := actual_input_safe a b c n h0 h1
  have hcode : (actualView a b c n).encode >>> 32 ≠ 0 := by
    have hdec := (actualView a b c n).decode_encode (actualView_valid a b c n)
    rw [hdec.2.2.2.2.2]
    change centerCode c n ≠ 0
    unfold centerCode
    split <;> omega
  simp only [endGood, hcode, beq_iff_eq, ↓reduceIte,
    flush_actual a b c n 5 h0 h1 ha hb hc] at hgood
  obtain ⟨ac0,ac1,ac2⟩ := (actualView a b c (n+5)).accept_encode
    (actualView_valid a b c (n+5))
  rw [ac0,ac1,ac2] at hgood
  change (!(relAccept (relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5)) &&
    !relAccept (relationRun a b c (n+5)) &&
    !relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)))) = true at hgood
  rw [r2] at hgood
  have hor : relAccept (relationRun a b c (n+5)) = true ∨
      relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)) = true := by
    cases hx : relAccept (relationRun a b c (n+5)) <;>
      cases hy : relAccept (relationRun (Phi a) (Phi b) (c+1) (n+5)) <;>
      simp_all
  rcases hor with he | he
  · exact Or.inl ((relationRun_full_iff a b c (n+5) (ha.mono (by omega))
      (hb.mono (by omega)) (by omega)).mp he)
  · exact Or.inr ((relationRun_full_iff (Phi a) (Phi b) (c+1) (n+5)
      (ha.phi.mono (by omega)) (hb.phi.mono (by omega)) (by omega)).mp he)

def ZeroWord (xs : List Bool) : Prop := ∀ b, b ∈ xs → b = false

inductive StripeWord : List Bool → Prop
  | single (zs : List Bool) (h : ZeroWord zs) : StripeWord (zs ++ [true])
  | double (zs : List Bool) (h : ZeroWord zs) : StripeWord (zs ++ [true,true])
  | extend {xs : List Bool} (h : StripeWord xs) : StripeWord (xs ++ [false,true])

def TailInvariant (xs : List Bool) (s : Nat) : Prop :=
  match s with
  | 0 => ZeroWord xs
  | 1 => ∃ zs, ZeroWord zs ∧ xs = zs ++ [true]
  | 2 => ∃ ys, StripeWord ys ∧ xs = ys ++ [false]
  | 3 => StripeWord xs
  | _ => True

theorem zeroWord_append_false {xs : List Bool} (h : ZeroWord xs) :
    ZeroWord (xs ++ [false]) := by
  intro b hb
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | hb
  · exact h b hb
  · exact hb

theorem tailInvariant_step (xs : List Bool) (s : Nat) (b : Bool)
    (h : TailInvariant xs s) : TailInvariant (xs ++ [b]) (tailNext s b) := by
  rcases s with _ | s
  · cases b
    · exact zeroWord_append_false h
    · exact ⟨xs,h,rfl⟩
  · rcases s with _ | s
    · obtain ⟨zs,hz,rfl⟩ := h
      cases b
      · exact ⟨zs ++ [true],StripeWord.single zs hz,rfl⟩
      · simpa [TailInvariant, tailNext, List.append_assoc] using
          StripeWord.double zs hz
    · rcases s with _ | s
      · obtain ⟨ys,hy,rfl⟩ := h
        cases b
        · trivial
        · simpa [TailInvariant, tailNext, List.append_assoc] using
            StripeWord.extend hy
      · rcases s with _ | s
        · cases b
          · exact ⟨xs,h,rfl⟩
          · trivial
        · cases b <;> trivial

def tailFold (s : Nat) (xs : List Bool) : Nat := xs.foldl tailNext s

theorem tailFold_append (s : Nat) (xs ys : List Bool) :
    tailFold s (xs ++ ys) = tailFold (tailFold s xs) ys := List.foldl_append

theorem tailInvariant_fold (xs ys : List Bool) (s : Nat) (h : TailInvariant xs s) :
    TailInvariant (xs ++ ys) (tailFold s ys) := by
  induction ys generalizing xs s with
  | nil => simpa only [List.append_nil,tailFold,List.foldl_nil] using h
  | cons b ys ih =>
      have hh := ih (xs ++ [b]) (tailNext s b) (tailInvariant_step xs s b h)
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        tailFold, List.foldl_cons] using hh

theorem tailFold_zero {xs : List Bool} (h : ZeroWord xs) : tailFold 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hb := h b (by simp)
      have hx : ZeroWord xs := fun x hx => h x (by simp [hx])
      simpa [tailFold, hb, tailNext] using ih hx

theorem stripeWord_accept {xs : List Bool} (h : StripeWord xs) :
    tailFold 0 xs = 1 ∨ tailFold 0 xs = 3 := by
  induction h with
  | single zs hz =>
      left
      rw [tailFold_append, tailFold_zero hz]
      rfl
  | double zs hz =>
      right
      rw [tailFold_append, tailFold_zero hz]
      rfl
  | extend h ih =>
      right
      rw [tailFold_append]
      rcases ih with hi | hi <;> rw [hi] <;> rfl

theorem tailFold_accept_iff (xs : List Bool) :
    tailFold 0 xs = 1 ∨ tailFold 0 xs = 3 ↔ StripeWord xs := by
  constructor
  · intro h
    have hz : TailInvariant [] 0 := by intro b hb; simp at hb
    have hi := tailInvariant_fold [] xs 0 hz
    simp only [List.nil_append] at hi
    rcases h with h | h
    · rw [h] at hi
      obtain ⟨zs,hz,rfl⟩ := hi
      exact StripeWord.single zs hz
    · simpa only [h, TailInvariant] using hi
  · exact stripeWord_accept

def rowBits (a n : Nat) : List Bool := (List.range n).map a.testBit

theorem rowBits_succ (a n : Nat) : rowBits a (n+1) = rowBits a n ++ [a.testBit n] := by
  simp only [rowBits, List.range_succ, List.map_append, List.map_singleton]

theorem tailRun_eq_fold (a n : Nat) : tailRun a n = tailFold 0 (rowBits a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rowBits_succ, tailFold_append, ← ih]
      rfl

theorem tailRun_accept_iff (a n : Nat) :
    tailRun a n = 1 ∨ tailRun a n = 3 ↔ StripeWord (rowBits a n) := by
  rw [tailRun_eq_fold]
  exact tailFold_accept_iff _

def StripeRelated (a b c : Nat) : Prop := a = b ∨ ∃ j, j ≤ c ∧
  StripeWord (rowBits a (j+1)) ∧ StripeWord (rowBits b (j+1)) ∧
  a.testBit j = true ∧ b.testBit j = true ∧
  a.testBit (j+1) = false ∧ b.testBit (j+1) = false ∧
  ∀ i, j+1 < i → a.testBit i = b.testBit i

theorem rowRelated_iff_stripeRelated (a b c : Nat) :
    RowRelated a b c ↔ StripeRelated a b c := by
  unfold RowRelated StripeRelated EligibleCut
  simp only [tailRun_accept_iff]
  constructor
  · rintro (he | ⟨j,⟨hc,ha,hb,hsa,hsb⟩,hza,hzb,hs⟩)
    · exact Or.inl he
    · exact Or.inr ⟨j,hc,hsa,hsb,ha,hb,hza,hzb,hs⟩
  · rintro (he | ⟨j,hc,hsa,hsb,ha,hb,hza,hzb,hs⟩)
    · exact Or.inl he
    · exact Or.inr ⟨j,⟨hc,ha,hb,hsa,hsb⟩,hza,hzb,hs⟩

/-- A pair with equal first two center observations cannot first become
stripe-related on the second step. This quantifies over all finite integer
rows and all center indices, with no bound on their sizes. -/
theorem two_step_stripe_related (a b c : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1))
    (h2 : StripeRelated (Phi (Phi a)) (Phi (Phi b)) (c+2)) :
    StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  have h := two_step_common_cut a b c h0 h1
    ((rowRelated_iff_stripeRelated _ _ _).mpr h2)
  rcases h with h | h
  · exact Or.inl ((rowRelated_iff_stripeRelated _ _ _).mp h)
  · exact Or.inr ((rowRelated_iff_stripeRelated _ _ _).mp h)

def phiRows (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => Phi (phiRows a t)

def SameCenterPrefix (a b c t : Nat) : Prop :=
  ∀ s, s < t → (phiRows a s).testBit (c+s) = (phiRows b s).testBit (c+s)

theorem sameCenterPrefix_mono {a b c t u : Nat} (h : SameCenterPrefix a b c t)
    (hu : u ≤ t) : SameCenterPrefix a b c u := fun s hs => h s (by omega)

/-- If finite rows become stripe-related after any number of steps, and all
preceding center observations agree, they were stripe-related at time 0 or 1.
The stripe relation is allowed to disappear and reappear; no equivariance
or preservation under Phi is assumed. -/
theorem stripe_meeting_is_early (a b c t : Nat) (ht : SameCenterPrefix a b c t)
    (hr : StripeRelated (phiRows a t) (phiRows b t) (c+t)) :
    StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
      rcases t with _ | t
      · exact Or.inl hr
      · rcases t with _ | t
        · exact Or.inr hr
        · have h0 := ht t (by omega)
          have h1 := ht (t+1) (by omega)
          have hh : StripeRelated (Phi (Phi (phiRows a t)))
              (Phi (Phi (phiRows b t))) ((c+t)+2) := by
            simpa only [phiRows, Nat.add_assoc] using hr
          have he := two_step_stripe_related (phiRows a t) (phiRows b t) (c+t)
            h0 (by simpa only [phiRows, Nat.add_assoc] using h1) hh
          rcases he with he | he
          · exact ih t (by omega) (sameCenterPrefix_mono ht (by omega)) he
          · apply ih (t+1) (by omega) (sameCenterPrefix_mono ht (by omega))
            simpa only [phiRows, Nat.add_assoc] using he

/-- The contrapositive is useful for a trace-completeness argument: two rows
not stripe-related at time 0 or 1 cannot become stripe-related later while
their center observations continue to agree. It does not establish that
every equal infinite trace must eventually enter this relation. -/
theorem no_delayed_stripe_meeting (a b c t : Nat)
    (h0 : ¬ StripeRelated a b c)
    (h1 : ¬ StripeRelated (Phi a) (Phi b) (c+1))
    (ht : SameCenterPrefix a b c t) :
    ¬ StripeRelated (phiRows a t) (phiRows b t) (c+t) := by
  intro hr
  rcases stripe_meeting_is_early a b c t ht hr with h | h
  · exact h0 h
  · exact h1 h

theorem StripeRelated.center_pair {a b c : Nat} (h : StripeRelated a b c) :
    a.testBit c = b.testBit c ∧ (Phi a).testBit (c+1) = (Phi b).testBit (c+1) := by
  rcases h with he | ⟨j,hjc,hsa,hsb,hja,hjb,hza,hzb,hs⟩
  · subst b
    exact ⟨rfl,rfl⟩
  · have hagree : ∀ i, j ≤ i → a.testBit i = b.testBit i := by
      intro i hi
      by_cases h0 : i = j
      · rw [h0,hja,hjb]
      · by_cases h1 : i = j+1
        · rw [h1,hza,hzb]
        · exact hs i (by omega)
    refine ⟨hagree c hjc,?_⟩
    by_cases hc : c = j
    · subst c
      rw [Phi_testBit, Phi_testBit, before_succ_zero, before_succ_zero,hza,hzb,hja,hjb]
      simp
    · rw [Phi_testBit, Phi_testBit, before_succ_zero, before_succ_zero,
        before_of_lt a (c+1) 1 (by omega), before_of_lt b (c+1) 1 (by omega),
        hagree (c+1) (by omega), hagree c hjc, hagree ((c+1)-(1+1)) (by omega)]

theorem preservesTwo_after_actual (a b c n : Nat)
    (h0 : a.testBit c = b.testBit c)
    (h1 : (Phi a).testBit (c+1) = (Phi b).testBit (c+1)) :
    preservesTwo (actualView a b c n).encode = true := by
  have hr : Ruliology.CellularAutomata.Rule30StripeMeeting.run initial
      ((actualInput a b c n).map Letter.val) = some (actualView a b c n).encode := by
    rw [← initialView_encode, initialView.run_encode initialView_valid,
      actualInput_run a b c n h0 h1]
    rfl
  apply all_of_member preservesTwo_pool (run_member initial_member ?_ hr)
  intro u hu
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
  exact symbol_lt x.a x.b x.marker

/-- Stripe-related rows remain stripe-related after two Rule 30 steps.
One-step preservation is false, as shown by rows 2 and 3 at center 1. -/
theorem stripe_related_preserves_two (a b c : Nat) (h : StripeRelated a b c) :
    StripeRelated (Phi (Phi a)) (Phi (Phi b)) (c+2) := by
  obtain ⟨h0,h1⟩ := h.center_pair
  let n := a+b+c+1
  have ha : ZerosFrom a n := zerosFrom_large a n (by dsimp [n]; omega)
  have hb : ZerosFrom b n := zerosFrom_large b n (by dsimp [n]; omega)
  have hc : c < n := by dsimp [n]; omega
  have he := (rowRelated_iff_stripeRelated a b c).mpr h
  have r0 := (relationRun_full_iff a b c (n+5) (ha.mono (by omega))
    (hb.mono (by omega)) (by omega)).mpr he
  have hg := preservesTwo_after_actual a b c n h0 h1
  have hcode : (actualView a b c n).encode >>> 32 ≠ 0 := by
    have hdec := (actualView a b c n).decode_encode (actualView_valid a b c n)
    rw [hdec.2.2.2.2.2]
    change centerCode c n ≠ 0
    unfold centerCode
    split <;> omega
  simp only [preservesTwo, hcode, beq_iff_eq, ↓reduceIte,
    flush_actual a b c n 5 h0 h1 ha hb hc] at hg
  obtain ⟨ac0,_,ac2⟩ := (actualView a b c (n+5)).accept_encode
    (actualView_valid a b c (n+5))
  rw [ac0,ac2] at hg
  change (!relAccept (relationRun a b c (n+5)) ||
    relAccept (relationRun (Phi (Phi a)) (Phi (Phi b)) (c+2) (n+5))) = true at hg
  rw [r0] at hg
  simp only [Bool.not_true, Bool.false_or] at hg
  apply (rowRelated_iff_stripeRelated _ _ _).mp
  apply (relationRun_full_iff _ _ _ (n+5) (ha.phi.phi.mono (by omega))
    (hb.phi.phi.mono (by omega)) (by omega)).mp
  exact hg

theorem phiRows_add (a s t : Nat) : phiRows a (s+t) = phiRows (phiRows a s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change Phi (phiRows a (s+t)) = Phi (phiRows (phiRows a s) t)
      exact congrArg Phi ih

theorem phiRows_two_start (a t : Nat) :
    phiRows (Phi (Phi a)) t = phiRows a (t+2) := by
  have h := (phiRows_add a 2 t).symm
  simpa only [Nat.add_comm 2 t,phiRows] using h

/-- Erasing or replacing a stripe prefix with a common white separator
preserves the entire center trace. This is one direction of the trace-kernel
classification; the converse is not claimed. -/
theorem stripe_related_same_trace (a b c : Nat) (h : StripeRelated a b c) (t : Nat) :
    (phiRows a t).testBit (c+t) = (phiRows b t).testBit (c+t) := by
  induction t using Nat.strongRecOn generalizing a b c with
  | ind t ih =>
      rcases t with _ | t
      · exact h.center_pair.1
      · rcases t with _ | t
        · exact h.center_pair.2
        · have hn : t+1+1 = t+2 := by omega
          rw [hn]
          have hh := ih t (by omega) (Phi (Phi a)) (Phi (Phi b)) (c+2)
            (stripe_related_preserves_two a b c h)
          have hc : (c+2)+t = c+(t+2) := by omega
          simpa only [phiRows_two_start,hc] using hh

theorem stripe_related_same_prefix (a b c t : Nat) (h : StripeRelated a b c) :
    SameCenterPrefix a b c t := fun s _ => stripe_related_same_trace a b c h s

/-- For a pair with equal entire center traces, entering the stripe relation
at any finite time is equivalent to entering it at time zero or one. This
does not assert that such an entry must happen. -/
theorem eventually_stripe_iff_early (a b c : Nat)
    (ht : ∀ t, (phiRows a t).testBit (c+t) = (phiRows b t).testBit (c+t)) :
    (∃ t, StripeRelated (phiRows a t) (phiRows b t) (c+t)) ↔
      StripeRelated a b c ∨ StripeRelated (Phi a) (Phi b) (c+1) := by
  constructor
  · rintro ⟨t,hr⟩
    exact stripe_meeting_is_early a b c t (fun s _ => ht s) hr
  · rintro (h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩

/-! ## Even-step all-time persistence of `StripeRelated` and unconditional joint trace/stripe equivalence -/

/-- **Even-Step All-Time Persistence of `StripeRelated` and Unconditional Joint Trace/Stripe Equivalence (`stripe_related_even_and_joint_early_iff`).** -/
theorem stripe_related_even_and_joint_early_iff (a b c : Nat) :
    (StripeRelated a b c → ∀ k : Nat,
      StripeRelated (phiRows a (2 * k)) (phiRows b (2 * k)) (c + 2 * k)) ∧
    (((∀ t, (phiRows a t).testBit (c + t) = (phiRows b t).testBit (c + t)) ∧
      (∃ t, StripeRelated (phiRows a t) (phiRows b t) (c + t))) ↔
      (StripeRelated a b c ∨ (a.testBit c = b.testBit c ∧ StripeRelated (Phi a) (Phi b) (c + 1)))) := by
  have heven : ∀ (x y z k : Nat), StripeRelated x y z →
      StripeRelated (phiRows x (2 * k)) (phiRows y (2 * k)) (z + 2 * k) := by
    intro x y z k
    induction k generalizing x y z with
    | zero => intro h; exact h
    | succ k ih =>
      intro h
      have h2 := ih (Phi (Phi x)) (Phi (Phi y)) (z + 2) (stripe_related_preserves_two x y z h)
      rw [phiRows_two_start, phiRows_two_start] at h2
      simpa only [show 2 * k + 2 = 2 * (k + 1) by omega,
                  show z + 2 + 2 * k = z + 2 * (k + 1) by omega] using h2
  refine ⟨fun h k => heven a b c k h, ⟨fun ⟨ht, hex⟩ => ?_, fun h => ?_⟩⟩
  · rcases (eventually_stripe_iff_early a b c ht).mp hex with h0 | h1
    · exact Or.inl h0
    · exact Or.inr ⟨ht 0, h1⟩
  · rcases h with h0 | ⟨hc0, h1⟩
    · exact ⟨stripe_related_same_trace a b c h0, ⟨0, h0⟩⟩
    · refine ⟨fun t => ?_, ⟨1, h1⟩⟩
      cases t with
      | zero => exact hc0
      | succ t =>
        have htr := stripe_related_same_trace (Phi a) (Phi b) (c + 1) h1 t
        have ha1 : phiRows (Phi a) t = phiRows a (t + 1) := by
          simpa only [Nat.add_comm 1 t, phiRows] using (phiRows_add a 1 t).symm
        have hb1 : phiRows (Phi b) t = phiRows b (t + 1) := by
          simpa only [Nat.add_comm 1 t, phiRows] using (phiRows_add b 1 t).symm
        rw [ha1, hb1, show c + 1 + t = c + (t + 1) by omega] at htr
        exact htr

end Ruliology.CellularAutomata.Rule30StripeMeeting
