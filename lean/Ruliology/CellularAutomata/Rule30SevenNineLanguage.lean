module

public import Ruliology.CellularAutomata.Rule30FastImage
public import Ruliology.CellularAutomata.Rule30RankedWords
public import Ruliology.CellularAutomata.Rule30Certificates.SevenNineLanguage

/-!
# No cyclic mixture of 7- and 9-white gaps without 7,7,7 or 7,9,7,9 is an eventual centre clock

Write `pulse q` for one black tick followed by `q` white ones and `blocks qs` for the pulses of a list of gaps.
`EventuallyWord w` says that the centre column of Rule 30 from a single black cell equals `w` repeated from some
time on. `gapAt qs i` is the gap at position `i` of the cyclic list.

* `excludes_language`: let every gap of `qs` be 7 or 9, and let the cyclic sequence of gaps have no three
  consecutive 7s and no 7, 9, 7, 9 (`Clean`). Then `¬ EventuallyWord (blocks qs)`, at any onset.

The proof runs on the 13 cells east of the centre, remembering the last three gaps. From any state, fourteen blocks
of such gaps lead into a set of 3,042 nodes (a strip state with a memory). There the nodes fall into three levels,
by which of two small strongly connected parts they can still reach; the level never rises along a path, so it is
eventually constant.
* Level 0 holds a sink part of 1,274 nodes, whose readings of site 1 depend only on the memory and the next gap,
  and transients that no path keeps for more than nine blocks.
* Level 1 holds a part of 126 nodes and transients that no path keeps for more than four blocks.
* Level 2 is a part of 29 nodes.
In each small part, two paths from one node under the same gaps stay related by a certified partner relation and
show the same readings of site 1. By pigeonhole the true path repeats a node at two period boundaries, so its
readings repeat from then on. Then the masked column `orCol 0` is eventually periodic, which masked Jen forbids
(`orCol_not_eventuallyPeriodic`). All finite checks use the kit's bit-parallel image `fimage`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SevenNineLanguage

open Rule30Jen Rule30Prize Rule30MaskedJen Rule30StripCertificates Rule30RunEnvelopes Rule30RankedWords
open Rule30FastImage Data

/-! ## Blocks and fast images -/

/-- One black tick followed by `q` white ones. -/
def pulse (q : Nat) : List Bool := true :: List.replicate q false

/-- The pulses of a list of gaps. -/
def blocks (qs : List Nat) : List Bool := qs.flatMap pulse

theorem pulse_length (q : Nat) : (pulse q).length = q + 1 := by simp [pulse]

/-- The bit-parallel image of a set of 13-cell strips along a word of centre letters. -/
def fword : List Bool → Nat → Nat
  | [], S => S
  | a :: u, S => fword u (fimage 13 a S)

theorem fword_append : ∀ (u v : List Bool) (S : Nat), fword (u ++ v) S = fword v (fword u S)
  | [], _, _ => rfl
  | a :: u, v, S => fword_append u v (fimage 13 a S)

theorem image_sub_fimage (a : Bool) (S : Nat) : Sub (image 13 a S) (fimage 13 a S) := by
  apply imageAux_forall 13 a S (fun y => (fimage 13 a S).testBit y = true) _ (2 ^ 13) (by omega)
  intro s hs hm z
  exact fimage_mem hs hm z

theorem applyWord_sub_fword : ∀ (u : List Bool) (S : Nat), Sub (applyWord 13 u S) (fword u S)
  | [], _ => fun _ h => h
  | a :: u, S => fun y h => applyWord_sub_fword u (fimage 13 a S) y
      (applyWord_mono 13 u (image_sub_fimage a S) y h)

/-- **The true strip follows the fast image.** -/
theorem fword_sound {t S : Nat} {u : List Bool} (h : Reads t u) (hs : S.testBit (code 13 t) = true) :
    (fword u S).testBit (code 13 (t + u.length)) = true :=
  applyWord_sub_fword u S _ (code_word h hs)

theorem code_lt (t : Nat) : code 13 t < 2 ^ 13 := (enc_encRow 13 t 0).1

theorem code_bit0 (t : Nat) : (code 13 t).testBit 0 = cell t 1 := by
  have h := (enc_encRow 13 t 0).2 0 (by decide)
  simpa using h

/-! ## Readings of site 1 -/

/-- All strips of `X` show one colour at site 1. -/
def const0 (X : Nat) : Bool := (X &&& bm 0 13 == 0) || (X &&& (fullSet 13 ^^^ bm 0 13) == 0)

theorem const0_sound {X r r' : Nat} (h : const0 X = true) (hr : r < 2 ^ 13) (hr' : r' < 2 ^ 13)
    (hx : X.testBit r = true) (hx' : X.testBit r' = true) : r.testBit 0 = r'.testBit 0 := by
  have bit : ∀ y, X.testBit y = true → (X &&& bm 0 13).testBit y = (decide (y < 2 ^ 13) && y.testBit 0) := by
    intro y hy; rw [Nat.testBit_and, hy, testBit_bm, Bool.true_and]
  have bit' : ∀ y, X.testBit y = true →
      (X &&& (fullSet 13 ^^^ bm 0 13)).testBit y = (decide (y < 2 ^ 13) && !y.testBit 0) := by
    intro y hy
    rw [Nat.testBit_and, hy, Nat.testBit_xor, testBit_fullSet, testBit_bm, Bool.true_and]
    cases decide (y < 2 ^ 13) <;> cases y.testBit 0 <;> rfl
  unfold const0 at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · have hz := beq_iff_eq.mp h
    have e1 := bit r hx; have e2 := bit r' hx'
    rw [hz, Nat.zero_testBit] at e1 e2
    simp only [hr, hr', decide_true, Bool.true_and] at e1 e2
    revert e1 e2
    cases r.testBit 0 <;> cases r'.testBit 0 <;> decide
  · have hz := beq_iff_eq.mp h
    have e1 := bit' r hx; have e2 := bit' r' hx'
    rw [hz, Nat.zero_testBit] at e1 e2
    simp only [hr, hr', decide_true, Bool.true_and] at e1 e2
    revert e1 e2
    cases r.testBit 0 <;> cases r'.testBit 0 <;> decide

/-- One colour at site 1 after each letter of `u`. -/
def chk : List Bool → Nat → Bool
  | [], _ => true
  | a :: u, S => const0 (fimage 13 a S) && chk u (fimage 13 a S)

theorem chk_sound : ∀ (u : List Bool) (S : Nat), chk u S = true →
    ∀ o, 1 ≤ o → o ≤ u.length → const0 (fword (u.take o) S) = true
  | [], _, _, o, h1, h2 => by simp at h2; omega
  | a :: u, S, h, o, h1, h2 => by
    simp only [chk, Bool.and_eq_true] at h
    obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
    rcases Nat.eq_zero_or_pos o' with rfl | hp
    · simpa [fword] using h.1
    · simp only [List.take_succ_cons, fword]
      exact chk_sound u _ h.2 o' hp (by simp at h2; omega)

/-- The readings of a block from all strips of `S` agree at its white ticks. -/
def readsOK (S q : Nat) : Bool := chk ((pulse q).take q) S

theorem readsOK_sound {S q : Nat} (h : readsOK S q = true) {o : Nat} (h1 : 1 ≤ o) (h2 : o ≤ q) :
    const0 (fword ((pulse q).take o) S) = true := by
  have := chk_sound _ S h o h1 (by rw [List.length_take, pulse_length]; omega)
  rwa [List.take_take, Nat.min_eq_left h2] at this

/-! ## Sets as bit masks -/

def subB (A B : Nat) : Bool := A &&& B == A

theorem subB_sound {A B s : Nat} (h : subB A B = true) (hs : A.testBit s = true) : B.testBit s = true := by
  have e := congrArg (fun n : Nat => n.testBit s) (beq_iff_eq.mp h)
  simp only [Nat.testBit_and, hs, Bool.true_and] at e
  exact e

theorem testBit_single (x : Nat) : (1 <<< x).testBit x = true := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self]

/-- The partner set of a state in a table of (memory, state, partners). -/
def gLook (tbl : List (List Nat × Nat × List Nat)) (m : List Nat) (u : Nat) : Nat :=
  match tbl.find? (fun e => e.1 == m && e.2.1 == u) with
  | some e => ofList e.2.2
  | none => 0

/-! ## Memories and moves -/

/-- The memories: the last three gaps, without 7,7,7. -/
def mems : List (List Nat) := [[7, 7, 9], [7, 9, 7], [7, 9, 9], [9, 7, 7], [9, 7, 9], [9, 9, 7], [9, 9, 9]]

/-- A gap may follow a memory unless it makes 7,7,7 or 7,9,7,9. -/
def allowed (m : List Nat) (q : Nat) : Bool := !(m.drop 1 == [7, 7] && q == 7) && !(m == [7, 9, 7] && q == 9)

def next (m : List Nat) (q : Nat) : List Nat := m.drop 1 ++ [q]

/-- A check over every allowed move. -/
def forMoves (f : List Nat → Nat → List Nat → Bool) : Bool :=
  mems.all (fun m => [7, 9].all (fun q => !allowed m q || f m q (next m q)))

theorem forMoves_spec {f : List Nat → Nat → List Nat → Bool} (h : forMoves f = true) {m : List Nat} {q : Nat}
    (hm : m ∈ mems) (hq : q = 7 ∨ q = 9) (ha : allowed m q = true) : f m q (next m q) = true := by
  unfold forMoves at h
  have h1 := List.all_eq_true.mp h m hm
  have h2 := List.all_eq_true.mp h1 q (by rcases hq with rfl | rfl <;> simp)
  simpa [ha] using h2

/-! ## The certificate -/

def lvl0 (m : List Nat) : Nat := bS m ||| t0 m
def lv1 (m : List Nat) : Nat := p1 m ||| t1 m
def lvl01 (m : List Nat) : Nat := lvl0 m ||| lv1 m
def last (m : List Nat) : Nat := lvl01 m ||| p2 m

/-- Warm-up checkpoints; checkpoint 0 is every state. -/
def W (i : Nat) (m : List Nat) : Nat := if i = 0 then fullSet 13 else warm i m

/-- Two blocks at a time from each checkpoint into the next, and the last checkpoint inside the lasting nodes. -/
def chkWarm : Bool :=
  (List.range warmRounds).all (fun i => forMoves (fun m q m1 => [7, 9].all (fun q2 =>
    !allowed m1 q2 || subB (fword (pulse q ++ pulse q2) (W i m)) (W (i + 1) (next m1 q2))))) &&
  mems.all (fun m => subB (W warmRounds m) (last m))

/-- The levels are forward closed; the sink part is closed; the part of 126 keeps its level-1 successors; the
sink part's readings depend only on the memory and the gap. -/
def chkRegions : Bool :=
  forMoves (fun m q m' =>
    subB (fword (pulse q) (lvl0 m)) (lvl0 m') && subB (fword (pulse q) (lvl01 m)) (lvl01 m') &&
    subB (fword (pulse q) (last m)) (last m') && subB (fword (pulse q) (bS m)) (bS m') &&
    subB (fword (pulse q) (p1 m) &&& lv1 m') (p1 m') && readsOK (bS m) q)

/-- No path stays among the transients of a level for `len` blocks. -/
def chkZ (z : Nat → List Nat → Nat) (t : List Nat → Nat) (len : Nat) : Bool :=
  forMoves (fun m q m' => (List.range len).all (fun j => subB (fword (pulse q) (z j m) &&& t m') (z (j + 1) m'))) &&
  mems.all (fun m => z 0 m == t m && z len m == 0)

/-- A part with partner sets: the diagonal, closure under moves with one gap, the nodes that cannot stay in the
part, and equal readings among the partners that can. -/
def chkPart (P : List Nat → Nat) (C : List Nat → Nat → Nat) (tbl : List (List Nat × Nat × List Nat)) : Bool :=
  forMoves (fun m q m' =>
    checkMask (fun u => (gLook tbl m u).testBit u) 13 0 (P m) &&
    checkMask (fun u =>
      let su := fword (pulse q) (1 <<< u) &&& P m'
      let im := fword (pulse q) (gLook tbl m u) &&& P m'
      checkMask (fun t => subB im (gLook tbl m' t)) 13 0 su) 13 0 (P m) &&
    (fword (pulse q) (P m ^^^ (P m &&& C m q)) &&& P m' == 0) &&
    checkMask (fun u => readsOK (gLook tbl m u &&& C m q) q) 13 0 (C m q))

def c2 (m : List Nat) (_ : Nat) : Nat := p2 m

set_option maxRecDepth 100000 in
theorem chkWarm_ok : chkWarm = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chkRegions_ok : chkRegions = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chkZ0_ok : chkZ z0 t0 z0Len = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chkZ1_ok : chkZ z1 t1 z1Len = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chkP1_ok : chkPart p1 c1 g1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chkP2_ok : chkPart p2 c2 g2 = true := by decide +kernel

/-! ## The true path -/

/-- The gap at position `i` of the cyclic list. -/
def gapAt (qs : List Nat) (i : Nat) : Nat := qs.getD (i % qs.length) 0

/-- No three consecutive 7s and no 7, 9, 7, 9 in the cyclic sequence of gaps. -/
def Clean (qs : List Nat) : Prop := ∀ i,
  ¬ (gapAt qs i = 7 ∧ gapAt qs (i + 1) = 7 ∧ gapAt qs (i + 2) = 7) ∧
  ¬ (gapAt qs i = 7 ∧ gapAt qs (i + 1) = 9 ∧ gapAt qs (i + 2) = 7 ∧ gapAt qs (i + 3) = 9)

/-- The start of block `i`, for an eventual word with its first letter at `T`. -/
def startAt (qs : List Nat) (T i : Nat) : Nat :=
  T + i / qs.length * (blocks qs).length + (blocks (qs.take (i % qs.length))).length

theorem getD_eq {qs : List Nat} {r : Nat} (hr : r < qs.length) : qs.getD r 0 = qs[r] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]

theorem blocks_take_succ {qs : List Nat} {r : Nat} (hr : r < qs.length) :
    blocks (qs.take (r + 1)) = blocks (qs.take r) ++ pulse (qs.getD r 0) := by
  unfold blocks
  rw [List.take_add_one, List.getElem?_eq_getElem hr, getD_eq hr, List.flatMap_append]
  simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem blocks_split {qs : List Nat} {r : Nat} (hr : r < qs.length) :
    blocks qs = blocks (qs.take r) ++ (pulse (qs.getD r 0) ++ blocks (qs.drop (r + 1))) := by
  rw [getD_eq hr]
  unfold blocks
  conv => lhs; rw [← List.take_append_drop r qs, List.drop_eq_getElem_cons hr]
  rw [List.flatMap_append, List.flatMap_cons]

theorem startAt_succ {qs : List Nat} (hn : 0 < qs.length) (T i : Nat) :
    startAt qs T (i + 1) = startAt qs T i + gapAt qs i + 1 := by
  have hr : i % qs.length < qs.length := Nat.mod_lt _ hn
  have e : i + 1 = (i % qs.length + 1) + qs.length * (i / qs.length) := by
    have := Nat.div_add_mod i qs.length; omega
  have hd : (i + 1) / qs.length = (i % qs.length + 1) / qs.length + i / qs.length := by
    rw [e, Nat.add_mul_div_left _ _ hn]
  have hm : (i + 1) % qs.length = (i % qs.length + 1) % qs.length := by
    rw [e, Nat.add_mul_mod_self_left]
  have hs := blocks_take_succ hr
  unfold startAt gapAt
  rw [hd, hm]
  by_cases hc : i % qs.length + 1 < qs.length
  · rw [Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc, hs, List.length_append, pulse_length, Nat.zero_add]; omega
  · have heq : i % qs.length + 1 = qs.length := by omega
    have hall : (blocks qs).length = (blocks (qs.take (i % qs.length))).length + (qs.getD (i % qs.length) 0 + 1) := by
      rw [← pulse_length, ← List.length_append, ← hs, heq, List.take_length]
    rw [heq, Nat.div_self hn, Nat.mod_self, List.take_zero, hall, Nat.add_mul, Nat.one_mul]
    simp [blocks]
    omega

theorem startAt_add {qs : List Nat} (hn : 0 < qs.length) (T i : Nat) :
    startAt qs T (i + qs.length) = startAt qs T i + (blocks qs).length := by
  unfold startAt
  rw [Nat.add_div_right i hn, Nat.add_mod_right, Nat.add_mul, Nat.one_mul]
  omega

theorem startAt_add_mul {qs : List Nat} (hn : 0 < qs.length) (T i : Nat) :
    ∀ c, startAt qs T (i + c * qs.length) = startAt qs T i + c * (blocks qs).length
  | 0 => by simp
  | c + 1 => by
    rw [show i + (c + 1) * qs.length = (i + c * qs.length) + qs.length by rw [Nat.add_mul]; omega,
      startAt_add hn, startAt_add_mul hn T i c, Nat.add_mul]
    omega

theorem gapAt_add_mul (qs : List Nat) (i : Nat) : ∀ c, gapAt qs (i + c * qs.length) = gapAt qs i
  | 0 => by simp
  | c + 1 => by
    rw [show i + (c + 1) * qs.length = (i + c * qs.length) + qs.length by rw [Nat.add_mul]; omega]
    unfold gapAt
    rw [Nat.add_mod_right]
    exact gapAt_add_mul qs i c

theorem reads_block {qs : List Nat} {T : Nat} (hn : 0 < qs.length)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false) (i : Nat) :
    Reads (startAt qs T i) (pulse (gapAt qs i)) := by
  have hb : ∀ m, Reads (T + m * (blocks qs).length) (blocks qs) := by
    intro m j hj
    rw [hT _ (by omega), show T + m * (blocks qs).length + j - T = j + m * (blocks qs).length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hr : i % qs.length < qs.length := Nat.mod_lt _ hn
  have h1 : Reads (T + i / qs.length * (blocks qs).length)
      (blocks (qs.take (i % qs.length)) ++
        (pulse (qs.getD (i % qs.length) 0) ++ blocks (qs.drop (i % qs.length + 1)))) := by
    rw [← blocks_split hr]; exact hb _
  exact reads_left (reads_right h1)

theorem step_mem {qs : List Nat} {T : Nat} (hn : 0 < qs.length)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false)
    {S : Nat} (i : Nat) (hs : S.testBit (code 13 (startAt qs T i)) = true) :
    (fword (pulse (gapAt qs i)) S).testBit (code 13 (startAt qs T (i + 1))) = true := by
  have h := fword_sound (reads_block hn hT i) hs
  rwa [pulse_length, ← Nat.add_assoc, ← startAt_succ hn] at h

theorem prefix_mem {qs : List Nat} {T : Nat} (hn : 0 < qs.length)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false)
    {S : Nat} (i o : Nat) (ho : o ≤ gapAt qs i + 1) (hs : S.testBit (code 13 (startAt qs T i)) = true) :
    (fword ((pulse (gapAt qs i)).take o) S).testBit (code 13 (startAt qs T i + o)) = true := by
  have hr := reads_block hn hT i
  rw [← List.take_append_drop o (pulse (gapAt qs i))] at hr
  have h := fword_sound (reads_left hr) hs
  rwa [List.length_take, pulse_length, Nat.min_eq_left ho] at h

theorem centre_at {qs : List Nat} {T : Nat} (hn : 0 < qs.length)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false)
    (i o : Nat) (ho : o ≤ gapAt qs i) : cell (startAt qs T i + o) 0 = decide (o = 0) := by
  have h := reads_block hn hT i o (by rw [pulse_length]; omega)
  rw [h]
  cases o with
  | zero => rfl
  | succ o => simp [pulse, List.getD_eq_getElem?_getD, show o < gapAt qs i by omega]

theorem cover {qs : List Nat} (hn : 0 < qs.length) (T k0 : Nat) :
    ∀ d, ∃ i o, o ≤ gapAt qs (k0 + i) ∧ startAt qs T k0 + d = startAt qs T (k0 + i) + o
  | 0 => ⟨0, 0, Nat.zero_le _, rfl⟩
  | d + 1 => by
    obtain ⟨i, o, ho, he⟩ := cover hn T k0 d
    by_cases h : o < gapAt qs (k0 + i)
    · exact ⟨i, o + 1, h, by omega⟩
    · refine ⟨i + 1, 0, Nat.zero_le _, ?_⟩
      rw [show k0 + (i + 1) = (k0 + i) + 1 by omega, startAt_succ hn]
      omega

/-! ## Nodes of the true path -/

/-- The strip at block `k + 3`. -/
def nodeX (qs : List Nat) (T k : Nat) : Nat := code 13 (startAt qs T (k + 3))

/-- The three gaps before block `k + 3`. -/
def memAt (qs : List Nat) (k : Nat) : List Nat := [gapAt qs k, gapAt qs (k + 1), gapAt qs (k + 2)]

/-- The gap of block `k + 3`. -/
def gapQ (qs : List Nat) (k : Nat) : Nat := gapAt qs (k + 3)

theorem memAt_next (qs : List Nat) (k : Nat) : next (memAt qs k) (gapQ qs k) = memAt qs (k + 1) := by
  simp [next, memAt, gapQ]

theorem gap79 {qs : List Nat} (hn : 0 < qs.length) (h79 : ∀ q ∈ qs, q = 7 ∨ q = 9) (i : Nat) :
    gapAt qs i = 7 ∨ gapAt qs i = 9 := by
  unfold gapAt
  have hr : i % qs.length < qs.length := Nat.mod_lt _ hn
  rw [getD_eq hr]
  exact h79 _ (List.getElem_mem hr)

theorem memAt_ok {qs : List Nat} (hn : 0 < qs.length) (h79 : ∀ q ∈ qs, q = 7 ∨ q = 9) (hcl : Clean qs)
    (k : Nat) : memAt qs k ∈ mems ∧ allowed (memAt qs k) (gapQ qs k) = true ∧
      (gapQ qs k = 7 ∨ gapQ qs k = 9) := by
  have c0 := hcl k
  have c1 := hcl (k + 1)
  rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega] at c1
  unfold memAt gapQ
  rcases gap79 hn h79 k with e0 | e0 <;> rcases gap79 hn h79 (k + 1) with e1 | e1 <;>
    rcases gap79 hn h79 (k + 2) with e2 | e2 <;> rcases gap79 hn h79 (k + 3) with e3 | e3 <;>
    simp only [e0, e1, e2, e3] at c0 c1 ⊢ <;> simp_all (config := { decide := true })

theorem stepX {qs : List Nat} {T : Nat} (hn : 0 < qs.length)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false)
    {S : Nat} (k : Nat) (hs : S.testBit (nodeX qs T k) = true) :
    (fword (pulse (gapQ qs k)) S).testBit (nodeX qs T (k + 1)) = true := by
  have h := step_mem hn hT (k + 3) hs
  rwa [show k + 3 + 1 = k + 1 + 3 by omega] at h

/-! ## Reading the certificate along the path -/

theorem regions_spec {m : List Nat} {q : Nat} (hm : m ∈ mems) (hq : q = 7 ∨ q = 9) (ha : allowed m q = true) :
    Sub (fword (pulse q) (lvl0 m)) (lvl0 (next m q)) ∧ Sub (fword (pulse q) (lvl01 m)) (lvl01 (next m q)) ∧
    Sub (fword (pulse q) (last m)) (last (next m q)) ∧ Sub (fword (pulse q) (bS m)) (bS (next m q)) ∧
    Sub (fword (pulse q) (p1 m) &&& lv1 (next m q)) (p1 (next m q)) ∧ readsOK (bS m) q = true := by
  have h := forMoves_spec chkRegions_ok hm hq ha
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨fun _ => subB_sound h1, fun _ => subB_sound h2, fun _ => subB_sound h3, fun _ => subB_sound h4,
    fun _ => subB_sound h5, h6⟩

theorem zspec {z : Nat → List Nat → Nat} {t : List Nat → Nat} {len : Nat} (h : chkZ z t len = true) :
    (∀ m, m ∈ mems → z 0 m = t m ∧ z len m = 0) ∧
    ∀ m q, m ∈ mems → (q = 7 ∨ q = 9) → allowed m q = true → ∀ j, j < len →
      Sub (fword (pulse q) (z j m) &&& t (next m q)) (z (j + 1) (next m q)) := by
  unfold chkZ at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun m hm => ?_, fun m q hm hq ha j hj => ?_⟩
  · have := List.all_eq_true.mp h.2 m hm
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this
  · have h1 := forMoves_spec h.1 hm hq ha
    have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
    exact fun _ => subB_sound h2

/-- Closure of a family of sets along the path. -/
theorem along {qs : List Nat} {T : Nat} (hn : 0 < qs.length) (h79 : ∀ q ∈ qs, q = 7 ∨ q = 9) (hcl : Clean qs)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false)
    {A : List Nat → Nat}
    (hA : ∀ m q, m ∈ mems → (q = 7 ∨ q = 9) → allowed m q = true →
      Sub (fword (pulse q) (A m)) (A (next m q)))
    (k : Nat) (h : (A (memAt qs k)).testBit (nodeX qs T k) = true) :
    (A (memAt qs (k + 1))).testBit (nodeX qs T (k + 1)) = true := by
  obtain ⟨hm, ha, hq⟩ := memAt_ok hn h79 hcl k
  rw [← memAt_next]
  exact hA _ _ hm hq ha _ (stepX hn hT k h)

/-! ## From two related paths to a periodic masked column -/

theorem blocks_length_pos {qs : List Nat} (hne : qs ≠ []) : 0 < (blocks qs).length := by
  cases qs with
  | nil => exact (hne rfl).elim
  | cons q rest => simp [blocks, pulse]

theorem periodic_of_pairs {qs : List Nat} {T : Nat} (hn : 0 < qs.length) (hL : 0 < (blocks qs).length)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false)
    (a c : Nat) (hc : 0 < c) (S : Nat → Nat)
    (hX : ∀ l, (S l).testBit (nodeX qs T (a + l)) = true)
    (hY : ∀ l, (S l).testBit (nodeX qs T (a + c * qs.length + l)) = true)
    (hR : ∀ l, readsOK (S l) (gapQ qs (a + l)) = true) :
    EventuallyPeriodic (fun t => orCol 0 t) := by
  refine ⟨startAt qs T (a + 3), c * (blocks qs).length, Nat.mul_pos hc hL, fun t ht => ?_⟩
  obtain ⟨i, o, ho, he⟩ := cover hn T (a + 3) (t - startAt qs T (a + 3))
  have ht' : t = startAt qs T (a + 3 + i) + o := by omega
  have hshift : t + c * (blocks qs).length = startAt qs T (a + c * qs.length + i + 3) + o := by
    rw [show a + c * qs.length + i + 3 = (a + 3 + i) + c * qs.length by omega, startAt_add_mul hn]
    omega
  have hgap : gapAt qs (a + c * qs.length + i + 3) = gapAt qs (a + 3 + i) := by
    rw [show a + c * qs.length + i + 3 = (a + 3 + i) + c * qs.length by omega, gapAt_add_mul]
  have ho' : o ≤ gapAt qs (a + c * qs.length + i + 3) := by rw [hgap]; exact ho
  show (cell (t + c * (blocks qs).length) 0 || cell (t + c * (blocks qs).length) (0 + 1)) =
    (cell t 0 || cell t (0 + 1))
  rw [hshift, ht', centre_at hn hT _ _ ho, centre_at hn hT _ _ ho']
  rcases Nat.eq_zero_or_pos o with rfl | hpos
  · rfl
  · have hz : decide (o = 0) = false := by simp; omega
    rw [hz, Bool.false_or, Bool.false_or, show (0 : Int) + 1 = 1 by rfl, ← code_bit0, ← code_bit0]
    have hq : gapQ qs (a + i) = gapAt qs (a + 3 + i) := by unfold gapQ; congr 1; omega
    have hconst := readsOK_sound (hR i) hpos (by rw [hq]; exact ho)
    rw [hq] at hconst
    have m1 := prefix_mem hn hT (S := S i) (a + 3 + i) o (by omega)
      (by have := hX i; unfold nodeX at this; rwa [show a + i + 3 = a + 3 + i by omega] at this)
    have m2 := prefix_mem hn hT (S := S i) (a + c * qs.length + i + 3) o (by omega)
      (by have := hY i; unfold nodeX at this; exact this)
    rw [hgap] at m2
    exact const0_sound hconst (code_lt _) (code_lt _) m2 m1

/-! ## Pigeonhole -/

/-- Pigeonhole, as the kit's private `Rule30EveryKInverse.collision`. -/
theorem collision (N : Nat) (a : Nat → Nat) (h : ∀ t, a t < N) :
    ∃ i j, i < j ∧ j ≤ N ∧ a i = a j := by
  apply Classical.byContradiction
  intro hn
  have nd := Rule30Jen.nodup_map_of_inj a (List.nodup_range (n := N + 1)) (by
    intro i hi j hj e
    simp only [List.mem_range] at hi hj
    rcases Nat.lt_trichotomy i j with lt | eq | gt
    · exact (hn ⟨i, j, lt, by omega, e⟩).elim
    · exact eq
    · exact (hn ⟨j, i, gt, by omega, e.symm⟩).elim)
  have size := Rule30Jen.length_le_of_subset (l₂ := List.range N) nd (by
    intro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (h t))
  simp at size
  omega

/-! ## The three kinds of part -/

theorem memAt_add_mul (qs : List Nat) (k c : Nat) : memAt qs (k + c * qs.length) = memAt qs k := by
  unfold memAt
  rw [show k + c * qs.length + 1 = (k + 1) + c * qs.length by omega,
    show k + c * qs.length + 2 = (k + 2) + c * qs.length by omega, gapAt_add_mul, gapAt_add_mul, gapAt_add_mul]

theorem gapQ_add_mul (qs : List Nat) (k c : Nat) : gapQ qs (k + c * qs.length) = gapQ qs k := by
  unfold gapQ
  rw [show k + c * qs.length + 3 = (k + 3) + c * qs.length by omega, gapAt_add_mul]

theorem sink_periodic {qs : List Nat} {T : Nat} (hn : 0 < qs.length) (hL : 0 < (blocks qs).length)
    (h79 : ∀ q ∈ qs, q = 7 ∨ q = 9) (hcl : Clean qs)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false)
    {k3 : Nat} (hin : ∀ k, k3 ≤ k → (bS (memAt qs k)).testBit (nodeX qs T k) = true) :
    EventuallyPeriodic (fun t => orCol 0 t) := by
  apply periodic_of_pairs hn hL hT k3 1 (by decide) (fun l => bS (memAt qs (k3 + l)))
  · intro l; exact hin _ (by omega)
  · intro l
    have h := hin (k3 + 1 * qs.length + l) (by omega)
    have e : memAt qs (k3 + 1 * qs.length + l) = memAt qs (k3 + l) := by
      rw [show k3 + 1 * qs.length + l = (k3 + l) + 1 * qs.length by omega, memAt_add_mul]
    rwa [e] at h
  · intro l
    obtain ⟨hm, ha, hq⟩ := memAt_ok hn h79 hcl (k3 + l)
    exact (regions_spec hm hq ha).2.2.2.2.2

theorem part_periodic {qs : List Nat} {T : Nat} (hn : 0 < qs.length) (hL : 0 < (blocks qs).length)
    (h79 : ∀ q ∈ qs, q = 7 ∨ q = 9) (hcl : Clean qs)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false)
    {P : List Nat → Nat} {C : List Nat → Nat → Nat} {tbl : List (List Nat × Nat × List Nat)}
    (hchk : chkPart P C tbl = true)
    {k3 : Nat} (hin : ∀ k, k3 ≤ k → (P (memAt qs k)).testBit (nodeX qs T k) = true) :
    EventuallyPeriodic (fun t => orCol 0 t) := by
  -- the four checks at the moves of the path
  have spec : ∀ k,
      (∀ u, u < 2 ^ 13 → (P (memAt qs k)).testBit u = true → (gLook tbl (memAt qs k) u).testBit u = true) ∧
      (∀ u, u < 2 ^ 13 → (P (memAt qs k)).testBit u = true → ∀ t, t < 2 ^ 13 →
        (fword (pulse (gapQ qs k)) (1 <<< u) &&& P (next (memAt qs k) (gapQ qs k))).testBit t = true →
        subB (fword (pulse (gapQ qs k)) (gLook tbl (memAt qs k) u) &&& P (next (memAt qs k) (gapQ qs k)))
          (gLook tbl (next (memAt qs k) (gapQ qs k)) t) = true) ∧
      (fword (pulse (gapQ qs k)) (P (memAt qs k) ^^^ (P (memAt qs k) &&& C (memAt qs k) (gapQ qs k))) &&&
        P (next (memAt qs k) (gapQ qs k)) = 0) ∧
      (∀ u, u < 2 ^ 13 → (C (memAt qs k) (gapQ qs k)).testBit u = true →
        readsOK (gLook tbl (memAt qs k) u &&& C (memAt qs k) (gapQ qs k)) (gapQ qs k) = true) := by
    intro k
    obtain ⟨hm, ha, hq⟩ := memAt_ok hn h79 hcl k
    have h := forMoves_spec hchk hm hq ha
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨fun u hu hp => ?_, fun u hu hp t ht hs => ?_, h3, fun u hu hc => ?_⟩
    · simpa using checkMask_spec _ 13 0 _ h1 u hu hp
    · have := checkMask_spec _ 13 0 _ h2 u hu hp
      simp only [Nat.zero_add] at this
      simpa using checkMask_spec _ 13 0 _ this t ht hs
    · simpa using checkMask_spec _ 13 0 _ h4 u hu hc
  -- every node of the path from k3 on can stay in the part, so it lies in C
  have inC : ∀ k, k3 ≤ k → (C (memAt qs k) (gapQ qs k)).testBit (nodeX qs T k) = true := by
    intro k hk
    apply Classical.byContradiction
    intro hc
    have hc' : (C (memAt qs k) (gapQ qs k)).testBit (nodeX qs T k) = false := by simpa using hc
    have hx : (P (memAt qs k) ^^^ (P (memAt qs k) &&& C (memAt qs k) (gapQ qs k))).testBit
        (nodeX qs T k) = true := by
      rw [Nat.testBit_xor, Nat.testBit_and, hin k hk, hc']; rfl
    have h1 := stepX hn hT k hx
    have h2 := hin (k + 1) (by omega)
    rw [← memAt_next] at h2
    have h3 : (fword (pulse (gapQ qs k)) (P (memAt qs k) ^^^ (P (memAt qs k) &&& C (memAt qs k) (gapQ qs k))) &&&
        P (next (memAt qs k) (gapQ qs k))).testBit (nodeX qs T (k + 1)) = true := by
      rw [Nat.testBit_and, h1, h2]; rfl
    rw [(spec k).2.2.1, Nat.zero_testBit] at h3
    exact absurd h3 (by decide)
  -- pigeonhole at period boundaries
  obtain ⟨i, j, hij, -, he⟩ := collision (2 ^ 13) (fun j => nodeX qs T (k3 + j * qs.length)) (fun _ => code_lt _)
  have hb : ∀ l, k3 + i * qs.length + (j - i) * qs.length + l =
      (k3 + i * qs.length + l) + (j - i) * qs.length := fun l => by omega
  have hmem : ∀ l, memAt qs (k3 + i * qs.length + (j - i) * qs.length + l) = memAt qs (k3 + i * qs.length + l) :=
    fun l => by rw [hb, memAt_add_mul]
  have hgq : ∀ l, gapQ qs (k3 + i * qs.length + (j - i) * qs.length + l) = gapQ qs (k3 + i * qs.length + l) :=
    fun l => by rw [hb, gapQ_add_mul]
  have hab : k3 + i * qs.length + (j - i) * qs.length = k3 + j * qs.length := by
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' (Nat.le_of_lt hij)]
  -- the two paths stay partners
  have pair : ∀ l, (gLook tbl (memAt qs (k3 + i * qs.length + l)) (nodeX qs T (k3 + i * qs.length + l))).testBit
      (nodeX qs T (k3 + i * qs.length + (j - i) * qs.length + l)) = true := by
    intro l
    induction l with
    | zero =>
      rw [Nat.add_zero, Nat.add_zero, hab, ← he]
      exact (spec _).1 _ (code_lt _) (hin _ (by omega))
    | succ l ih =>
      have sp := spec (k3 + i * qs.length + l)
      have ht1 := stepX hn hT (S := 1 <<< nodeX qs T (k3 + i * qs.length + l)) (k3 + i * qs.length + l)
        (testBit_single _)
      have ht2 := hin (k3 + i * qs.length + l + 1) (by omega)
      rw [← memAt_next] at ht2
      have hsucc : (fword (pulse (gapQ qs (k3 + i * qs.length + l))) (1 <<< nodeX qs T (k3 + i * qs.length + l)) &&&
          P (next (memAt qs (k3 + i * qs.length + l)) (gapQ qs (k3 + i * qs.length + l)))).testBit
            (nodeX qs T (k3 + i * qs.length + l + 1)) = true := by
        rw [Nat.testBit_and, ht1, ht2]; rfl
      have hcl' := sp.2.1 _ (code_lt _) (hin _ (by omega)) _ (code_lt _) hsucc
      have hy1 := stepX hn hT (k3 + i * qs.length + (j - i) * qs.length + l) ih
      rw [hgq] at hy1
      have hy2 := hin (k3 + i * qs.length + (j - i) * qs.length + l + 1) (by omega)
      rw [show k3 + i * qs.length + (j - i) * qs.length + l + 1 =
          k3 + i * qs.length + (j - i) * qs.length + (l + 1) by omega, hmem,
        show k3 + i * qs.length + (l + 1) = k3 + i * qs.length + l + 1 by omega, ← memAt_next] at hy2
      rw [show k3 + i * qs.length + (j - i) * qs.length + l + 1 =
          k3 + i * qs.length + (j - i) * qs.length + (l + 1) by omega] at hy1
      have hy : (fword (pulse (gapQ qs (k3 + i * qs.length + l)))
          (gLook tbl (memAt qs (k3 + i * qs.length + l)) (nodeX qs T (k3 + i * qs.length + l))) &&&
          P (next (memAt qs (k3 + i * qs.length + l)) (gapQ qs (k3 + i * qs.length + l)))).testBit
            (nodeX qs T (k3 + i * qs.length + (j - i) * qs.length + (l + 1))) = true := by
        rw [Nat.testBit_and, hy1, hy2]; rfl
      have := subB_sound hcl' hy
      rwa [memAt_next, show k3 + i * qs.length + l + 1 = k3 + i * qs.length + (l + 1) by omega] at this
  apply periodic_of_pairs hn hL hT (k3 + i * qs.length) (j - i) (by omega)
    (fun l => gLook tbl (memAt qs (k3 + i * qs.length + l)) (nodeX qs T (k3 + i * qs.length + l)) &&&
      C (memAt qs (k3 + i * qs.length + l)) (gapQ qs (k3 + i * qs.length + l)))
  · intro l
    have hd := (spec (k3 + i * qs.length + l)).1 (nodeX qs T (k3 + i * qs.length + l)) (code_lt _)
      (hin (k3 + i * qs.length + l) (by omega))
    rw [Nat.testBit_and, hd, inC (k3 + i * qs.length + l) (by omega)]; rfl
  · intro l
    have hc := inC (k3 + i * qs.length + (j - i) * qs.length + l) (by omega)
    rw [hmem, hgq] at hc
    rw [Nat.testBit_and, pair l, hc]; rfl
  · intro l
    exact (spec (k3 + i * qs.length + l)).2.2.2 (nodeX qs T (k3 + i * qs.length + l)) (code_lt _)
      (inC (k3 + i * qs.length + l) (by omega))

/-! ## Transients do not last -/

theorem eventually_in {inP inT : Nat → Prop} {Z : Nat → Nat → Prop} {k1 L : Nat}
    (hPT : ∀ k, k1 ≤ k → inP k ∨ inT k) (hP : ∀ k, k1 ≤ k → inP k → inP (k + 1))
    (hZ0 : ∀ k, inT k → Z 0 k) (hZ : ∀ k j, k1 ≤ k → j < L → Z j k → inT (k + 1) → Z (j + 1) (k + 1))
    (hZL : ∀ k, ¬ Z L k) : ∀ k, k1 + L ≤ k → inP k := by
  intro k hk
  apply Classical.byContradiction
  intro hnot
  have hnp : ∀ j, j ≤ L → ¬ inP (k - L + j) := by
    intro j hj hp
    have up : ∀ e, inP (k - L + j + e) := by
      intro e
      induction e with
      | zero => exact hp
      | succ e ih => exact hP (k - L + j + e) (by omega) ih
    have := up (L - j)
    rw [show k - L + j + (L - j) = k by omega] at this
    exact hnot this
  have hzj : ∀ j, j ≤ L → Z j (k - L + j) := by
    intro j hj
    induction j with
    | zero => exact hZ0 _ ((hPT _ (by omega)).resolve_left (hnp 0 (by omega)))
    | succ j ih =>
      have hT' : inT (k - L + j + 1) := by
        have := (hPT (k - L + (j + 1)) (by omega)).resolve_left (hnp (j + 1) hj)
        rwa [show k - L + (j + 1) = k - L + j + 1 by omega] at this
      have := hZ (k - L + j) j (by omega) (by omega) (ih (by omega)) hT'
      rwa [show k - L + j + 1 = k - L + (j + 1) by omega] at this
  have := hzj L (Nat.le_refl _)
  rw [show k - L + L = k by omega] at this
  exact hZL _ this

/-! ## Levels -/

def lev (qs : List Nat) (T k : Nat) : Nat :=
  if (lvl0 (memAt qs k)).testBit (nodeX qs T k) = true then 0
  else if (lvl01 (memAt qs k)).testBit (nodeX qs T k) = true then 1 else 2

theorem lev_mono {qs : List Nat} {T : Nat} (hn : 0 < qs.length) (h79 : ∀ q ∈ qs, q = 7 ∨ q = 9) (hcl : Clean qs)
    (hT : ∀ t, T ≤ t → cell t 0 = (blocks qs).getD ((t - T) % (blocks qs).length) false) (k : Nat) :
    lev qs T (k + 1) ≤ lev qs T k := by
  have c0 := along hn h79 hcl hT (A := lvl0) (fun m q hm hq ha => (regions_spec hm hq ha).1) k
  have c1 := along hn h79 hcl hT (A := lvl01) (fun m q hm hq ha => (regions_spec hm hq ha).2.1) k
  unfold lev
  by_cases h0 : (lvl0 (memAt qs k)).testBit (nodeX qs T k) = true
  · simp only [c0 h0, ↓reduceIte]; exact Nat.zero_le _
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : (lvl01 (memAt qs k)).testBit (nodeX qs T k) = true
    · simp only [h1, c1 h1, ↓reduceIte]
      split <;> omega
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      split
      · omega
      · split <;> omega

/-! ## The theorem -/

/-- **No cyclic mixture of 7-gaps and 9-gaps with no 7,7,7 and no 7,9,7,9 is an eventual centre clock.** -/
theorem excludes_language (qs : List Nat) (hne : qs ≠ []) (h79 : ∀ q ∈ qs, q = 7 ∨ q = 9) (hcl : Clean qs) :
    ¬ EventuallyWord (blocks qs) := by
  intro hw
  have hn : 0 < qs.length := List.length_pos_iff.mpr hne
  have hL := blocks_length_pos hne
  have hbne : blocks qs ≠ [] := fun h => by rw [h] at hL; exact absurd hL (by decide)
  have hper := eventuallyPeriodic_of_word hbne hw
  apply orCol_not_eventuallyPeriodic 0 hper
  obtain ⟨T, hT⟩ := hw
  -- warm-up into the lasting nodes
  have hchk := chkWarm_ok
  unfold chkWarm at hchk
  simp only [Bool.and_eq_true] at hchk
  have hwarm : ∀ i, i ≤ warmRounds → (W i (memAt qs (2 * i))).testBit (nodeX qs T (2 * i)) = true := by
    intro i hi
    induction i with
    | zero =>
      unfold W
      simp only [↓reduceIte]; rw [testBit_fullSet]; exact decide_eq_true (code_lt _)
    | succ i ih =>
      have hw := ih (by omega)
      obtain ⟨hm, ha, hq⟩ := memAt_ok hn h79 hcl (2 * i)
      obtain ⟨_, ha1, hq1⟩ := memAt_ok hn h79 hcl (2 * i + 1)
      have s1 := stepX hn hT (2 * i) hw
      have s2 := stepX hn hT (2 * i + 1) s1
      rw [← fword_append] at s2
      have h1 := List.all_eq_true.mp hchk.1 i (List.mem_range.mpr (by omega))
      have h2 := forMoves_spec h1 hm hq ha
      rw [memAt_next] at h2
      have h3 := List.all_eq_true.mp h2 (gapQ qs (2 * i + 1)) (by rcases hq1 with h | h <;> simp [h])
      simp only [ha1, Bool.not_true, Bool.false_or] at h3
      have := subB_sound h3 s2
      rwa [memAt_next, show 2 * i + 1 + 1 = 2 * (i + 1) by omega] at this
  have hlast0 : (last (memAt qs (2 * warmRounds))).testBit (nodeX qs T (2 * warmRounds)) = true := by
    have := List.all_eq_true.mp hchk.2 _ (memAt_ok hn h79 hcl (2 * warmRounds)).1
    exact subB_sound this (hwarm _ (Nat.le_refl _))
  have hlast : ∀ k, 2 * warmRounds ≤ k → (last (memAt qs k)).testBit (nodeX qs T k) = true := by
    intro k hk
    obtain ⟨d, rfl⟩ : ∃ d, k = 2 * warmRounds + d := ⟨k - 2 * warmRounds, by omega⟩
    clear hk
    induction d with
    | zero => exact hlast0
    | succ d ih =>
      exact along hn h79 hcl hT (A := last) (fun m q hm hq ha => (regions_spec hm hq ha).2.2.1) _ ih
  -- the level is eventually constant
  obtain ⟨k1, -, hk1⟩ := antitone_eventually_const (lev qs T) 0 (fun t _ => lev_mono hn h79 hcl hT t)
  have hle : lev qs T k1 ≤ 2 := by
    unfold lev; split
    · omega
    · split <;> omega
  rcases (show lev qs T k1 = 0 ∨ lev qs T k1 = 1 ∨ lev qs T k1 = 2 by omega) with h0 | h1 | h2
  · -- level 0: the sink part, after its transients
    have in0 : ∀ k, k1 ≤ k → (lvl0 (memAt qs k)).testBit (nodeX qs T k) = true := by
      intro k hk
      have := hk1 k hk
      rw [h0] at this
      unfold lev at this
      split at this
      · assumption
      · split at this <;> omega
    obtain ⟨hz0, hzs⟩ := zspec chkZ0_ok
    apply sink_periodic hn hL h79 hcl hT (k3 := k1 + z0Len)
    refine eventually_in (inP := fun k => (bS (memAt qs k)).testBit (nodeX qs T k) = true)
      (inT := fun k => (t0 (memAt qs k)).testBit (nodeX qs T k) = true)
      (Z := fun j k => (z0 j (memAt qs k)).testBit (nodeX qs T k) = true) (k1 := k1) (L := z0Len) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have := in0 k hk
      unfold lvl0 at this
      rw [Nat.testBit_or] at this
      exact Bool.or_eq_true_iff.mp this
    · intro k _ h
      exact along hn h79 hcl hT (A := bS) (fun m q hm hq ha => (regions_spec hm hq ha).2.2.2.1) k h
    · intro k h
      show (z0 0 (memAt qs k)).testBit _ = true
      rw [(hz0 _ (memAt_ok hn h79 hcl k).1).1]; exact h
    · intro k j _ hj hz ht
      obtain ⟨hm, ha, hq⟩ := memAt_ok hn h79 hcl k
      have s := stepX hn hT k hz
      show (z0 (j + 1) (memAt qs (k + 1))).testBit _ = true
      change (t0 (memAt qs (k + 1))).testBit _ = true at ht
      rw [← memAt_next] at ht ⊢
      have hand : (fword (pulse (gapQ qs k)) (z0 j (memAt qs k)) &&& t0 (next (memAt qs k) (gapQ qs k))).testBit
          (nodeX qs T (k + 1)) = true := by rw [Nat.testBit_and, s, ht]; rfl
      exact hzs _ _ hm hq ha j hj _ hand
    · intro k h
      change (z0 z0Len (memAt qs k)).testBit _ = true at h
      rw [(hz0 _ (memAt_ok hn h79 hcl k).1).2, Nat.zero_testBit] at h
      exact absurd h (by decide)
  · -- level 1: the part of 126, after its transients
    have in1 : ∀ k, k1 ≤ k → (lv1 (memAt qs k)).testBit (nodeX qs T k) = true := by
      intro k hk
      have := hk1 k hk
      rw [h1] at this
      unfold lev at this
      split at this
      · omega
      · rename_i hn0
        split at this
        · rename_i h01
          unfold lvl01 at h01
          rw [Nat.testBit_or] at h01
          rcases Bool.or_eq_true_iff.mp h01 with h | h
          · exact absurd h hn0
          · exact h
        · omega
    obtain ⟨hz0, hzs⟩ := zspec chkZ1_ok
    apply part_periodic hn hL h79 hcl hT chkP1_ok (k3 := k1 + z1Len)
    refine eventually_in (inP := fun k => (p1 (memAt qs k)).testBit (nodeX qs T k) = true)
      (inT := fun k => (t1 (memAt qs k)).testBit (nodeX qs T k) = true)
      (Z := fun j k => (z1 j (memAt qs k)).testBit (nodeX qs T k) = true) (k1 := k1) (L := z1Len) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have := in1 k hk
      unfold lv1 at this
      rw [Nat.testBit_or] at this
      exact Bool.or_eq_true_iff.mp this
    · intro k hk h
      obtain ⟨hm, ha, hq⟩ := memAt_ok hn h79 hcl k
      have s := stepX hn hT k h
      have hl := in1 (k + 1) (by omega)
      rw [← memAt_next] at hl ⊢
      have hand : (fword (pulse (gapQ qs k)) (p1 (memAt qs k)) &&& lv1 (next (memAt qs k) (gapQ qs k))).testBit
          (nodeX qs T (k + 1)) = true := by rw [Nat.testBit_and, s, hl]; rfl
      exact (regions_spec hm hq ha).2.2.2.2.1 _ hand
    · intro k h
      show (z1 0 (memAt qs k)).testBit _ = true
      rw [(hz0 _ (memAt_ok hn h79 hcl k).1).1]; exact h
    · intro k j _ hj hz ht
      obtain ⟨hm, ha, hq⟩ := memAt_ok hn h79 hcl k
      have s := stepX hn hT k hz
      show (z1 (j + 1) (memAt qs (k + 1))).testBit _ = true
      change (t1 (memAt qs (k + 1))).testBit _ = true at ht
      rw [← memAt_next] at ht ⊢
      have hand : (fword (pulse (gapQ qs k)) (z1 j (memAt qs k)) &&& t1 (next (memAt qs k) (gapQ qs k))).testBit
          (nodeX qs T (k + 1)) = true := by rw [Nat.testBit_and, s, ht]; rfl
      exact hzs _ _ hm hq ha j hj _ hand
    · intro k h
      change (z1 z1Len (memAt qs k)).testBit _ = true at h
      rw [(hz0 _ (memAt_ok hn h79 hcl k).1).2, Nat.zero_testBit] at h
      exact absurd h (by decide)
  · -- level 2: the part of 29
    apply part_periodic hn hL h79 hcl hT chkP2_ok (k3 := k1 + 2 * warmRounds)
    intro k hk
    have hl := hlast k (by omega)
    have := hk1 k (by omega)
    rw [h2] at this
    unfold lev at this
    split at this
    · omega
    · split at this
      · omega
      · rename_i _ h01
        unfold last at hl
        rw [Nat.testBit_or] at hl
        rcases Bool.or_eq_true_iff.mp hl with h | h
        · exact absurd h h01
        · exact h

/-! ## A decidable form, and two clocks no earlier result reaches -/

/-- `Clean`, checked on the windows that start in one period. -/
def cleanB (qs : List Nat) : Bool := (List.range qs.length).all (fun i =>
  !(gapAt qs i == 7 && gapAt qs (i + 1) == 7 && gapAt qs (i + 2) == 7) &&
  !(gapAt qs i == 7 && gapAt qs (i + 1) == 9 && gapAt qs (i + 2) == 7 && gapAt qs (i + 3) == 9))

theorem clean_of_cleanB {qs : List Nat} (hn : 0 < qs.length) (h : cleanB qs = true) : Clean qs := by
  intro i
  have e : ∀ d, gapAt qs (i + d) = gapAt qs (i % qs.length + d) := fun d => by
    unfold gapAt; rw [Nat.mod_add_mod]
  have h1 := List.all_eq_true.mp h (i % qs.length) (List.mem_range.mpr (Nat.mod_lt _ hn))
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h1
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3
  simp only [Nat.add_zero] at e0
  rw [e0, e1, e2, e3]
  constructor
  · rintro ⟨a, b, c⟩
    rcases h1.1 with (⟨x | x⟩ | x) <;> simp_all
  · rintro ⟨a, b, c, d⟩
    rcases h1.2 with ((x | x) | x) | x <;> simp_all

/-- The 26-tick clock `1 0^7 1 0^7 1 0^9`. -/
theorem clock_779 : ¬ EventuallyWord (blocks [7, 7, 9]) :=
  excludes_language _ (by simp) (by decide) (clean_of_cleanB (by decide) (by decide))

/-- The 36-tick clock `1 0^7 1 0^7 1 0^9 1 0^9`. -/
theorem clock_7799 : ¬ EventuallyWord (blocks [7, 7, 9, 9]) :=
  excludes_language _ (by simp) (by decide) (clean_of_cleanB (by decide) (by decide))

end Ruliology.CellularAutomata.Rule30SevenNineLanguage
