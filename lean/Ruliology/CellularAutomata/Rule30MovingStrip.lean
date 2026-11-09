module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30RingOrbits

/-!
# Rule 30: Strip potential transducers and verified packed RUP refutations

This module provides the verified SAT/RUP certificate replayer and the finite-strip potential
transducer framework used to certify linear upper bounds on spatial word counts for periodic
travelling waves.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30MovingStrip

open Ruliology.CellularAutomata.Rule30RingOrbits

set_option linter.all false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- ==================== FAST RUP CHECKER ====================
def Lit (a : Nat → Bool) (l : Nat) : Prop := a (l / 2) = (l % 2 == 1)
def Models (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, Lit a l
def ModelsMask (a : Nat → Bool) (c : Nat) : Prop := ∃ l, c.testBit l = true ∧ Lit a l
def AllFalseMask (a : Nat → Bool) (xs : Nat) : Prop := ∀ l, xs.testBit l = true → ¬ Lit a l
def Known (getClause : Nat → Nat) (a : Nat → Bool) (bound : Nat) : Prop :=
  ∀ i < bound, ModelsMask a (getClause i)
def flipLit (u : Nat) : Nat := Nat.xor u (nat_lit 1)
def strictNat {α : Type} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k+1 => f (Nat.add k 1)
@[simp] theorem strictNat_eq {α : Type} (n : Nat) (f : Nat → α) : strictNat n f = f n := by
  cases n <;> rfl
def subsetMask (c xs : Nat) : Bool := Nat.beq (Nat.land c xs) c
def branch (mid : Nat) (left right : Nat → Nat) (i : Nat) : Nat :=
  bif Nat.ble i mid then left i else right i
noncomputable def checkFormula (getClause : Nat → Nat) (cs : List (List Nat)) (idx : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun _ => true)
    (fun c _ recurse idx => strictNat idx fun idx => strictNat (getClause idx) fun mask =>
      c.all (fun l => mask.testBit l) && recurse (Nat.add idx 1)) cs idx
theorem checkFormula_cons (getClause : Nat → Nat) (c : List Nat) (cs : List (List Nat)) (idx : Nat) :
    checkFormula getClause (c::cs) idx =
      strictNat idx (fun idx => strictNat (getClause idx) (fun mask =>
        c.all (fun l => mask.testBit l) && checkFormula getClause cs (idx+1))) := rfl
theorem checkFormula_append_ok {getClause : Nat → Nat} {left right : List (List Nat)} {idx : Nat}
    (hl : checkFormula getClause left idx = true)
    (hr : checkFormula getClause right (idx + left.length) = true) :
    checkFormula getClause (left ++ right) idx = true := by
  induction left generalizing idx with
  | nil => simpa using hr
  | cons c cs ih =>
    simp only [List.cons_append]
    rw [checkFormula_cons,strictNat_eq,strictNat_eq] at hl ⊢
    rcases Bool.and_eq_true_iff.mp hl with ⟨hc,ht⟩
    apply Bool.and_eq_true_iff.mpr
    exact ⟨hc,ih ht (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hr)⟩
theorem flipLit_sound {a : Nat → Bool} {u : Nat} (hu : Lit a u) : ¬ Lit a (flipLit u) := by
  have beq_false (v : Nat) (hn : v ≠ 1) : (v == 1) = false := by
    cases hb : (v == 1)
    · rfl
    · exact False.elim (hn (Nat.eq_of_beq_eq_true hb))
  have hd : (u ^^^ 1) / 2 = u / 2 := by rw [Nat.xor_div_two]; simp
  have hm : (u ^^^ 1) % 2 = 1 ↔ ¬ u % 2 = 1 := by
    simpa using (Nat.xor_mod_two_eq_one (a := u) (b := 1))
  intro hv
  unfold Lit at hu hv
  unfold flipLit at hv
  change a ((u ^^^ 1) / 2) = ((u ^^^ 1) % 2 == 1) at hv
  rw [hd] at hv
  by_cases hh : u % 2 = 1
  · have hx : (u ^^^ 1) % 2 ≠ 1 := fun h => hm.mp h hh
    have ha : a (u / 2) = true := by simpa [hh] using hu
    have hb : a (u / 2) = false := by simpa only [beq_false _ hx] using hv
    exact Bool.noConfusion (ha.symm.trans hb)
  · have hx : (u ^^^ 1) % 2 = 1 := hm.mpr hh
    have ha : a (u / 2) = false := by simpa only [beq_false _ hh] using hu
    have hb : a (u / 2) = true := by simpa [hx] using hv
    exact Bool.noConfusion (ha.symm.trans hb)
theorem subsetMask_sound {c xs : Nat} (h : subsetMask c xs = true) :
    ∀ l, c.testBit l = true → xs.testBit l = true := by
  rw [subsetMask] at h
  have he : c &&& xs = c := Nat.eq_of_beq_eq_true h
  intro l hl
  have ht := congrArg (fun n : Nat => n.testBit l) he
  simpa only [Nat.testBit_and,hl,Bool.true_and] using ht
theorem singleton_bit {u l : Nat} (h : (1 <<< u : Nat).testBit l = true) : l=u := by
  simp only [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq,
    Nat.testBit_one_eq_true_iff_self_eq_zero] at h
  omega
theorem allFalse_of_not_models {a : Nat → Bool} {c : Nat} (h : ¬ ModelsMask a c) :
    AllFalseMask a c := by
  intro l hl ha
  exact h ⟨l,hl,ha⟩
theorem allFalse_union_single {a : Nat → Bool} {xs u : Nat}
    (hx : AllFalseMask a xs) (hu : ¬ Lit a u) : AllFalseMask a (xs ||| (1 <<< u)) := by
  intro l hl
  rw [Nat.testBit_or,Bool.or_eq_true] at hl
  rcases hl with hl | hl
  · exact hx l hl
  · have he := singleton_bit hl
    exact he ▸ hu
theorem unit_sound {a : Nat → Bool} {c xs u : Nat}
    (hm : ModelsMask a c) (hx : AllFalseMask a xs)
    (hs : subsetMask c (xs ||| (1 <<< u)) = true) : Lit a u := by
  rcases hm with ⟨l,hl,ha⟩
  have ht := subsetMask_sound hs l hl
  rw [Nat.testBit_or,Bool.or_eq_true] at ht
  rcases ht with ht | ht
  · exact False.elim (hx l ht ha)
  · exact singleton_bit ht ▸ ha
theorem checkFormula_sound {getClause : Nat → Nat} {a : Nat → Bool} :
    ∀ {cs : List (List Nat)} {idx : Nat}, checkFormula getClause cs idx = true →
      (∀ c ∈ cs, Models a c) → ∀ k, idx ≤ k → k < idx + cs.length → ModelsMask a (getClause k)
  | [], idx, _, _, k, hle, hlt => by simp at hlt; omega
  | c::cs, idx, hc, hm, k, hle, hlt => by
    rw [checkFormula_cons,strictNat_eq,strictNat_eq] at hc
    change (c.all (fun l => (getClause idx).testBit l) && checkFormula getClause cs (idx+1)) = true at hc
    rcases Bool.and_eq_true_iff.mp hc with ⟨heq,hrest⟩
    rcases Nat.eq_or_lt_of_le hle with rfl | hgt
    · rcases hm c List.mem_cons_self with ⟨l,hl,ha⟩
      exact ⟨l,List.all_eq_true.mp heq l hl,ha⟩
    · apply checkFormula_sound hrest (fun d hd => hm d (List.mem_cons_of_mem c hd)) k hgt
      simp only [List.length_cons] at hlt
      omega
theorem initial_known {getClause : Nat → Nat} {formula : List (List Nat)}
    (hc : checkFormula getClause formula 0 = true)
    {a : Nat → Bool} (hm : ∀ c∈formula, Models a c) : Known getClause a formula.length := by
  intro k hk
  exact checkFormula_sound hc hm k (Nat.zero_le k) (by omega)
theorem unsat_of_known_nil {getClause : Nat → Nat} {lastIdx : Nat}
    (hnil : Nat.beq (getClause lastIdx) 0 = true)
    {a : Nat → Bool} (hk : Known getClause a (lastIdx+1)) : False := by
  rcases hk lastIdx (Nat.lt_succ_self _) with ⟨l,hl,_⟩
  rw [Nat.eq_of_beq_eq_true hnil,Nat.zero_testBit] at hl
  exact Bool.noConfusion hl
noncomputable def propagatePackedN (getClause : Nat → Nat) (conflict bound n data xs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ xs => Nat.blt conflict bound && subsetMask (getClause conflict) xs)
    (fun _ recurse data xs =>
      strictNat data fun data => strictNat xs fun xs =>
      let h := Nat.land data 0x3fff
      let u := Nat.land (Nat.shiftRight data 14) 0x7ff
      bif Nat.blt h bound && subsetMask (getClause h) (Nat.lor xs (Nat.shiftLeft 1 u)) then
        recurse (Nat.shiftRight data 25) (Nat.lor xs (Nat.shiftLeft 1 (flipLit u)))
      else false) n data xs

noncomputable def replayPackedN (getClause getStep : Nat → Nat) (n curIdx pos : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun _ _ => true)
    (fun _ recurse curIdx pos =>
      strictNat curIdx fun curIdx => strictNat pos fun pos => strictNat (getStep pos) fun data =>
      let conf := Nat.land data 0x3fff
      let count := Nat.land (Nat.shiftRight data 14) 0x3ff
      bif propagatePackedN getClause conf curIdx count (Nat.shiftRight data 24) (getClause curIdx) then
        recurse (Nat.add curIdx 1) (Nat.add pos 1)
      else false) n curIdx pos

theorem propagatePackedN_succ (getClause : Nat → Nat) (conflict bound n data xs : Nat) :
    propagatePackedN getClause conflict bound (n+1) data xs =
      strictNat data (fun data => strictNat xs (fun xs =>
      let h := Nat.land data 0x3fff
      let u := Nat.land (Nat.shiftRight data 14) 0x7ff

      bif Nat.blt h bound && subsetMask (getClause h) (Nat.lor xs (Nat.shiftLeft 1 u)) then
        propagatePackedN getClause conflict bound n (Nat.shiftRight data 25) (Nat.lor xs (Nat.shiftLeft 1 (flipLit u)))
      else false)) := rfl

theorem replayPackedN_succ (getClause getStep : Nat → Nat) (n curIdx pos : Nat) :
    replayPackedN getClause getStep (n+1) curIdx pos =
      strictNat curIdx (fun curIdx => strictNat pos (fun pos => strictNat (getStep pos) (fun data =>
      let conf := Nat.land data 0x3fff
      let count := Nat.land (Nat.shiftRight data 14) 0x3ff
      bif propagatePackedN getClause conf curIdx count (Nat.shiftRight data 24) (getClause curIdx) then
        replayPackedN getClause getStep n (Nat.add curIdx 1) (Nat.add pos 1)
      else false))) := rfl

theorem propagatePackedN_sound {getClause : Nat → Nat} {a : Nat → Bool}
    {conflict bound : Nat} (hk : Known getClause a bound) :
    ∀ n data xs, AllFalseMask a xs →
      propagatePackedN getClause conflict bound n data xs = true → False
  | 0, data, xs, hx, hp => by
    rcases Bool.and_eq_true_iff.mp hp with ⟨hb,hs⟩
    rcases hk conflict (Nat.le_of_ble_eq_true hb) with ⟨l,hl,ha⟩
    exact hx l (subsetMask_sound hs l hl) ha
  | n+1, data, xs, hx, hp => by
    rw [propagatePackedN_succ,strictNat_eq,strictNat_eq] at hp
    let h := data &&& 0x3fff
    let u := (data >>> 14) &&& 0x7ff
    change (bif Nat.blt h bound && subsetMask (getClause h) (xs ||| (1 <<< u)) then
      propagatePackedN getClause conflict bound n (data >>> 25) (xs ||| (1 <<< flipLit u)) else false) = true at hp
    cases hc : Nat.blt h bound && subsetMask (getClause h) (xs ||| (1 <<< u))
    · rw [hc] at hp
      exact Bool.noConfusion hp
    · rw [hc] at hp
      rcases Bool.and_eq_true_iff.mp hc with ⟨hb,hs⟩
      have hu := unit_sound (hk h (Nat.le_of_ble_eq_true hb)) hx hs
      exact propagatePackedN_sound hk n (data >>> 25) _ (allFalse_union_single hx (flipLit_sound hu)) hp

theorem packed_step_sound {getClause : Nat → Nat} {a : Nat → Bool} {idx conflict n data : Nat}
    (hk : Known getClause a idx)
    (hp : propagatePackedN getClause conflict idx n data (getClause idx) = true) :
    Known getClause a (idx+1) := by
  have hm : ModelsMask a (getClause idx) := by
    apply Classical.byContradiction
    intro hn
    exact propagatePackedN_sound hk n data _ (allFalse_of_not_models hn) hp
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact hk i hi
  · exact hm

theorem replayPackedN_sound {getClause getStep : Nat → Nat} {a : Nat → Bool} :
    ∀ n curIdx pos, Known getClause a curIdx →
      replayPackedN getClause getStep n curIdx pos = true → Known getClause a (curIdx+n)
  | 0, curIdx, pos, hk, _ => by simpa using hk
  | n+1, curIdx, pos, hk, hr => by
    rw [replayPackedN_succ,strictNat_eq,strictNat_eq,strictNat_eq] at hr
    let data := getStep pos
    let conf := data &&& 0x3fff
    let count := (data >>> 14) &&& 0x3ff
    change (bif propagatePackedN getClause conf curIdx count (data >>> 24) (getClause curIdx) then
      replayPackedN getClause getStep n (curIdx+1) (pos+1) else false) = true at hr
    cases hp : propagatePackedN getClause conf curIdx count (data >>> 24) (getClause curIdx)
    · rw [hp] at hr
      exact Bool.noConfusion hr
    · rw [hp] at hr
      have hh := replayPackedN_sound n (curIdx+1) (pos+1) (packed_step_sound hk hp) hr
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hh

-- ==================== STRIP TRANSDUCER & POTENTIAL ====================
def mkLit (v : Nat) (b : Bool) : Nat := 2 * v + b.toNat

@[simp] theorem lit_mk (a : Nat → Bool) (v : Nat) (b : Bool) :
    Lit a (mkLit v b) ↔ a v = b := by
  have hd : (2 * v + b.toNat) / 2 = v := by cases b <;> simp [Bool.toNat] <;> omega
  have hm : (2 * v + b.toNat) % 2 = b.toNat := by cases b <;> simp [Bool.toNat] <;> omega
  simp only [Lit, mkLit, hd, hm]
  cases b <;> rfl

def sixClauses (a b c d : Nat) : List (List Nat) :=
  [[mkLit b false, mkLit a true, mkLit d true],
   [mkLit b false, mkLit a false, mkLit d false],
   [mkLit c false, mkLit a true, mkLit d true],
   [mkLit c false, mkLit a false, mkLit d false],
   [mkLit b true, mkLit c true, mkLit a false, mkLit d true],
   [mkLit b true, mkLit c true, mkLit a true, mkLit d false]]

private theorem bool_six_clauses : ∀ (va vb vc : Bool),
    let vd := xor va (vb || vc)
    (vb = false ∨ va = true ∨ vd = true) ∧
    (vb = false ∨ va = false ∨ vd = false) ∧
    (vc = false ∨ va = true ∨ vd = true) ∧
    (vc = false ∨ va = false ∨ vd = false) ∧
    (vb = true ∨ vc = true ∨ va = false ∨ vd = true) ∧
    (vb = true ∨ vc = true ∨ va = true ∨ vd = false) := by
  decide +kernel

theorem sixClauses_models (assign : Nat → Bool) (a b c d : Nat)
    (h : assign d = xor (assign a) (assign b || assign c)) :
    ∀ clause ∈ sixClauses a b c d, Models assign clause := by
  have h6 := bool_six_clauses (assign a) (assign b) (assign c)
  dsimp only at h6
  rw [← h] at h6
  rcases h6 with ⟨h1, h2, h3, h4, h5, h6⟩
  intro clause hc
  simp only [sixClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Models, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, lit_mk]
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

def vid (q t i : Nat) : Nat := q * t + i

def assignment (q : Nat) (x : Int → Bool) (origin : Int) (v : Nat) : Bool :=
  orbit x (v / q) (origin + (v % q : Nat))

theorem assignment_variable {q : Nat} (hq : 0 < q) (x : Int → Bool) (origin : Int)
    (t i : Nat) (hi : i < q) :
    assignment q x origin (vid q t i) = orbit x t (origin + i) := by
  simp [assignment, vid, Nat.mul_add_div hq, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]

def transitionFormula (p q : Nat) : List (List Nat) :=
  (List.range p).flatMap fun t => (List.range (q - 2)).flatMap fun i =>
    sixClauses (vid q t i) (vid q t (i + 1)) (vid q t (i + 2)) (vid q (t + 1) i)

def periodFormula (p q cols : Nat) : List (List Nat) :=
  (List.range cols).flatMap fun i =>
    [[mkLit (vid q p i) false, mkLit (vid q 0 i) true],
     [mkLit (vid q p i) true, mkLit (vid q 0 i) false]]

def forbid (q offset w s : Nat) : List Nat :=
  (List.range w).map fun j => mkLit (vid q 0 (offset + j)) (!s.testBit j)

def stripFormula (p q cols offset w : Nat) (states : List Nat) : List (List Nat) :=
  transitionFormula p q ++ periodFormula p q cols ++
    states.map (forbid q offset w)

theorem transition_models {p q : Nat} (hq : 0 < q) (x : Int → Bool) (origin : Int) :
    ∀ c ∈ transitionFormula p q, Models (assignment q x origin) c := by
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨t, _, hc⟩
  rcases List.mem_flatMap.mp hc with ⟨i, hi, hc⟩
  have hi0 : i < q := by have := List.mem_range.mp hi; omega
  have hi1 : i + 1 < q := by have := List.mem_range.mp hi; omega
  have hi2 : i + 2 < q := by have := List.mem_range.mp hi; omega
  apply sixClauses_models _ _ _ _ _ ?_ c hc
  rw [assignment_variable hq x origin (t + 1) i hi0,
    assignment_variable hq x origin t i hi0,
    assignment_variable hq x origin t (i + 1) hi1,
    assignment_variable hq x origin t (i + 2) hi2]
  simp [orbit, Phi, Int.natCast_add, Int.add_assoc]

theorem period_models {p q cols : Nat} (hq : 0 < q) (hcols : cols ≤ q)
    (x : Int → Bool) (hx : orbit x p = x) (origin : Int) :
    ∀ c ∈ periodFormula p q cols, Models (assignment q x origin) c := by
  intro c hc
  rcases List.mem_flatMap.mp hc with ⟨i, hi, hc⟩
  have hiq : i < q := by have := List.mem_range.mp hi; omega
  have heq : assignment q x origin (vid q p i) =
      assignment q x origin (vid q 0 i) := by
    rw [assignment_variable hq x origin p i hiq,
      assignment_variable hq x origin 0 i hiq, hx]
    rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
    simp only [Models, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, lit_mk]
  · cases hval : assignment q x origin (vid q 0 i) <;> simp [heq, hval]
  · cases hval : assignment q x origin (vid q 0 i) <;> simp [heq, hval]

def Matches (x : Int → Bool) (origin : Int) (w s : Nat) : Prop :=
  ∀ j < w, x (origin + j) = s.testBit j

theorem finite_strip_forces {p q cols offset w : Nat} {states : List Nat}
    (hq : 0 < q) (hcols : cols ≤ q) (hfit : offset + w ≤ q)
    (hu : ∀ assign : Nat → Bool, ¬ (∀ c ∈ stripFormula p q cols offset w states, Models assign c))
    (x : Int → Bool) (hx : orbit x p = x) (origin : Int) :
    ∃ s ∈ states, Matches x origin w s := by
  apply Classical.byContradiction
  intro hnot
  let start : Int := origin - offset
  let a := assignment q x start
  apply hu a
  intro c hc
  simp only [stripFormula, List.mem_append] at hc
  rcases hc with (ht | ht) | ht
  · exact transition_models hq x start c ht
  · exact period_models hq hcols x hx start c ht
  · rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
    have hd : ∃ j, j < w ∧ x (origin + j) ≠ s.testBit j := by
      apply Classical.byContradiction
      intro hn
      apply hnot
      refine ⟨s, hs, ?_⟩
      intro j hj
      apply Classical.byContradiction
      intro hh
      exact hn ⟨j, hj, hh⟩
    rcases hd with ⟨j, hj, hd⟩
    refine ⟨mkLit (vid q 0 (offset + j)) (!s.testBit j), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    · apply (lit_mk a _ _).mpr
      change assignment q x start (vid q 0 (offset + j)) = _
      rw [assignment_variable hq x start 0 (offset + j) (by omega)]
      simp only [orbit]
      have he : start + ((offset + j : Nat) : Int) = origin + j := by
        dsimp [start]
        omega
      rw [he]
      cases hv : x (origin + j) <;> cases hb : s.testBit j <;> simp_all

/-! ### Overlap graph and linear path-word bound -/

def edge (w v u : Nat) : Bool :=
  Nat.beq (v / 2) (u % (2 ^ (w - 1)))

theorem edge_of_matches {x : Int → Bool} {origin : Int} {w v u : Nat}
    (hw : 0 < w) (hv : v < 2 ^ w)
    (hmv : Matches x origin w v) (hmu : Matches x (origin + 1) w u) :
    edge w v u = true := by
  unfold edge
  rw [Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  have hdiv : (v / 2).testBit k = v.testBit (1 + k) := by
    change (v >>> 1).testBit k = v.testBit (1 + k)
    exact Nat.testBit_shiftRight v
  rw [hdiv, Nat.testBit_mod_two_pow]
  by_cases hk : k < w - 1
  · have hk1 : 1 + k < w := by omega
    rw [decide_eq_true hk, Bool.true_and]
    rw [← hmv (1 + k) hk1, ← hmu k (by omega)]
    congr 1
    omega
  · rw [decide_eq_false hk, Bool.false_and]
    apply Nat.testBit_lt_two_pow
    have hle : w ≤ 1 + k := by omega
    exact Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) hle)

def stateAt (states : List Nat) (j : Nat) : Nat := states.getD j 0
def baseAt (base : List Nat) (j : Nat) : Nat := base.getD j 0
def slopeAt (slope : List Nat) (j : Nat) : Nat := slope.getD j 0
def bitAt (states : List Nat) (j : Nat) : Bool := (stateAt states j).testBit 0

def children (w : Nat) (states : List Nat) (j : Nat) : List Nat :=
  (List.range states.length).filter (fun i => edge w (stateAt states j) (stateAt states i))

def wordsFrom (w : Nat) (states : List Nat) : Nat → Nat → List (List Bool)
  | 0, j => [[bitAt states j]]
  | m + 1, j =>
    ((children w states j).flatMap (wordsFrom w states m)).map (fun bs => bitAt states j :: bs)

def allWords (w : Nat) (states : List Nat) (m : Nat) : List (List Bool) :=
  (List.range states.length).flatMap (wordsFrom w states m)

def rowWord (x : Int → Bool) (origin : Int) : Nat → List Bool
  | 0 => [x origin]
  | m + 1 => x origin :: rowWord x (origin + 1) m

theorem mem_stateAt {states : List Nat} {s : Nat} (hs : s ∈ states) :
    ∃ j ∈ List.range states.length, stateAt states j = s := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  refine ⟨j, List.mem_range.mpr hj, ?_⟩
  simp [stateAt, List.getD_eq_getElem?_getD, hj]

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

def checkVertex (w : Nat) (states base slope : List Nat) (j : Nat) : Bool :=
  let s := stateAt states j
  let b := baseAt base j
  let sl := slopeAt slope j
  let ch := children w states j
  (decide (s < 2 ^ w) && decide (1 ≤ b)) &&
    (decide (sumList (ch.map (baseAt base)) ≤ b + sl) &&
     decide (sumList (ch.map (slopeAt slope)) ≤ sl))

def checkPotential (w : Nat) (states base slope : List Nat) (maxA maxB : Nat) : Bool :=
  decide (0 < w) &&
  ((List.range states.length).all (checkVertex w states base slope)) &&
  decide (sumList ((List.range states.length).map (baseAt base)) ≤ maxA) &&
  decide (sumList ((List.range states.length).map (slopeAt slope)) ≤ maxB)

theorem checkVertex_lt_pow {w : Nat} {states base slope : List Nat} {j : Nat}
    (h : checkVertex w states base slope j = true) :
    stateAt states j < 2 ^ w := by
  unfold checkVertex at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h1, _⟩
  rcases Bool.and_eq_true_iff.mp h1 with ⟨hs, _⟩
  exact of_decide_eq_true hs

theorem checkVertex_one_le_base {w : Nat} {states base slope : List Nat} {j : Nat}
    (h : checkVertex w states base slope j = true) :
    1 ≤ baseAt base j := by
  unfold checkVertex at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h1, _⟩
  rcases Bool.and_eq_true_iff.mp h1 with ⟨_, hb⟩
  exact of_decide_eq_true hb

theorem checkVertex_sum_base {w : Nat} {states base slope : List Nat} {j : Nat}
    (h : checkVertex w states base slope j = true) :
    sumList ((children w states j).map (baseAt base)) ≤ baseAt base j + slopeAt slope j := by
  unfold checkVertex at h
  rcases Bool.and_eq_true_iff.mp h with ⟨_, h2⟩
  rcases Bool.and_eq_true_iff.mp h2 with ⟨hb, _⟩
  exact of_decide_eq_true hb

theorem checkVertex_sum_slope {w : Nat} {states base slope : List Nat} {j : Nat}
    (h : checkVertex w states base slope j = true) :
    sumList ((children w states j).map (slopeAt slope)) ≤ slopeAt slope j := by
  unfold checkVertex at h
  rcases Bool.and_eq_true_iff.mp h with ⟨_, h2⟩
  rcases Bool.and_eq_true_iff.mp h2 with ⟨_, hsl⟩
  exact of_decide_eq_true hsl

theorem rowWord_mem_wordsFrom {w : Nat} {states base slope : List Nat}
    (hw : 0 < w)
    (hall : ∀ j ∈ List.range states.length, checkVertex w states base slope j = true)
    {x : Int → Bool}
    (hforce : ∀ origin : Int, ∃ s ∈ states, Matches x origin w s) :
    ∀ (m : Nat) (origin : Int) {j : Nat},
      j ∈ List.range states.length →
      Matches x origin w (stateAt states j) →
      rowWord x origin m ∈ wordsFrom w states m j
  | 0, origin, j, _, hmj => by
    have h0 : x origin = bitAt states j := by
      have := hmj 0 hw
      simpa [bitAt] using this
    simp [rowWord, wordsFrom, h0]
  | m + 1, origin, j, hj, hmj => by
    obtain ⟨s', hs', hms'⟩ := hforce (origin + 1)
    obtain ⟨i, hi, rfl⟩ := mem_stateAt hs'
    have hlt : stateAt states j < 2 ^ w := checkVertex_lt_pow (hall j hj)
    have hedge : edge w (stateAt states j) (stateAt states i) = true :=
      edge_of_matches hw hlt hmj hms'
    have hich : i ∈ children w states j :=
      List.mem_filter.mpr ⟨hi, hedge⟩
    have hih : rowWord x (origin + 1) m ∈ wordsFrom w states m i :=
      rowWord_mem_wordsFrom hw hall hforce m (origin + 1) hi hms'
    have h0 : x origin = bitAt states j := by
      have := hmj 0 hw
      simpa [bitAt] using this
    simp only [rowWord, wordsFrom, h0]
    exact List.mem_map.mpr ⟨rowWord x (origin + 1) m, List.mem_flatMap.mpr ⟨i, hich, hih⟩, rfl⟩

theorem rowWord_mem_allWords {w : Nat} {states base slope : List Nat} {maxA maxB : Nat}
    (hp : checkPotential w states base slope maxA maxB = true)
    {x : Int → Bool}
    (hforce : ∀ origin : Int, ∃ s ∈ states, Matches x origin w s)
    (m : Nat) (origin : Int) :
    rowWord x origin m ∈ allWords w states m := by
  unfold checkPotential at hp
  rcases Bool.and_eq_true_iff.mp hp with ⟨h123, _⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, _⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hw_dec, hall_dec⟩
  have hw : 0 < w := of_decide_eq_true hw_dec
  have hall : ∀ j ∈ List.range states.length, checkVertex w states base slope j = true :=
    List.all_eq_true.mp hall_dec
  obtain ⟨s, hs, hms⟩ := hforce origin
  obtain ⟨j, hj, rfl⟩ := mem_stateAt hs
  exact List.mem_flatMap.mpr ⟨j, hj, rowWord_mem_wordsFrom hw hall hforce m origin hj hms⟩

theorem length_flatMap_eq_sumList {α β : Type} (f : α → List β) :
    ∀ (xs : List α), (xs.flatMap f).length = sumList (xs.map (fun x => (f x).length))
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, List.length_append, List.map_cons, sumList]
    rw [length_flatMap_eq_sumList f xs]

theorem sumList_linear_le {α : Type} (g1 g2 g3 : α → Nat) (m : Nat) :
    ∀ {xs : List α},
      (∀ x ∈ xs, g1 x ≤ g2 x + m * g3 x) →
      sumList (xs.map g1) ≤ sumList (xs.map g2) + m * sumList (xs.map g3)
  | [], _ => by simp [sumList]
  | x :: xs, h => by
    simp only [List.map_cons, sumList]
    have hx := h x List.mem_cons_self
    have hxs := sumList_linear_le g1 g2 g3 m (fun y hy => h y (List.mem_cons_of_mem x hy))
    rw [Nat.mul_add]
    omega

theorem wordsFrom_length_le {w : Nat} {states base slope : List Nat}
    (hall : ∀ j ∈ List.range states.length, checkVertex w states base slope j = true) :
    ∀ (m : Nat) {j : Nat},
      j ∈ List.range states.length →
      (wordsFrom w states m j).length ≤ baseAt base j + m * slopeAt slope j
  | 0, j, hj => by
    have hb := checkVertex_one_le_base (hall j hj)
    simp only [wordsFrom, List.length_singleton]
    omega
  | m + 1, j, hj => by
    simp only [wordsFrom, List.length_map]
    rw [length_flatMap_eq_sumList]
    have hch : ∀ i ∈ children w states j,
        (wordsFrom w states m i).length ≤ baseAt base i + m * slopeAt slope i := by
      intro i hi
      exact wordsFrom_length_le hall m (List.mem_filter.mp hi).1
    have hsum := sumList_linear_le
      (fun i => (wordsFrom w states m i).length) (baseAt base) (slopeAt slope) m hch
    have hb := checkVertex_sum_base (hall j hj)
    have hsl := checkVertex_sum_slope (hall j hj)
    have hmul : m * sumList ((children w states j).map (slopeAt slope)) ≤ m * slopeAt slope j :=
      Nat.mul_le_mul_left m hsl
    have hsucc : (m + 1) * slopeAt slope j = slopeAt slope j + m * slopeAt slope j := by
      rw [Nat.add_comm m 1, Nat.add_mul, Nat.one_mul]
    omega

theorem allWords_length_le {w : Nat} {states base slope : List Nat} {maxA maxB : Nat}
    (hp : checkPotential w states base slope maxA maxB = true) (m : Nat) :
    (allWords w states m).length ≤ maxA + m * maxB := by
  unfold checkPotential at hp
  rcases Bool.and_eq_true_iff.mp hp with ⟨h123, hB_dec⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, hA_dec⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨_, hall_dec⟩
  have hall : ∀ j ∈ List.range states.length, checkVertex w states base slope j = true :=
    List.all_eq_true.mp hall_dec
  have hA : sumList ((List.range states.length).map (baseAt base)) ≤ maxA :=
    of_decide_eq_true hA_dec
  have hB : sumList ((List.range states.length).map (slopeAt slope)) ≤ maxB :=
    of_decide_eq_true hB_dec
  unfold allWords
  rw [length_flatMap_eq_sumList]
  have hsum := sumList_linear_le
    (fun j => (wordsFrom w states m j).length) (baseAt base) (slopeAt slope) m
    (fun j hj => wordsFrom_length_le hall m hj)
  have hmul : m * sumList ((List.range states.length).map (slopeAt slope)) ≤ m * maxB :=
    Nat.mul_le_mul_left m hB
  omega

theorem getD_rowWord (x : Int → Bool) :
    ∀ (m : Nat) (origin : Int) (k : Nat),
      k < m + 1 → (rowWord x origin m).getD k false = x (origin + k)
  | 0, origin, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    simp [rowWord]
  | m + 1, origin, 0, _ => by
    simp [rowWord]
  | m + 1, origin, k + 1, hk => by
    simp only [rowWord, List.getD_cons_succ]
    rw [getD_rowWord x m (origin + 1) k (by omega)]
    congr 1
    omega

theorem linear_words_of_strip {p w : Nat} {states base slope : List Nat} {maxA maxB : Nat}
    (hp : checkPotential w states base slope maxA maxB = true)
    (hforce : ∀ (x : Int → Bool), orbit x p = x → ∀ origin : Int, ∃ s ∈ states, Matches x origin w s)
    (m : Nat) :
    ∃ L : List (List Bool),
      L.length ≤ maxA + m * maxB ∧
      ∀ (x : Int → Bool), orbit x p = x → ∀ origin : Int, rowWord x origin m ∈ L :=
  ⟨allWords w states m, allWords_length_le hp m,
   fun x hx origin => rowWord_mem_allWords hp (hforce x hx) m origin⟩


end Ruliology.CellularAutomata.Rule30MovingStrip
