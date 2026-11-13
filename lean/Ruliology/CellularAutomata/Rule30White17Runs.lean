module
public import Ruliology.CellularAutomata.Rule30Certificates.White17
public import Ruliology.CellularAutomata.Rule30RankedWords
/-!
# Every white run at least 17

**Partial result on Problem 1.** For every nonempty list of blocks `(r, q)` with `r ≥ 1` and `q ≥ 17`,
chosen independently, the single-seed center column is not eventually the repeating word
`1^(r₁) 0^(q₁) … 1^(rₖ) 0^(qₖ)`, whatever the transient (`not_eventually_long_white_runs`). The number
of blocks and every run length are unbounded. Corollary: `1^r 0^q` for all `r ≥ 1`, `q ≥ 17`
(`not_eventually_black_white`).

**Method.** The fourteen cells right of the center, with an arbitrary cell beyond them, form the strip
relaxation of `Rule30StripCertificates`. Any two blocks capture every strip into a 683-strip envelope
split into nine rank regions (`Rule30White17Data`). No block raises the rank, so along successive
periods the rank is eventually constant (`Rule30RankedWords.no_word_ranked`). A block that keeps the
rank has a prescribed column-1 response along its white run, depending only on the rank and the black
length. Hence `orCol 0` is eventually periodic, which masked Jen
(`Rule30MaskedJen.orCol_not_eventuallyPeriodic`) forbids. The certificate was found by computer search
and every finite inclusion is decided by the kernel.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30White17Runs
open Rule30StripCertificates Rule30RunEnvelopes Rule30RankedWords Rule30White17Data
open Rule30Jen Rule30MaskedJen

def Good (a : Nat×Nat) : Prop := 1≤a.1 ∧ 17≤a.2
abbrev driver (a : Nat×Nat) : List Bool := word a.1 a.2
def blocks (as : List (Nat×Nat)) : List Bool := as.flatMap driver

theorem rank_block (t r q : Nat) (hr : 1≤r) (hq : 17≤q)
    (h : Reads t (word r q)) (hs : E.testBit (code 14 t)=true) :
    E.testBit (code 14 (t+(word r q).length))=true ∧
    rank (code 14 (t+(word r q).length))≤rank (code 14 t) ∧
    (rank (code 14 (t+(word r q).length))=rank (code 14 t) →
      rank (code 14 t)=0 ∨ (rank (code 14 t)=4 ∧ r=3) ∨ (rank (code 14 t)=8 ∧ r=3)) := by
  have hslt : code 14 t<2^14 := (enc_encRow 14 t 0).1
  obtain ⟨hbound,hregion⟩ := partition (code 14 t) hslt hs
  have hendlt : code 14 (t+(word r q).length)<2^14 := (enc_encRow 14 (t+(word r q).length) 0).1
  have cases : rank (code 14 t)=0 ∨ rank (code 14 t)=1 ∨ rank (code 14 t)=2 ∨
    rank (code 14 t)=3 ∨ rank (code 14 t)=4 ∨ rank (code 14 t)=5 ∨
    rank (code 14 t)=6 ∨ rank (code 14 t)=7 ∨ rank (code 14 t)=8 := by omega
  rcases cases with hj | hj | hj | hj | hj | hj | hj | hj | hj
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target0 _ hendlt (advance0 r q hr hq _ hm)
    exact ⟨hh.1,hh.2,fun _ => Or.inl rfl⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target1 _ hendlt (advance1 r q hr hq _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target2 _ hendlt (advance2 r q hr hq _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target3 _ hendlt (advance3 r q hr hq _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target4 _ hendlt (advance4 r q hr hq _ hm)
    refine ⟨hh.1,hh.2,fun he => ?_⟩
    have hr3 : r=3 := by
      by_cases hn : r=3
      · exact hn
      exfalso
      have cases : r=1 ∨ r=2 ∨ 4≤r := by omega
      rcases cases with h1 | h2 | h4
      · subst r
        have hx := exitTarget4_1 _ hendlt (exit4_1 q hq _ hm)
        omega
      · subst r
        have hx := exitTarget4_2 _ hendlt (exit4_2 q hq _ hm)
        omega
      · have hx := exitTarget4_4 _ hendlt (exit4_4 r q h4 hq _ hm)
        omega
    exact Or.inr (Or.inl ⟨rfl,hr3⟩)
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target5 _ hendlt (advance5 r q hr hq _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target6 _ hendlt (advance6 r q hr hq _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target7 _ hendlt (advance7 r q hr hq _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target8 _ hendlt (advance8 r q hr hq _ hm)
    refine ⟨hh.1,hh.2,fun he => ?_⟩
    have hr3 : r=3 := by
      by_cases hn : r=3
      · exact hn
      exfalso
      have cases : r=1 ∨ r=2 ∨ 4≤r := by omega
      rcases cases with h1 | h2 | h4
      · subst r
        have hx := exitTarget8_1 _ hendlt (exit8_1 q hq _ hm)
        omega
      · subst r
        have hx := exitTarget8_2 _ hendlt (exit8_2 q hq _ hm)
        omega
      · have hx := exitTarget8_4 _ hendlt (exit8_4 r q h4 hq _ hm)
        omega
    exact Or.inr (Or.inr ⟨rfl,hr3⟩)

def delayAt (j r : Nat) : Nat := if j=4 then 3 else if j=8 then 10 else delay r

def response (a : Nat×Nat) (j i : Nat) : Bool :=
  if i<a.1 then true else decide (delayAt j a.1≤i-a.1)

theorem reads_take {t : Nat} {w : List Bool} (h : Reads t w) (i : Nat) : Reads t (w.take i) := by
  intro k hk
  have hk' : k<w.length := by simp only [List.length_take] at hk;omega
  have hh := h k hk'
  simpa [List.getD_eq_getElem?_getD,List.getElem?_take,show k<i by simp only [List.length_take] at hk;omega] using hh

theorem driver_observation (t r q j : Nat) (h : Reads t (word r q))
    (hs : (region j).testBit (code 14 t)=true)
    (hp : ∀ i, Const 14 (applyWord 14 (List.replicate i false)
      (applyWord 14 (List.replicate r true) (region j))) (decide (delayAt j r≤i))) :
    ∀ i,i<(word r q).length → orCol 0 (t+i)=response (r,q) j i := by
  intro i hi
  have hc := h i hi
  rw [word_getD] at hc
  unfold orCol response
  simp only [Int.zero_add]
  rw [hc]
  by_cases hir : i<r
  · simp [hir]
  · have htake : (word r q).take i=List.replicate r true++List.replicate (i-r) false := by
      have hi' : i-r≤q := by simp only [word,List.length_append,List.length_replicate] at hi;omega
      simp [word,List.take_append,List.take_replicate,Nat.min_eq_right (by omega : r≤i),Nat.min_eq_left hi']
    have hm := code_word (reads_take h i) hs
    rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi),htake,apply_append] at hm
    have hh := hp (i-r) (code 14 (t+i)) (enc_encRow 14 (t+i) 0).1 hm
    have hb := (enc_encRow 14 (t+i) 0).2 0 (by decide)
    change (code 14 (t+i)).testBit 0=cell (t+i) 1 at hb
    simpa [hir,←hb] using hh

theorem ranked_driver (a : Nat×Nat) (ha : Good a) :
    Ranked 14 E rank (driver a) (response a) := by
  intro t ht hs
  obtain ⟨he,hle,hallow⟩ := rank_block t a.1 a.2 ha.1 ha.2 ht hs
  refine ⟨he,hle,fun heq => ?_⟩
  have hreg := (partition _ (enc_encRow 14 t 0).1 hs).2
  apply driver_observation t a.1 a.2 (rank (code 14 t)) ht hreg
  intro i
  rcases hallow heq with h0 | ⟨h4,hr⟩ | ⟨h8,hr⟩
  · simpa [h0,region,delayAt] using profile a.1 ha.1 i
  · simpa [h4,hr,region,delayAt] using exception4 i
  · simpa [h8,hr,region,delayAt] using exception8 i

def outputs : List (Nat×Nat)→Nat→Nat→Bool
  | [],_,_ => false
  | a::as,j,i => if i<(driver a).length then response a j i else outputs as j (i-(driver a).length)

theorem ranked_blocks (as : List (Nat×Nat)) (ha : ∀a∈as,Good a) :
    Ranked 14 E rank (blocks as) (outputs as) := by
  induction as with
  | nil => exact ranked_nil 14 E rank _
  | cons a as ih =>
    have h0 := ha a (by simp)
    have has : ∀b∈as,Good b := fun b hb => ha b (by simp [hb])
    exact ranked_append (ranked_driver a h0) (ih has)

theorem stableE (a : Nat×Nat) (ha : Good a) : Sub (applyWord 14 (driver a) E) E :=
  sub_trans (word_mono 14 subsetA1 _) (capture1 a.1 a.2 ha.1 ha.2)

theorem stableA1 (a : Nat×Nat) (ha : Good a) : Sub (applyWord 14 (driver a) A1) A1 :=
  sub_trans (capture1 a.1 a.2 ha.1 ha.2) subsetA1

theorem stable_blocks (B : Nat)
    (h : ∀a,Good a → Sub (applyWord 14 (driver a) B) B)
    (as : List (Nat×Nat)) (ha : ∀a∈as,Good a) : Sub (applyWord 14 (blocks as) B) B := by
  induction as with
  | nil => exact sub_refl B
  | cons a as ih =>
    change Sub (applyWord 14 (driver a++blocks as) B) B
    rw [apply_append]
    exact sub_trans (word_mono 14 (h a (ha a (by simp))) _)
      (ih (fun b hb => ha b (by simp [hb])))

theorem capture_blocks (A B : Nat)
    (h : ∀a,Good a → Sub (applyWord 14 (driver a) A) B)
    (stable : ∀a,Good a → Sub (applyWord 14 (driver a) B) B)
    (as : List (Nat×Nat)) (hne : as≠[]) (ha : ∀a∈as,Good a) :
    Sub (applyWord 14 (blocks as) A) B := by
  cases as with
  | nil => exact (hne rfl).elim
  | cons a as =>
    change Sub (applyWord 14 (driver a++blocks as) A) B
    rw [apply_append]
    exact sub_trans (word_mono 14 (h a (ha a (by simp))) _)
      (stable_blocks B stable as (fun b hb => ha b (by simp [hb])))

theorem blocks_warm (as : List (Nat×Nat)) (hne : as≠[]) (ha : ∀a∈as,Good a) :
    Sub (iterW 14 (blocks as) 2 (fullSet 14)) E := by
  have h0 := capture_blocks (fullSet 14) A1 (fun a h => capture0 a.1 a.2 h.1 h.2) stableA1 as hne ha
  have h1 := capture_blocks A1 E (fun a h => capture1 a.1 a.2 h.1 h.2) stableE as hne ha
  exact sub_trans (word_mono 14 h0 _) h1

/-- **W(17).** Every white run may independently have any length at least seventeen;
black lengths, block count and the transient are all unbounded. -/
theorem not_eventually_long_white_runs (as : List (Nat×Nat)) (hne : as≠[])
    (ha : ∀a∈as,1≤a.1 ∧ 17≤a.2) :
    ¬ EventuallyWord (as.flatMap (fun a => List.replicate a.1 true++List.replicate a.2 false)) := by
  change ¬ EventuallyWord (blocks as)
  have hw : 0<(blocks as).length := by
    cases as with
    | nil => exact (hne rfl).elim
    | cons a as =>
      have h := (ha a (by simp)).1
      change 0<(driver a++blocks as).length
      simp only [List.length_append,word,List.length_replicate]
      omega
  exact no_word_ranked 14 E 2 rank (blocks as) (outputs as) hw (blocks_warm as hne ha) (ranked_blocks as ha)

theorem not_eventually_black_white (r q : Nat) (hr : 1≤r) (hq : 17≤q) :
    ¬ EventuallyWord (List.replicate r true++List.replicate q false) := by
  simpa using not_eventually_long_white_runs [(r,q)] (by simp) (by simpa using And.intro hr hq)

/-! ## Multi-period envelope stability `Sub (iterW 14 (blocks as) m E) E` and two-block `1^r1 0^q1 1^r2 0^q2` exclusion -/

/-- **Multi-Period Envelope Stability and Two-Block `W(17)` Exclusion (`iterW_blocks_E_and_two_block_white17`).** -/
theorem iterW_blocks_E_and_two_block_white17
    (as : List (Nat × Nat)) (ha : ∀ a ∈ as, Good a) (m r1 q1 r2 q2 : Nat)
    (hr1 : 1 ≤ r1) (hq1 : 17 ≤ q1) (hr2 : 1 ≤ r2) (hq2 : 17 ≤ q2) :
    Sub (iterW 14 (blocks as) m E) E ∧
    ¬ EventuallyWord ((List.replicate r1 true ++ List.replicate q1 false) ++
                      (List.replicate r2 true ++ List.replicate q2 false)) := by
  have hmono : ∀ (k : Nat) {X Y : Nat}, Sub X Y →
      Sub (iterW 14 (blocks as) k X) (iterW 14 (blocks as) k Y) := by
    intro k
    induction k with
    | zero => intro X Y h; exact h
    | succ k ih => intro X Y h; exact ih (word_mono 14 h (blocks as))
  have hiter : ∀ k : Nat, Sub (iterW 14 (blocks as) k E) E := by
    intro k
    induction k with
    | zero => exact sub_refl E
    | succ k ih =>
      unfold iterW
      exact sub_trans (hmono k (stable_blocks E stableE as ha)) ih
  refine ⟨hiter m, ?_⟩
  have htwo := not_eventually_long_white_runs [(r1, q1), (r2, q2)] (by simp) (by
    intro a hmem
    rcases List.mem_cons.mp hmem with rfl | hmem2
    · exact ⟨hr1, hq1⟩
    · have ha2 : a = (r2, q2) := by simpa using hmem2
      subst ha2
      exact ⟨hr2, hq2⟩)
  simpa [List.flatMap] using htwo

end Ruliology.CellularAutomata.Rule30White17Runs
