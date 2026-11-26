module

public import Ruliology.CellularAutomata.Rule30RunTransitions
public import Ruliology.CellularAutomata.Rule30FiniteStrips

/-!
# Rule 30 run-transition windows at every site

Kurtuluş's original strip windows and black-run parity argument extend to full rows.
The sharp two-run table and these windows can be combined independently at every
white phase of an eventual period in a row with a leftmost black cell.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30RunTransitionWindows
open Rule30Jen Rule30Realization Rule30StripCertificates Rule30FiniteStrips
open Rule30RunTransitions

/-- A black run, one white tick, and a second black run. -/
def piece (a r : Nat) := ones a ++ [false] ++ ones r
def Driven (x : Int → Bool) (j : Int) (s : Nat) (w : List Bool) :=
  ∀i, i < w.length → evol x (s+i) j = w.getD i false
def Force (w : List Bool) (b : Bool) :=
  ∀x j s, Driven x j s w → evol x (s+w.length) (j+1) = b

theorem suffix_drive {x j s u v} (h : Driven x j s (u++v)) : Driven x j (s+u.length) v := by
  intro i hi
  simpa [List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.add_assoc] using h (u.length+i) (by simp;omega)

theorem prefix_irrelevant {w b} (force : Force w b) (u : List Bool) : Force (u++w) b := by
  intro x j s h
  simpa only [List.length_append,Nat.add_assoc] using force x j _ (suffix_drive h)

private theorem from_strip {w b W} (width : 0<W) (h : colConst W (applyWord W w (fullSet W)) b = true) : Force w b := by
  intro x j s drive
  have enc := enc_encRow (x:=x) W s j
  have full : (fullSet W).testBit (encRow x s j W) = true := by
    unfold fullSet;rw [Nat.testBit_two_pow_sub_one];exact decide_eq_true enc.1
  obtain ⟨r,e,mem⟩ := enc_applyWord w s _ _ enc full drive
  have bound := allBelow_spec (p:=fun k => !(applyWord W w (fullSet W)).testBit k || k.testBit 0 == b) h r e.1
  have c : r.testBit 0 = b := by simpa [mem] using bound
  have e0 := e.2 0 width
  simpa only [Int.natCast_zero,Int.add_zero] using e0.symm.trans c

/-- Least preceding run needed to fix the next right reading. -/
def age : Nat → Nat
  | 1 | 2 | 3 | 5 => 8
  | 4 => 15
  | 6 => 16
  | 7 => 4
  | 8 => 14
  | _ => 0

/-- Right reading after a forcing pair. -/
def tone (r : Nat) := decide (r=2 ∨ r=4 ∨ r=6)

private theorem short_table : ∀i : Fin 8,
    colConst 7 (applyWord 7 (piece (age (i.val+1)) (i.val+1)) (fullSet 7)) (tone (i.val+1)) = true := by
  decide +kernel
private theorem long_table : colConst 5 (applyWord 5 (ones 9) (fullSet 5)) false = true := by decide +kernel

private theorem short_run (a r : Nat) (pos : 1≤r) (short : r≤8) (le : age r ≤ a) :
    Force (piece a r) (tone r) := by
  let i : Fin 8 := ⟨r-1,by omega⟩
  have row := short_table i
  have eq : i.val+1=r := by dsimp [i]; omega
  rw [eq] at row
  have split : ones a = ones (a-age r) ++ ones (age r) := by
    simp only [ones]
    rw [List.replicate_append_replicate,show a-age r+age r=a by omega]
  unfold piece;rw [split,List.append_assoc,List.append_assoc]
  simpa only [piece,List.append_assoc] using prefix_irrelevant (from_strip (by decide) row) (ones (a-age r))

private theorem long_run (a r : Nat) (long : 9≤r) : Force (piece a r) false := by
  have split : ones r = ones (r-9) ++ ones 9 := by
    simp only [ones]
    rw [List.replicate_append_replicate,show r-9+9=r by omega]
  unfold piece;rw [split,←List.append_assoc]
  exact prefix_irrelevant (from_strip (by decide) long_table) _

theorem pair_forces (a r : Nat) (pos : 1≤r) (le : age r≤a) : Force (piece a r) (tone r) := by
  by_cases small : r≤8
  · exact short_run a r pos small le
  · have zero : tone r = false := by simp [tone];omega
    rw [zero];exact long_run a r (by omega)

def run (W:Nat) (c boundary:Nat→Bool) (v:Nat) : Nat→Nat
  |0=>v
  |t+1=>stripStep W (c t) (boundary t) (run W c boundary v t)
private theorem run_lt (W:Nat) (c boundary:Nat→Bool) (v:Nat) (hv:v<2^W) (t:Nat) : run W c boundary v t<2^W := by
  cases t with |zero=>exact hv |succ t=>exact stripStep_lt _ _ _ _

/-- A physical row and a wide strip seeded identically agree in the entire one-sided cone.
The far boundary of the strip is arbitrary at every tick. -/
private theorem cone (W:Nat) (c boundary:Nat→Bool) (v:Nat) (x:Int→Bool) (hv:v<2^W)
    (initial:∀i:Nat,i<W→v.testBit i=x ((i:Int)+1)) (drive:∀t,evol x t 0=c t) :
    ∀t i:Nat,t+i<W→(run W c boundary v t).testBit i=evol x t ((i:Int)+1)
  |0,i,hi=>initial i (by omega)
  |t+1,i,hi=>by
    rw [run,testBit_stripStep W _ _ _ (run_lt _ _ _ _ hv _) i (by omega),ite_eq_right (show ¬ i+1=W by omega)]
    change rule _ _ _=rule (evol x t (((i:Int)+1)-1)) (evol x t ((i:Int)+1)) (evol x t (((i:Int)+1)+1))
    rw [cone W c boundary v x hv initial drive t i (by omega),cone W c boundary v x hv initial drive t (i+1) (by omega)]
    by_cases h:i=0
    · subst i;rw [ite_eq_left rfl,←drive];rfl
    · rw [ite_eq_right h,cone W c boundary v x hv initial drive t (i-1) (by omega)]
      congr 2 <;> omega

private def cutoffWord (i : Fin 8) := piece (age (i.val+1)-1) (i.val+1)
private def seedPair (i : Fin 8) : Nat × Nat :=
  [(681,627),(499,59),(1925,2995),(670067,216443),(5689,4467),(6183621,469425),(1766,659),(4505173,2721349)].getD i.val (0,0)
private def seed (i : Fin 8) (b : Bool) := if b then (seedPair i).2 else (seedPair i).1
private theorem controls : ∀i : Fin 8, ∀b : Bool,
    seed i b < 2^(1+(cutoffWord i).length) ∧
    (run (1+(cutoffWord i).length) (fun t => (cutoffWord i).getD t false)
      (fun _ => false) (seed i b) (cutoffWord i).length).testBit 0 = b := by decide +kernel

private theorem both_before (i : Fin 8) (b : Bool) : ∃x,Driven x 0 0 (cutoffWord i) ∧
    evol x (cutoffWord i).length 1 = b := by
  let w := cutoffWord i
  let c := fun t => w.getD t false
  let R : Int → Bool := fun j => (seed i b).testBit (j-1).toNat
  let x := conf R c
  have spec := realize R c
  have init (k : Nat) (_ : k < 1+w.length) : (seed i b).testBit k = x ((k:Int)+1) := by
    rw [show x ((k:Int)+1) = R ((k:Int)+1) from spec.1 _ (by omega)]
    simp [R]
  have facts := controls i b
  have terminal := cone (1+w.length) c (fun _ => false) (seed i b) x facts.1 init spec.2
    w.length 0 (by omega)
  refine ⟨x,?_,?_⟩
  · intro t _; simpa [c,w,x] using spec.2 t
  · simpa using terminal.symm.trans facts.2
private theorem age_of_large {r} (le : 9≤r) : age r=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le le
  rw [Nat.add_comm]; rfl

theorem exact_pair (a r : Nat) (pos : 1≤r) : (∃b,Force (piece a r) b) ↔ age r≤a := by
  constructor
  · rintro ⟨b,f⟩
    apply Classical.byContradiction;intro no
    have small : r≤8 := by
      by_cases h:9≤r
      · rw [age_of_large h] at no;omega
      · omega
    let i : Fin 8 := ⟨r-1,by omega⟩
    have eq : i.val+1=r := by dsimp [i];omega
    obtain ⟨x,drive,opposite⟩ := both_before i (!b)
    have same : cutoffWord i = ones (age r-1-a) ++ piece a r := by
      have split : ones (age r-1) = ones (age r-1-a) ++ ones a := by
        simp only [ones]
        rw [List.replicate_append_replicate,show age r-1-a+a=age r-1 by omega]
      simp only [cutoffWord,eq,piece,split,List.append_assoc]
    have bound := prefix_irrelevant f (ones (age r-1-a))
    rw [←same] at bound
    have yes := bound x 0 0 drive
    simp only [Nat.zero_add,Int.zero_add] at yes
    rw [yes] at opposite
    cases b <;> contradiction
  · intro yes;exact ⟨tone r,pair_forces a r pos yes⟩

section
variable {x : Int → Bool} {j : Int}

private theorem tick (t : Nat) (i : Int) :
    evol x (t+1) i = rule (evol x t (i-1)) (evol x t i) (evol x t (i+1)) := rfl

/-- A black center turns `a(1) ∨ a(2)` into a white `a(1)`. -/
private theorem pp_or (t : Nat) (hc : evol x t j = true) (h : (evol x t (j + 1) || evol x t (j + 2)) = true) :
    evol x (t + 1) (j + 1) = false := by
  rw [tick, show j + 1 - 1 = j by omega, show j + 1 + 1 = j + 2 by omega, hc]
  unfold rule
  rw [h]
  rfl

/-- A black center turns a white `a(1)` into `a(1) ∨ a(2)`. -/
private theorem pp_zero (t : Nat) (hc : evol x t j = true) (h : evol x t (j + 1) = false) :
    (evol x (t + 1) (j + 1) || evol x (t + 1) (j + 2)) = true := by
  rw [tick, tick, show j + 1 - 1 = j by omega, show j + 1 + 1 = j + 2 by omega,
    show j + 2 - 1 = j + 1 by omega, show j + 2 + 1 = j + 3 by omega, hc, h]
  unfold rule
  cases evol x t (j + 2) <;> cases evol x t (j + 3) <;> rfl

/-- After `a(1) ∨ a(2)`, an odd black run forces `a(1)` white. -/
private theorem pp_odd : ∀ (n s : Nat), (∀ k, k < 2 * n + 1 → evol x (s + k) j = true) →
    (evol x s (j + 1) || evol x s (j + 2)) = true → evol x (s + (2 * n + 1)) (j + 1) = false
  | 0, s, hb, h => by simpa using pp_or s (by simpa using hb 0 (by omega)) h
  | n + 1, s, hb, h => by
    have h1 : evol x (s + 1) (j + 1) = false := pp_or s (by simpa using hb 0 (by omega)) h
    have h2 : (evol x (s + 1 + 1) (j + 1) || evol x (s + 1 + 1) (j + 2)) = true :=
      pp_zero (s + 1) (by simpa using hb 1 (by omega)) h1
    have := pp_odd n (s + 1 + 1) (fun k hk => by
      have e := hb (k + 2) (by omega)
      rwa [show s + (k + 2) = s + 1 + 1 + k by omega] at e) h2
    rwa [show s + 1 + 1 + (2 * n + 1) = s + (2 * (n + 1) + 1) by omega] at this

/-- After a white `a(1)`, an even black run forces `a(1)` white. -/
private theorem pp_even : ∀ (n s : Nat), (∀ k, k < 2 * n → evol x (s + k) j = true) →
    evol x s (j + 1) = false → evol x (s + 2 * n) (j + 1) = false
  | 0, s, _, h => by simpa using h
  | n + 1, s, hb, h => by
    have h1 : (evol x (s + 1) (j + 1) || evol x (s + 1) (j + 2)) = true :=
      pp_zero s (by simpa using hb 0 (by omega)) h
    have h2 : evol x (s + 1 + 1) (j + 1) = false := pp_or (s + 1) (by simpa using hb 1 (by omega)) h1
    have := pp_even n (s + 1 + 1) (fun k hk => by
      have e := hb (k + 2) (by omega)
      rwa [show s + (k + 2) = s + 1 + 1 + k by omega] at e) h2
    rwa [show s + 1 + 1 + 2 * n = s + 2 * (n + 1) by omega] at this
end

private theorem prefix_drive {x j s u v} (h : Driven x j s (u++v)) : Driven x j s u := by
  intro k hk
  simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left,hk] using h k (by simp; omega)

private theorem force_old_white {u : List Bool}
    (h : allIn 5 (applyWord 5 u (fullSet 5)) col1White = true) : Force u false :=
  from_strip (W := 5) (by decide) (by simpa [allIn,col1White,colConst] using h)

private theorem force_old_black {u : List Bool}
    (h : allIn 5 (applyWord 5 u (fullSet 5)) col1Black = true) : Force u true :=
  from_strip (W := 5) (by decide) (by simpa [allIn,col1Black,colConst] using h)

private theorem force_old_or {u : List Bool}
    (h : allIn 5 (applyWord 5 u (fullSet 5)) col12Or = true)
    {x j s} (hu : Driven x j s u) :
    (evol x (s+u.length) (j+1) || evol x (s+u.length) (j+2)) = true := by
  have he := enc_encRow (x := x) 5 s j
  obtain ⟨r,hr,hm⟩ := Rule30FiniteStrips.enc_applyWord u s _ _ he (fullSet_testBit 5 _ he.1) hu
  have hor := allBelow_spec h r hr.1
  simp only [hm,Bool.not_true,Bool.false_or,col12Or] at hor
  have h0 : r.testBit 0 = evol x (s+u.length) (j+1) := by simpa using hr.2 0 (by decide)
  have h1 : r.testBit 1 = evol x (s+u.length) (j+2) := by simpa [Int.add_assoc] using hr.2 1 (by decide)
  rwa [h0,h1] at hor

private theorem drive_ones {x j s n} (h : Driven x j s (ones n)) :
    ∀ k, k < n → evol x (s+k) j = true := by
  intro k hk
  have h' : k < (ones n).length := by simpa [length_ones] using hk
  exact (h k h').trans (getD_ones hk)

private theorem or_then_odd {u : List Bool}
    (h : allIn 5 (applyWord 5 u (fullSet 5)) col12Or = true) (n : Nat) :
    Force (u ++ ones (2*n+1)) false := by
  intro x j s hu
  have hf := pp_odd n (s+u.length) (drive_ones (suffix_drive hu))
      (force_old_or h (prefix_drive hu))
  simpa [Nat.add_assoc,length_ones] using hf

private theorem black_then_odd {u : List Bool}
    (h : allIn 5 (applyWord 5 u (fullSet 5)) col1Black = true) (n : Nat) :
    Force (u ++ ones (2*n+1)) false := by
  intro x j s hu
  have hor : (evol x (s+u.length) (j+1) || evol x (s+u.length) (j+2)) = true := by
    rw [force_old_black h x j s (prefix_drive hu)]
    rfl
  have hf := pp_odd n (s+u.length) (drive_ones (suffix_drive hu)) hor
  simpa [Nat.add_assoc,length_ones] using hf

private theorem white_then_even {u : List Bool}
    (h : allIn 5 (applyWord 5 u (fullSet 5)) col1White = true) (n : Nat) :
    Force (u ++ ones (2*n)) false := by
  intro x j s hu
  have hf := pp_even n (s+u.length) (drive_ones (suffix_drive hu))
      (force_old_white h x j s (prefix_drive hu))
  simpa [Nat.add_assoc,length_ones] using hf

/-- Every one of Kurtuluş's original window rules forces a reading in an arbitrary row. -/
theorem old_forcing_window {w : List Bool} {phase : Nat} (good : Good w phase) :
    ∃ v b, EndsWith w phase v ∧ v.length ≤ 3*w.length+16 ∧ Force v b := by
  rcases good with h | h | h | ⟨n,hn,h | h | h | h⟩ | ⟨n,hn,h⟩
  · exact ⟨_,false,h,by simp [w9,length_ones] <;> omega,force_old_white chk_w9⟩
  · exact ⟨_,false,h,by simp [w7,length_ones] <;> omega,force_old_white chk_w7⟩
  · exact ⟨_,true,h,by simp [w2,length_ones] <;> omega,force_old_black chk_w2⟩
  · exact ⟨_,false,h,by simp [a8,length_ones] <;> omega,black_then_odd chk_a8 n⟩
  · exact ⟨_,false,h,by simp [b42,length_ones] <;> omega,or_then_odd chk_b42 n⟩
  · exact ⟨_,false,h,by simp [b46,length_ones] <;> omega,black_then_odd chk_b46 n⟩
  · exact ⟨_,false,h,by simp [b84,length_ones] <;> omega,black_then_odd chk_b84 n⟩
  · exact ⟨_,false,h,by simp [b81,length_ones] <;> omega,white_then_even chk_b81 n⟩

/-- A two-run window contributes exactly its required number of trailing bits in the preceding
run. Runs of nine or more are already covered by the kit's w9. -/
def PairGood (w : List Bool) (phase : Nat) : Prop :=
  ∃ r : Fin 8, EndsWith w phase (piece (age (r.val+1)) (r.val+1))

instance (w : List Bool) (phase : Nat) : Decidable (PairGood w phase) := by
  unfold PairGood
  infer_instance

/-- Each white phase may use the old rule or the sharp two-run rule. -/
def Combined (w : List Bool) : Prop :=
  ∀ j, j < w.length → w.getD j false = false → Good w j ∨ PairGood w j

instance (w : List Bool) : Decidable (Combined w) :=
  inferInstanceAs (Decidable (∀ j, j < w.length → _))

private theorem drive_of_endsWith {w : List Bool} (hP : 0 < w.length) {T : Nat}
    {x : Int → Bool} {i : Int}
    (hT : ∀ t, T ≤ t → evol x t i = w.getD ((t - T) % w.length) false)
    {j : Nat} {v : List Bool} (hv : EndsWith w j v) {t : Nat} (ht : T + v.length ≤ t)
    (hj : (t - T) % w.length = j) : Driven x i (t - v.length) v := by
  intro k hk
  rw [hT _ (by omega), ← hv k hk]
  unfold cyc
  congr 1
  have hA : v.length ≤ v.length * w.length := Nat.le_mul_of_pos_right _ hP
  obtain ⟨q, hq⟩ : ∃ q, t - T = q * w.length + j :=
    ⟨(t - T) / w.length, by rw [← hj, Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm⟩
  have key : (t - v.length + k - T) + v.length * w.length =
      (j + v.length * w.length - v.length + k) + q * w.length := by
    generalize v.length * w.length = A at hA ⊢
    generalize q * w.length = B at hq ⊢
    omega
  have := congrArg (· % w.length) key
  simpa [Nat.add_mul_mod_self_right] using this

/-- A bounded choice of forcing windows, one per white phase, excludes that eventual word at
every site of every row with a leftmost black cell. The choice of window may vary by phase. -/
theorem exclude_of_windows {w : List Bool} (hw : w ≠ []) {B : Nat}
    (coverage : ∀ j, j < w.length → w.getD j false = false →
      ∃ v b, EndsWith w j v ∧ v.length ≤ B ∧ Force v b)
    {x : Int → Bool} {lo : Int} (black : x lo = true) (left : ∀ k, k < lo → x k = false)
    (i : Int) : ¬ Rule30FiniteStrips.EventuallyWord x i w := by
  rintro ⟨T,hT⟩
  have hP := List.length_pos_iff.2 hw
  have phase (t : Nat) (ht : T ≤ t) : (t+w.length-T)%w.length = (t-T)%w.length := by
    rw [show t+w.length-T = t-T+w.length by omega,Nat.add_mod_right]
  have same (t : Nat) (ht : T ≤ t) : evol x (t+w.length) i = evol x t i := by
    rw [hT _ (by omega),hT _ ht,phase t ht]
  apply Rule30FiniteMaskedJen.masked_jen black left i (T := T+B) hP (fun t ht => same t (by omega))
  intro t ht white
  have hwhite := (hT t (by omega)).symm.trans white
  obtain ⟨v,b,hv,hl,hf⟩ := coverage _ (Nat.mod_lt _ hP) hwhite
  have at_time (u : Nat) (hu : T+B ≤ u) (hu_phase : (u-T)%w.length = (t-T)%w.length) :
      evol x u (i+1) = b := by
    have h := hf x i (u-v.length) (drive_of_endsWith hP hT hv (by omega) hu_phase)
    rwa [show u-v.length+v.length=u by omega] at h
  exact (at_time _ (by omega) (phase t (by omega))).trans (at_time t ht rfl).symm

/-- The whole hybrid family. It includes mixed white-phase rules, at all word lengths and sites. -/
theorem not_eventually_combined {w : List Bool} (hw : w ≠ []) (cover : Combined w)
    {x : Int → Bool} {lo : Int} (black : x lo = true) (left : ∀ k, k < lo → x k = false)
    (i : Int) : ¬ Rule30FiniteStrips.EventuallyWord x i w := by
  apply exclude_of_windows hw (B := 3*w.length+25) _ black left i
  intro j hj white
  rcases cover j hj white with old | ⟨r,hr⟩
  · obtain ⟨v,b,hv,hl,hf⟩ := old_forcing_window old
    exact ⟨v,b,hv,by omega,hf⟩
  · have bound : ∀ k : Fin 8, (piece (age (k.val+1)) (k.val+1)).length ≤ 25 := by decide +kernel
    have len := bound r
    exact ⟨_,_,hr,by omega,pair_forces _ _ (by omega) (Nat.le_refl _)⟩

/-- Before the cutoff, each colour is attainable from a nonzero finitely supported row at
the specified column. The added leftmost black is outside all the observation cones. -/
theorem both_colours_below (a r : Nat) (pos : 1 ≤ r) (early : a < age r) (j : Int) (b : Bool) :
    ∃ (x : Int → Bool) (lo : Int), x lo = true ∧ (∀ k, k < lo → x k = false) ∧
      Rule30PeriodTwoSideways.FinConfig x ∧
      ∃ s : Nat, Driven x j s (piece a r) ∧ evol x (s+(piece a r).length) (j+1) = b := by
  have small : r ≤ 8 := by
    by_cases he : 9 ≤ r
    · rw [age_of_large he] at early
      omega
    · omega
  let i : Fin 8 := ⟨r-1,by omega⟩
  have hr : i.val+1 = r := by dsimp [i]; omega
  obtain ⟨y,drive,read⟩ := both_before i b
  let W := (cutoffWord i).length
  let start := (ones (age r-1-a)).length
  have split : cutoffWord i = ones (age r-1-a) ++ piece a r := by
    have lengths : ones (age r-1) = ones (age r-1-a) ++ ones a := by
      simp only [ones]
      rw [List.replicate_append_replicate,show age r-1-a+a=age r-1 by omega]
    simp only [cutoffWord,hr,piece,lengths,List.append_assoc]
  have htime : W = start + (piece a r).length := by
    change (cutoffWord i).length = (ones (age r-1-a)).length + _
    rw [split,List.length_append]
  have subdrive : Driven y 0 start (piece a r) := by
    have h : Driven y 0 0 (ones (age r-1-a) ++ piece a r) := split ▸ drive
    simpa [start] using suffix_drive h
  let lo : Int := -(W : Int)-1
  let z : Int → Bool := fun k =>
    if -(W : Int) ≤ k ∧ k ≤ (W : Int)+1 then y k else decide (k = lo)
  have coneEq : ∀ t : Nat, ∀ k : Int, -(W : Int)+t ≤ k → k+t ≤ (W : Int)+1 →
      evol z t k = evol y t k :=
    Rule30ZeroBoundaryBarriers.evol_local (by intro k hk hl; simp [z,hk,hl])
  let x : Int → Bool := fun k => z (k + -j)
  have hshift : ∀ (t : Nat) (k : Int), evol x t (k+j) = evol z t k :=
    Rule30ZeroBoundaryBarriers.evol_shift_all (by
      intro k
      change z (k+j + -j) = z k
      rw [show k+j + -j = k by omega])
  have leftmost : z lo = true := by
    have outside : ¬ -(W : Int) ≤ lo := by dsimp [lo]; omega
    simp [z,outside]
  have left : ∀ k, k < lo → z k = false := by
    intro k hk
    have h0 : ¬ -(W : Int) ≤ k := by dsimp [lo] at hk; omega
    simp [z,h0,show k ≠ lo by omega]
  refine ⟨x,lo+j,?_,?_,?_,start,?_,?_⟩
  · simpa [evol] using (hshift 0 lo).trans leftmost
  · intro k hk
    exact (by
      change z (k + -j) = false
      exact left _ (by omega))
  · refine ⟨W+1+j.natAbs,fun k hk => ?_⟩
    change z (k + -j) = false
    have outside : ¬ (-(W : Int) ≤ k + -j ∧ k + -j ≤ (W : Int)+1) := by omega
    have other : k + -j ≠ lo := by dsimp [lo]; omega
    simp [z,outside,other]
  · intro k hk
    have he : start+k ≤ W := by omega
    rw [show j=0+j by omega,hshift,coneEq _ _ (by omega) (by omega)]
    exact subdrive k hk
  · rw [← htime,show j+1=1+j by omega,hshift,coneEq _ _ (by omega) (by omega)]
    exact read



/-- A cycle with an old-only four-run phase and a new-only four-run phase. -/
def mixedExample : List Bool := runsWord [16,4,9,1,4,9]

theorem mixedExample_combined : Combined mixedExample := by decide +kernel

theorem mixedExample_requires_both :
    ¬ AllGood mixedExample ∧ ¬ PairGood mixedExample 38 ∧ Good mixedExample 38 ∧
      ¬ Good mixedExample 21 ∧ PairGood mixedExample 21 := by decide +kernel

end Ruliology.CellularAutomata.Rule30RunTransitionWindows
