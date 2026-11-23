module

public import Ruliology.CellularAutomata.Rule30Certificates.TrappedRunMasks
public import Ruliology.CellularAutomata.Rule30GateTrapLadder

/-! Two exclusions for runs of four 5-gaps in the trapped gate. On the kit's
ladder they hold from width 45 upward. A width-44 path attains the four-run word
at delay two. Two physical right halves witness the delay and run-count bounds. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30TrappedRuns
open Rule30GateTrap Rule30DrivenPrefix Rule30Ether Rule30StripCertificates
open Rule30PeriodTwoCoupled Rule30RunWindow

private def bits (a : Nat) : Nat → Bool
  | 0 => false
  | j+1 => a.testBit j

private theorem physical_gate (a s : Nat) :
    Rule30PeriodTwoSideways.u (bits a) s = (packed altCol a (2*s+1)).testBit 0 :=
  (packed_sound altCol (bits a) a (fun _ => rfl) _ 0).symm

private theorem physical_window (a t : Nat) : win (bits a) t =
    seg (fun i => (packed altCol a t).testBit i) 16 := by
  apply Rule30Ether.seg_congr
  intro i _
  simpa only [Nat.zero_add] using (packed_sound altCol (bits a) a (fun _ => rfl) t i).symm

private theorem witness {a code n s : Nat} (hc : code ∈ trapCodes)
    (hw : seg (fun i => (packed altCol a 1).testBit i) 16 = decode code)
    (hh : (List.range (closed n).length).all (fun i =>
      (packed altCol a (2*(s+i)+1)).testBit 0 == (closed n).getD i false) = true) :
    win (bits a) 1 ∈ trap ∧ ∀ i, i < (closed n).length →
      Rule30PeriodTwoSideways.u (bits a) (s+i) = (closed n).getD i false := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [physical_window, hw]
    exact List.mem_map.mpr ⟨_, hc, rfl⟩
  · rw [physical_gate]
    exact beq_iff_eq.mp (List.all_eq_true.mp hh i (List.mem_range.mpr hi))

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Four closed runs occur one sample after a trapped tick. -/
theorem four_one_sample :
    ∃ R, win R 1 ∈ trap ∧ ∀ i, i < (closed 4).length →
      Rule30PeriodTwoSideways.u R (1+i) = (closed 4).getD i false := by
  let a := 17911952117231624625415841284791634824617432618773606279499
  exact ⟨_, witness (a := a) (code := 44920) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)⟩

/-- Three closed runs occur sixty samples after a trapped tick. -/
theorem three_sixty_samples :
    ∃ R, win R 1 ∈ trap ∧ ∀ i, i < (closed 3).length →
      Rule30PeriodTwoSideways.u R (60+i) = (closed 3).getD i false := by
  let a := 88769951030016947892698456558596051073035529750717722303543758321481268415460012
  exact ⟨_, witness (a := a) (code := 40615) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)⟩

private theorem cone (R : Nat → Bool) (b x W : Nat)
    (start : ∀ j, j < W → x.testBit j = drv altCol R b (j+1)) :
    ∀ t j, j+t < W →
      (packed (fun k => altCol (b+k)) x t).testBit j = drv altCol R (b+t) (j+1) := by
  intro t
  induction t with
  | zero => exact start
  | succ t ih =>
    intro j hj
    rw [packed,step_bit,show b+(t+1) = b+t+1 by omega, drv_isR30 altCol R (b+t) j]
    unfold Rule30Jen.rule
    rw [ih j (by omega), ih (j+1) (by omega)]
    cases j with
    | zero => simp [drv_col0]
    | succ j => simp [ih j (by omega)]

private theorem packed_twice (b x : Nat) (hb : b%2=1) :
    ∀ i, iterate x i = packed (fun k => altCol (b+k)) x (2*i) := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    have ho : altCol (b+2*i) = false := by unfold altCol; simp; omega
    have he : altCol (b+(2*i+1)) = true := by unfold altCol; simp; omega
    rw [iterate,ih,show 2*(i+1)=2*i+1+1 by omega, packed,packed,ho,he,double]

private theorem shift_iterate (r : Nat) : ∀ i, iterate (double r) i = iterate r (i+1)
  | 0 => rfl
  | i+1 => congrArg double (shift_iterate r i)

private theorem from_frames (ds : List Window) (r : Nat)
    (h : ∀ i (hi : i < ds.length), Holds ds[i] (iterate r i)) : Trace r ds := by
  induction ds generalizing r with
  | nil => trivial
  | cons a ds ih =>
    refine ⟨h 0 (by simp), ih _ (fun i hi => ?_)⟩
    rw [shift_iterate]
    exact h (i+1) (by simpa using hi)

private theorem seg_at : ∀ (n : Nat) (f : Nat → Bool) (j : Nat), j<n → (seg f n).getD j false = f j
  | 0, _, _, h => absurd h (by omega)
  | _+1, _, 0, _ => rfl
  | n+1, f, j+1, h => seg_at n (fun i => f (i+1)) j (by omega)

private theorem trap_bounds : trapCodes.all (fun n => n < 2^16) = true := by decide +kernel

private theorem from_trap {R : Nat → Bool} {t q : Nat} (h : win R t ∈ trap)
    (hq : ∀ j, j<16 → q.testBit j = drv altCol R t (j+1)) : q % 2^16 ∈ trapCodes := by
  obtain ⟨c,hc,eq⟩ := List.mem_map.mp h
  have bound : c < 2^16 := of_decide_eq_true (List.all_eq_true.mp trap_bounds c hc)
  suffices q % 2^16 = c by rwa [this]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow]
  by_cases hj : j < 16
  · have e := congrArg (fun L : List Bool => L.getD j false) eq
    change (seg (fun i => c.testBit i) 16).getD j false =
      (seg (fun i => drv altCol R t (0+i+1)) 16).getD j false at e
    rw [seg_at _ _ _ hj,seg_at _ _ _ hj] at e
    simpa [hj, hq j hj] using e.symm
  · have bound' : c < 2^j := Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hj,Nat.testBit_lt_two_pow bound']

private theorem prefix_bit : ∀ (n : Nat) (f : Nat → Bool) (j : Nat), j < n →
    (encList (seg f n)).testBit j = f j
  | 0, _, _, h => absurd h (by omega)
  | _+1, f, 0, _ => by
    rw [Nat.testBit_zero]
    simp only [seg, encList]
    cases f 0 <;> simp <;> omega
  | n+1, f, j+1, h => by
    rw [Nat.testBit_succ]
    change (((if f 0 then 1 else 0) + 2 * encList (seg (fun i => f (i+1)) n)) / 2).testBit j = _
    have e (a : Nat) : ((if f 0 then 1 else 0) + 2*a) / 2 = a := by cases f 0 <;> simp <;> omega
    rw [e]
    exact prefix_bit n _ j (by omega)

/-- Every proposed physical occurrence supplies one finite packed trace. -/
theorem occurrence_trace (R : Nat → Bool) {t0 : Nat} (h0 : t0 % 2 = 1)
    (hw : win R t0 ∈ trap) (s : Nat) (hs : t0+4 ≤ 2*s+1)
    (word : ∀ i, i<96 → Rule30PeriodTwoSideways.u R (s+i) = (closed 4).getD i false) :
    ∃ r, Trace r initial := by
  let b := 2*s+1-4
  have hb : b%2=1 := by dsimp [b]; omega
  have at_b := win_mem_trap R h0 hw ((b-t0)/2)
  rw [show t0+2*((b-t0)/2)=b by dsimp [b]; omega] at at_b
  let f := fun j => drv altCol R b (j+1)
  let r := encList (seg f 210)
  have agree (i j : Nat) (bound : j+2*i<210) :
      (iterate r i).testBit j = drv altCol R (b+2*i) (j+1) := by
    rw [packed_twice b r hb]
    exact cone R b r 210 (prefix_bit 210 f) _ _ bound
  refine ⟨r, from_frames initial r (fun i hi => ?_)⟩
  have il : i < 98 := by simpa only [show initial.length = 98 by decide] using hi
  have ht := from_trap (win_mem_trap R hb at_b i) (fun j hj => agree i j (by omega))
  have ic : i < colours.length := by simpa only [initial, List.length_map] using hi
  have cell : initial[i]'hi = entry (colours[i]'ic) := by simp only [initial, List.getElem_map]
  rw [cell]
  cases i with
  | zero => exact ht
  | succ i =>
    cases i with
    | zero => exact ht
    | succ i =>
      have il' : i < (closed 4).length := by rw [show (closed 4).length = 96 by decide]; omega
      have colour : colours[i+1+1] = some ((closed 4)[i]) := by
        simp [colours]
      rw [colour]
      apply List.mem_filter.mpr
      refine ⟨ht, beq_iff_eq.mpr ?_⟩
      rw [Nat.testBit_mod_two_pow]
      have w := word i (by omega)
      unfold Rule30PeriodTwoSideways.u at w
      have gate := agree (i+1+1) 0 (by omega)
      rw [show b+2*(i+1+1) = 2*(s+i)+1 by dsimp [b]; omega] at gate
      simpa [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem il'] using gate.trans w

/-- Four closed runs of four 5-gaps cannot start two or more samples after trap entry. -/
theorem no_four_runs_of_four (R : Nat → Bool) {t0 : Nat} (h0 : t0 % 2 = 1)
    (hw : win R t0 ∈ trap) (s : Nat) (hs : t0+4 ≤ 2*s+1) :
    ¬ ∀ i, i<96 → Rule30PeriodTwoSideways.u R (s+i) = (closed 4).getD i false := by
  intro word
  obtain ⟨r,h⟩ := occurrence_trace R h0 hw s hs word
  exact Rule30TrappedRunMasks.no_trace r h

/-- The five-block word is excluded from the trapped tick itself. -/
theorem no_five_runs_of_four (R : Nat → Bool) {t0 : Nat} (h0 : t0 % 2 = 1)
    (hw : win R t0 ∈ trap) (s : Nat) (hs : t0 ≤ 2*s+1) :
    ¬ ∀ i, i<116 → Rule30PeriodTwoSideways.u R (s+i) = five.getD i false := by
  intro word
  have suffix : ∀ i, i<96 → five.getD (20+i) false = (closed 4).getD i false := by decide
  apply no_four_runs_of_four R h0 hw (s+20) (by omega)
  intro i hi
  rw [Nat.add_assoc, word (20+i) (by omega), suffix i hi]

end Ruliology.CellularAutomata.Rule30TrappedRuns

namespace Ruliology.CellularAutomata.Rule30TrappedLiftRuns
open Rule30DrivenPrefix Rule30GateTrap Rule30GateTrapLadder Rule30RunWindow
open Rule30StripCertificates Rule30TrappedRuns Rule30TrappedRunBoundary

private theorem enc_bit : ∀ (xs : List Bool) (i : Nat), (encList xs).testBit i = xs.getD i false
  | [], i => by simp [encList,List.getD_eq_getElem?_getD]
  | b::xs, 0 => by rw [Nat.testBit_zero]; cases b <;> simp [encList] <;> omega
  | b::xs, i+1 => by
    rw [Nat.testBit_succ]
    have e (v : Nat) : ((if b then 1 else 0)+2*v)/2=v := by cases b <;> simp <;> omega
    change (((if b then 1 else 0)+2*encList xs)/2).testBit i = xs.getD i false
    rw [e,enc_bit]

private theorem append_bit (xs : List Bool) (b : Bool) (j : Nat) (h : j<xs.length) :
    (xs++[b]).getD j false = xs.getD j false := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append,h]

private theorem lin_at : ∀ (j : Nat) (xs : List Bool), j+2<xs.length →
    (lin3 xs).getD j false = xor (xs.getD j false) (xs.getD (j+1) false || xs.getD (j+2) false)
  | j, [], h => by simp at h
  | j, [_], h => by simp at h <;> omega
  | j, [_,_], h => by simp at h <;> omega
  | 0, _::_::_::_, _ => rfl
  | j+1, a::b::c::xs, h => by
    exact lin_at j (b::c::xs) (by simp_all <;> omega)

private theorem tick_list {xs : List Bool} {r m : Nat} (l : Bool) (enough : m+1≤xs.length)
    (agree : ∀ j, j<m+1 → xs.getD j false=r.testBit j) (j : Nat) (hj : j<m) :
    (lin3 (l::xs)).getD j false = (step l r).testBit j := by
  rw [lin_at _ _ (by simp; omega),step_bit]
  cases j with
  | zero =>
    change xor l (xs.getD 0 false || xs.getD 1 false) = xor l (r.testBit 0 || r.testBit 1)
    rw [agree 0 (by omega),agree 1 (by omega)]
  | succ j =>
    change xor (xs.getD j false) (xs.getD (j+1) false || xs.getD (j+2) false) = xor (r.testBit j) (r.testBit (j+1) || r.testBit (j+2))
    rw [agree j (by omega),agree (j+1) (by omega),agree (j+2) (by omega)]

private theorem low_equal {x y k : Nat} (h : ∀ j, j<k → x.testBit j=y.testBit j) :
    x%2^k=y%2^k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow]
  by_cases e : j<k <;> simp [e, h]

/-- One step of a width-45 path agrees with a packed double step on the first
44 cells. Its last output cell uses the actual, freely chosen intermediate exterior. -/
private theorem lift_edges {ws : Nat → List Bool} (hp : LiftPath 45 ws) :
    ∀ t, ∃ x e, x%2^45=encList (ws t)%2^45 ∧ Edge x (encList (ws (t+1))) e := by
  intro t
  obtain ⟨x1,x2,next⟩ := hp.2.2 t
  let xs := ws t
  let q := encList (xs++[x1])
  have len : xs.length=45 := hp.length t
  let mid := lin3 (false::(xs++[x1]))
  have ml : mid.length=45 := by simp [mid,lin3_length,len]
  have first (j : Nat) (hj : j<45) : mid.getD j false = (step false q).testBit j :=
    tick_list (m := 45) false (by simp [len])
      (fun v _ => (enc_bit (xs++[x1]) v).symm) j hj
  refine ⟨q,x2,low_equal (fun j hj => ?_),low_equal (fun j hj => ?_),?_⟩
  · change (encList (xs++[x1])).testBit j = (encList xs).testBit j
    rw [enc_bit,enc_bit,append_bit _ _ _ (by omega)]
  · change (double q).testBit j = (encList (ws (t+1))).testBit j
    rw [next,enc_bit]
    symm
    exact tick_list (xs := mid++[x2]) (r := step false q) (m := 44) true (by simp [ml]) (fun v hv => by
      rw [append_bit mid x2 v (by omega)]; exact first v hv) j hj
  · rw [next,enc_bit]
    change (lin3 (true::(mid++[x2]))).getD 44 false = lastBit q x2
    rw [lin_at _ _ (by simp [ml])]
    change xor ((mid++[x2]).getD 43 false)
      (((mid++[x2]).getD 44 false) || (mid++[x2]).getD 45 false) = _
    have last : (mid++[x2]).getD 45 false = x2 := by
      simp [List.getD_eq_getElem?_getD,ml]
    rw [last,append_bit mid x2 43 (by omega),append_bit mid x2 44 (by omega),
      first 43 (by decide),first 44 (by decide)]
    rfl

private theorem seg_bit : ∀ (f : Nat → Bool) (n j : Nat), j<n → (seg f n).getD j false=f j
  | _,0,_,h => absurd h (by omega)
  | _,_+1,0,_ => rfl
  | f,n+1,j+1,h => seg_bit (fun u => f (u+1)) n j (by omega)

private theorem bounds : trapCodes.all (fun n => decide (n<2^16)) = true := by decide +kernel
private theorem low_trap {xs : List Bool} (h : xs.take 16 ∈ trap) : encList xs % 2^16 ∈ trapCodes := by
  obtain ⟨c,hc,eq⟩ := List.mem_map.mp h
  have limit : c<2^16 := of_decide_eq_true (List.all_eq_true.mp bounds _ hc)
  have id : encList xs % 2^16 = c % 2^16 := by
    apply low_equal
    intro j hj
    have e := congrArg (fun l : List Bool => l.getD j false) eq
    change (seg (fun i => c.testBit i) 16).getD j false = (xs.take 16).getD j false at e
    rw [seg_bit _ _ _ hj] at e
    simpa [enc_bit,List.getD_eq_getElem?_getD,List.getElem?_take,hj] using e.symm
  rwa [id,Nat.mod_eq_of_lt limit]

private theorem no_four_at45 {ws : Nat → List Bool} (hp : LiftPath 45 ws) (s : Nat) (hs : 2≤s) :
    ¬ ∀ i, i<96 → (ws (s+i)).headD false = (closed 4).getD i false := by
  intro word
  let start := s-2
  apply no_frames45 (fun i => encList (ws (start+i)))
  · intro i
    simpa only [Nat.add_assoc] using lift_edges hp (start+i)
  intro i hi
  have ic : i<colours.length := by simpa only [show colours.length=98 by decide] using hi
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ic,Option.getD_some]
  have ht := low_trap (hp.take16_mem (by omega) (start+i))
  cases i with
  | zero => exact ht
  | succ i =>
    cases i with
    | zero => exact ht
    | succ i =>
      have il' : i<(closed 4).length := by rw [show (closed 4).length=96 by decide]; omega
      have colour : colours[i+1+1] = some ((closed 4)[i]) := by simp [colours]
      rw [colour]
      apply List.mem_filter.mpr
      refine ⟨ht,beq_iff_eq.mpr ?_⟩
      rw [Nat.testBit_mod_two_pow]
      have time : start+(i+1+1)=s+i := by dsimp [start]; omega
      have w := word i (by omega)
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem il'] at w
      change (encList (ws (start+(i+1+1)))).testBit 0 = (closed 4)[i]
      rw [enc_bit,time]
      simpa [List.getD_eq_getElem?_getD,List.headD_eq_head?_getD,List.head?_eq_getElem?] using w

/-- Every kit ladder from width 45 upward excludes four closed runs after two steps. -/
theorem no_four_on_lift {W : Nat} (hW : 45≤W) {ws : Nat → List Bool}
    (hp : LiftPath W ws) (s : Nat) (hs : 2≤s) :
    ¬ ∀ i, i<96 → (ws (s+i)).headD false = (closed 4).getD i false := by
  intro word
  apply no_four_at45 (liftPath_take (by decide : 16≤45) hW hp) s hs
  intro i hi
  simpa only [headD_take _ _ (by decide : 1≤45)] using word i hi

/-- Every kit ladder from width 45 upward excludes five blocks from every sample. -/
theorem no_five_on_lift {W : Nat} (hW : 45≤W) {ws : Nat → List Bool}
    (hp : LiftPath W ws) (s : Nat) :
    ¬ ∀ i, i<116 → (ws (s+i)).headD false = five.getD i false := by
  intro word
  have suffix : ∀ i, i<96 → five.getD (20+i) false = (closed 4).getD i false := by decide
  apply no_four_on_lift hW hp (s+20) (by omega)
  intro i hi
  rw [Nat.add_assoc,word (20+i) (by omega),suffix _ hi]


private def strip44 (x : Nat) := seg (fun i => x.testBit i) 44
private def follow (a b : Nat) : Bool :=
  decide (strip44 b = step2 (strip44 a) (a.testBit 44) (a.testBit 45))
private def edges (a : Nat) : List Nat → Bool
  | [] => true
  | b::bs => follow a b && edges b bs
private def coast (w : List Bool) : Nat → List Bool
  | 0 => w
  | n+1 => step2 (coast w n) false false
private def walk44 (a : Nat) : List Nat → Nat → List Bool
  | [], n => coast (strip44 a) n
  | _::_, 0 => strip44 a
  | b::bs, n+1 => walk44 b bs n

private theorem walk_zero (a : Nat) (bs : List Nat) : walk44 a bs 0 = strip44 a := by
  cases bs <;> rfl

private theorem walk_next {a : Nat} {bs : List Nat} (ok : edges a bs) (n : Nat) :
    ∃ x y, walk44 a bs (n+1) = step2 (walk44 a bs n) x y := by
  induction bs generalizing a n with
  | nil => exact ⟨false,false,by simp only [walk44,coast]⟩
  | cons b bs ih =>
    obtain ⟨localStep,tail⟩ := Bool.and_eq_true_iff.mp ok
    cases n with
    | zero => exact ⟨a.testBit 44, a.testBit 45, (walk_zero b bs).trans (of_decide_eq_true localStep)⟩
    | succ n => exact ih tail n

-- Each integer carries the 44 cells, followed by its two exterior choices.
private def first44 : Nat := 251490522
private def rest44 : List Nat := [
    1057861496, 3807884183, 16428689178, 17655611477672, 48651827486375, 39451745367694,
    7000882740828, 9232369550442, 8276727919272, 14837065032359, 14871157510798, 17012327252572,
    3940897835114, 16592948627368, 2866707881383, 11200010907534, 10110095880540, 322906548586,
    1160561517032, 5486283841383, 1706712687566, 24557952161436, 4771541868090, 37792453223800,
    422781666711, 1720951318298, 24253393538728, 6319900081831, 8537250555534, 49202549869148,
    18420718864490, 16715602544552, 37685340482983, 172156534670, 714396131676, 37968941571434,
    37689766735336, 17795461398119, 49148712567950, 18576930414684, 52523949791594, 9501329990120,
    4964005519207, 18067425899470, 50262029035164, 8788720699962, 13211386841464, 12176552419735,
    15962322624026, 24672171976168, 5419916084839, 2192509118606, 7717483258972, 16292672176746,
    8564016679080, 13757757203623, 9261987790990, 8498960499292, 15237645822058, 16477792757672,
    7732109004199, 16385958352782, 8031831710044, 16620396474730, 3022738827752, 11821916955495,
    12860811908558, 15257931634332, 15781574696506, 4916429940088, 3113343501719, 12996015073050,
    14069908672168, 9948425903783, 1039692621454, 3993286249052, 17178671990890, 1313530316712,
    4723665640871, 2254012825486, 10656209264988, 3198023228778, 12524676443624, 17332807564903,
    821091419278, 3033210101852, 12891107367274, 15194174022120, 16263690035047, 8292302140366,
    14615367927452, 14342184315450, 14220923251064, 10937278112151, 3445705121306, 13263448126952,
    12423540790887]

/-- The freely driven width-44 strip actually reads the four-run word at delay two. -/
theorem four_at_width44 : ∃ ws, LiftPath 44 ws ∧ ∀ i, i<96 →
    (ws (2+i)).headD false = (closed 4).getD i false := by
  let ws := walk44 first44 rest44
  have checks : edges first44 rest44 = true := by decide +kernel
  refine ⟨ws,⟨length_seg 44 _,?_,walk_next checks⟩,?_⟩
  · exact List.mem_map.mpr ⟨28890, by decide +kernel, by decide +kernel⟩
  · decide +kernel

/-- On the trap ladder (widths at least 16), the universal four-run exclusion
holds exactly from width 45. The same width-44 path supplies every smaller witness
by taking its first W cells. -/
theorem four_width_iff {W : Nat} (hW : 16≤W) :
    (∀ ws, LiftPath W ws → ∀ s, 2≤s →
      ¬ ∀ i, i<96 → (ws (s+i)).headD false = (closed 4).getD i false) ↔ 45≤W := by
  constructor
  · intro law
    by_cases enough : 45≤W
    · exact enough
    · obtain ⟨ws,path,word⟩ := four_at_width44
      have cut := liftPath_take hW (show W≤44 by omega) path
      apply False.elim (law _ cut 2 (by decide) ?_)
      intro i hi
      simpa only [headD_take _ _ (show 1≤W by omega)] using word i hi
  · intro enough ws path s hs
    exact no_four_on_lift enough path s hs

end Ruliology.CellularAutomata.Rule30TrappedLiftRuns
