module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30GateTrap

/-!
# Two measured sites determine the next black pulse beside an alternating centre

Take a right half driven at site 0 by the black-first alternating column. At a
white tick when site 1 is black, measure sites 2 and 5. From the second white
tick onward the pairs 00, 01, 10 and 11 give the exact next black return after
4, 2, 5 and 3 white intervals, respectively. The intervening white samples
all have a white site 1. Finite rows witness all four gaps at that age and
give an exception at the first white tick.

The proof transports an eleven-cell cone through the kit's driven update.
After two physical updates only six five-site prefixes starting with a black
pulse can occur. On these prefixes the return table uses only sites 2 and 5.
The finite-clock version gives a test on the genuine singleton centre.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GatePulseReturn
open Rule30Ether Rule30StripCertificates Rule30PeriodTwoCoupled Rule30PeriodTwoSideways Rule30GateTrap

private def winW (W : Nat) (R : Nat → Bool) (t : Nat) : List Bool := rowOf (drv altCol R) t 0 W

-- The prefix identity from the kit's Rule30SidewaysLocks.seg_take.
private theorem seg_take : ∀ (m n : Nat) (f : Nat → Bool), n ≤ m → (seg f m).take n = seg f n
  | _, 0, _, _ => rfl
  | 0, _ + 1, _, h => absurd h (by omega)
  | m + 1, n + 1, f, h => by
    show f 0 :: (seg (fun i => f (i + 1)) m).take n = f 0 :: seg (fun i => f (i + 1)) n
    rw [seg_take m n _ (by omega)]

/-- The next pulse gap in white-sample intervals, given sites 2 through 5. -/
def gap (b2 b3 b4 b5 : Bool) : Nat :=
  if b2 then
    if b3 then (if b4 || b5 then 3 else 5) else (if b4 then 5 else 4)
  else
    if b3 then 4 else if b4 || b5 then 2 else 4

def nearGap (b2 b5 : Bool) : Nat :=
  if b2 then (if b5 then 3 else 5) else (if b5 then 2 else 4)

def GapAt (R : Nat → Bool) (s d : Nat) : Prop :=
  u R s = true ∧ (∀ j, 0 < j → j < d → u R (s+j) = false) ∧ u R (s+d) = true

private def readCell (w : List Bool) (j : Nat) : Bool :=
  (evolve 1 j (w.take (1+j))).headD false

private theorem parity_evolve (n t v : Nat) (h : t%2 = v%2) (row : List Bool) :
    evolve t n row = evolve v n row := by
  induction n generalizing t v row with
  | zero => rfl
  | succ n ih =>
    have wall : altCol t = altCol v := by simp only [altCol,h]
    simp only [evolve,wall]
    exact ih _ _ (by omega) _

private theorem read_physical (R : Nat → Bool) (s j : Nat) (hj : j ≤ 5) :
    readCell (winW 11 R (2*s+1)) (2*j) = u R (s+j) := by
  unfold readCell winW u
  have sub : (rowOf (drv altCol R) (2*s+1) 0 11).take (1+2*j) =
      rowOf (drv altCol R) (2*s+1) 0 (1+2*j) :=
    seg_take 11 (1+2*j) _ (by omega)
  rw [sub, parity_evolve (2*j) 1 (2*s+1) (by omega), ← rowOf_evolve R (2*j) (2*s+1) 1,
      show 2*(s+j)+1=2*s+1+2*j by omega]
  rfl

private def predicted (w : List Bool) := gap (w.getD 1 false) (w.getD 2 false)
    (w.getD 3 false) (w.getD 4 false)

private def check (w : List Bool) : Bool :=
  !w.headD false || (readCell w (2*predicted w) && ((List.range (predicted w)).all fun j =>
      j == 0 || !(readCell w (2*j))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem cone_check : (Rule30Jen.allLists 11).all check = true := by decide +kernel

/-- At any white-time pulse the four neighboring bits give the exact next pulse,
including every intervening white reading. No condition on the eastern tail. -/
theorem next_gap (R : Nat → Bool) (s : Nat) (pulse : u R s = true) :
    GapAt R s (gap (drv altCol R (2*s+1) 2) (drv altCol R (2*s+1) 3)
      (drv altCol R (2*s+1) 4) (drv altCol R (2*s+1) 5)) := by
  let w := winW 11 R (2*s+1)
  have len : w.length = 11 := length_seg 11 (fun i => drv altCol R (2*s+1) (0+i+1))
  have mem : w ∈ Rule30Jen.allLists 11 := len ▸ Rule30Jen.mem_allLists w
  have verified := List.all_eq_true.mp cone_check w mem
  have black : w.headD false = true := pulse
  have bound : predicted w ≤ 5 := by
    unfold predicted gap
    split <;> split <;> simp_all (config := {decide := true}) <;> split <;> decide
  change GapAt R s (predicted w)
  simp only [check,black,Bool.not_true,Bool.false_or,Bool.and_eq_true] at verified
  refine ⟨pulse, ?_, (read_physical R s (predicted w) bound).symm.trans verified.1⟩
  intro j hj hd
  have ok := List.all_eq_true.mp verified.2 j (List.mem_range.mpr hd)
  have nonzero : (j == 0) = false := by simp [Nat.ne_of_gt hj]
  rw [← read_physical R s j (by omega)]
  simpa only [nonzero,Bool.false_or,Bool.not_eq_true'] using ok

private def c (t : Nat) : Bool := decide (t%2=1)

private theorem two_updates (x : Nat → Bool) :
    let y := drv c x 2
    y 1=true → gap (y 2) (y 3) (y 4) (y 5) = nearGap (y 2) (y 5) := by
  dsimp only
  simp only [drv,ite_true]
  generalize x 1=a; generalize x 2=b; generalize x 3=d; generalize x 4=e
  generalize x 5=f; generalize x 6=g; generalize x 7=h
  revert a b d e f g h
  decide +kernel

/-- Site two and site five determine the exact next gap at every pulse from
the second white reading onwards, with arbitrary initial right support. -/
theorem next_gap_from_second_white (R : Nat → Bool) (s : Nat) (late : 1≤s)
    (pulse : u R s=true) :
    GapAt R s (nearGap (drv altCol R (2*s+1) 2) (drv altCol R (2*s+1) 5)) := by
  cases s with
  | zero => omega
  | succ k =>
    rw [←show gap (drv altCol R (2*(k+1)+1) 2) (drv altCol R (2*(k+1)+1) 3)
        (drv altCol R (2*(k+1)+1) 4) (drv altCol R (2*(k+1)+1) 5) =
        nearGap (drv altCol R (2*(k+1)+1) 2) (drv altCol R (2*(k+1)+1) 5) from ?_]
    · exact next_gap R _ pulse
    · have wall : (fun t => altCol (2*k+1+t))=c := by
        funext t
        apply decide_eq_decide.mpr
        change (2*k+1+t)%2=0 ↔ t%2=1
        omega
      have eq (j : Nat) : drv altCol R (2*(k+1)+1) j =
          drv c (drv altCol R (2*k+1)) 2 j := by
        rw [show 2*(k+1)+1=2*k+1+2 by omega, drv_shift,wall]
      rw [eq,eq,eq,eq]
      apply two_updates
      exact (eq 1).symm.trans pulse

abbrev seed := Rule30ZeroBoundary.IntegerForm.rowOfNat

/-- All four next gaps are attained at the same physical tick on finite
right starts. This rules out every one-bit measurement as a universal forecast. -/
theorem four_gaps_at_second_white :
    ∀ p ∈ ([(7,5),(15,4),(31,2),(39,3)] : List (Nat × Nat)), GapAt (seed p.1) 1 p.2 := by
  intro p member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> apply next_gap_from_second_white _ 1 (by decide) <;> decide

private theorem unique_gap {R s d e} (pos : 0<d) (pos' : 0<e)
    (one : GapAt R s d) (two : GapAt R s e) : d=e := by
  by_cases smaller : d<e
  · exact False.elim (Bool.noConfusion ((two.2.1 d pos smaller).symm.trans one.2.2))
  by_cases larger : e<d
  · exact False.elim (Bool.noConfusion ((one.2.1 e pos' larger).symm.trans two.2.2))
  omega

/-- The recurring exterior two-gap is a three-site spatial event from the
second white sample: a black pulse, white site two, and black site five. -/
theorem two_gap_iff_sites (R : Nat → Bool) (s : Nat) (late : 1≤s) :
    GapAt R s 2 ↔ u R s=true ∧ drv altCol R (2*s+1) 2=false ∧
      drv altCol R (2*s+1) 5=true := by
  constructor
  · intro h
    have law := next_gap_from_second_white R s late h.1
    refine ⟨h.1,?_⟩
    have pos (a b : Bool) : 0<nearGap a b := by cases a <;> cases b <;> decide
    have eq := unique_gap (by decide : 0<2) (pos _ _) h law
    have characterize : ∀ a b : Bool, 2=nearGap a b → a=false ∧ b=true := by decide
    exact characterize _ _ eq
  · rintro ⟨black,a,b⟩
    have law := next_gap_from_second_white R s late black
    rw [a,b] at law
    exact law

/-- No Boolean measurement, even an arbitrarily chosen function of the
initial row, can encode every next return at the fixed second white tick. -/
theorem no_one_bit_forecast (read : (Nat → Bool) → Bool) (decode : Bool → Nat) :
    ¬∀ R, Rule30ZeroBoundary.FinSupp R → u R 1=true →
      0 < decode (read R) ∧ GapAt R 1 (decode (read R)) := by
  intro universal
  have predicts (a g : Nat) (mem : (a,g) ∈ ([(7,5),(15,4),(31,2),(39,3)] : List (Nat × Nat)))
      (pos : 0<g) : decode (read (seed a)) = g := by
    have observation := four_gaps_at_second_white _ mem
    obtain ⟨ok,ret⟩ := universal (seed a) (Rule30ZeroBoundary.IntegerForm.finSupp_rowOfNat _) observation.1
    exact unique_gap ok pos ret observation
  have a := predicts 7 5 (by decide) (by decide)
  have b := predicts 15 4 (by decide) (by decide)
  have d := predicts 31 2 (by decide) (by decide)
  cases ha : read (seed 7) <;> cases hb : read (seed 15) <;> cases hd : read (seed 31) <;>
    simp only [ha,hb,hd] at a b d <;> omega

/-- A finite black-first row with only site three black gives the wrong
two-sensor forecast on its first white reading. -/
theorem first_white_can_fail :
    let R := seed 4
    u R 0=true ∧ nearGap (drv altCol R 1 2) (drv altCol R 1 5)=5 ∧ GapAt R 0 3 := by
  refine ⟨by decide, by decide, ?_⟩
  exact next_gap (seed 4) 0 (by decide)

private theorem agree_positive {F : Nat → Nat → Bool} (hf : IsR30 F) (a h : Nat)
    (clock : ∀ j, j<h → F (a+j) 0 = altCol j) :
    ∀ k, k≤h → ∀ p, F (a+k) (p+1) = drv altCol (F a) k (p+1) := by
  intro k
  induction k with
  | zero => intro _ p; exact (drv_init _ _ _ (Nat.succ_pos p)).symm
  | succ k ih =>
    intro bound p
    rw [show a+(k+1)=a+k+1 by omega,hf,drv_isR30]
    have eq (q : Nat) : F (a+k) q=drv altCol (F a) k q := by
      cases q with
      | zero => exact (clock k (by omega)).trans (drv_col0 ..).symm
      | succ q => exact ih (by omega) q
    rw [eq p,eq (p+1),eq (p+2)]

/-- A black pulse at the second white tick of any finite alternating strip.
The right neighbour is white at every intervening sample and black at its
forecast return. Only the centre ticks strictly before this endpoint matter. -/
theorem finite_clock_forecast {F : Nat → Nat → Bool} (hf : IsR30 F) (a d : Nat)
    (pulse : F (a+3) 1=true) (measure : nearGap (F (a+3) 2) (F (a+3) 5)=d)
    (clock : ∀ j, j<3+2*d → F (a+j) 0=altCol j) :
    (∀ i, 0<i → i<d → F (a+3+2*i) 1=false) ∧ F (a+3+2*d) 1=true := by
  have eq := agree_positive hf a (3+2*d) clock
  have obs : u (F a) 1=true := (eq 3 (by omega) 0).symm.trans pulse
  have law := next_gap_from_second_white (F a) 1 (by decide) obs
  have code : nearGap (drv altCol (F a) 3 2) (drv altCol (F a) 3 5)=d := by
    rw [←eq 3 (by omega) 1,←eq 3 (by omega) 4,measure]
  change GapAt (F a) 1 (nearGap (drv altCol (F a) 3 2) (drv altCol (F a) 3 5)) at law
  rw [code] at law
  have bit (i : Nat) (bound : i≤d) : F (a+3+2*i) 1 = u (F a) (1+i) := by
    unfold u
    rw [show a+3+2*i=a+(2*(1+i)+1) by omega]
    exact eq _ (by omega) 0
  exact ⟨fun i pos less => (bit i (by omega)).trans (law.2.1 i pos less),
    (bit d (by omega)).trans law.2.2⟩

/-- A missed pulse deadline or a premature pulse on the genuine singleton
locates a centre discrepancy strictly before the forecast endpoint. -/
theorem singleton_clock_break (a d : Nat) (pulse : Rule30Jen.cell (a+3) 1=true)
    (measure : nearGap (Rule30Jen.cell (a+3) 2) (Rule30Jen.cell (a+3) 5)=d)
    (miss : ¬((∀ i, 0<i → i<d → Rule30Jen.cell (a+3+2*i) 1=false) ∧
      Rule30Jen.cell (a+3+2*d) 1=true)) :
    ∃ j, j<3+2*d ∧ Rule30Jen.cell (a+j) 0 ≠ altCol j := by
  classical
  apply Classical.byContradiction
  intro noBreak
  apply miss
  apply finite_clock_forecast trueRight_isR30 a d pulse measure
  intro j hj
  exact Classical.byContradiction fun mismatch => noBreak ⟨j,hj,mismatch⟩

end Ruliology.CellularAutomata.Rule30GatePulseReturn
