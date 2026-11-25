module

public import Ruliology.CellularAutomata.Rule30PeriodThreeEntry

/-!
# The optimal entry slope beside a period-three column

The exceptional class-10 front of the period-three ether can advance eight
cells at a tick. `extend_back` shows that the transition can be repeated
indefinitely to the west in its finite preimages. The inverse needs only a
fixed local word and reduces the support bound by one at each step.

`family` gives rows with n eight-cell advances followed by a two-cell
advance into the recurrent class. The recurrent front retreats four cells
per ten ticks, so the rows of support 7n + O(1) still miss the corresponding
trap of `Rule30PeriodThreeEntry` at tick 21n + 1. This makes the known entry
slope of three optimal for 001 and for 011 (`sharp_001`, `sharp_011`).
The witnesses can miss by only a bounded additive time from 3D for every
large enough support allowance D (`late_001`, `late_011`).

The step needs nothing of the tail. `family_tail` gives the same run before any tail that is itself a row of Rule 30 and its
successors, and `holds_tail` how long that row shows the ether. With an ether tail, the bound 3w + 6 of
`Rule30EtherThreeErosion.erosion3_fin` has the least slope (`erosion_slope`). With a white one, a finite half beside 011 reads a
constant gate, of either colour, for three ticks a cell (`constant_gate_011`, `gate_slope_011`). By compactness one right half
keeps the exceptional front for ever (`endless`), so a right half that is not the ether can show the ether on columns 1..k for
ever: erosion needs the finite side (`not_eroded`). Beside 001 and 011 such a half never enters the trap (`stays_001`,
`stays_011`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EtherThreeSharpSlope

open Rule30Ether Rule30EtherThree Rule30EtherThreeErosion Rule30Jen
open Rule30EtherThreeDeparture Rule30PeriodThreeEntry Rule30PeriodThreeEntryTables

private theorem rule_cancel (a b c : Bool) : rule (rule a b c) b c = a := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Invert a finitely supported right row by sweeping from its white tail. -/
def back (y : Nat → Bool) (B p : Nat) : Bool :=
  if p < B then rule (y (p+1)) (back y B (p+1)) (back y B (p+2)) else false
termination_by B-p
decreasing_by all_goals omega

theorem back_white (y : Nat → Bool) {B p : Nat} (h : B ≤ p) : back y B p = false := by
  rw [back, ite_eq_right (by omega)]

theorem back_eq {y : Nat → Bool} {B : Nat} (white : ∀ p, B < p → y p = false) (p : Nat) :
    back y B p = rule (y (p+1)) (back y B (p+1)) (back y B (p+2)) := by
  by_cases h : p < B
  · rw [back, ite_eq_left h]
  · rw [back_white y (by omega), white _ (by omega), back_white y (by omega), back_white y (by omega)]
    rfl

private def stepBack (b : Bool) (v : Bool × Bool) : Bool × Bool := (rule b v.1 v.2, v.1)

private def outputs (y : Nat → Bool) (p : Nat) : Nat → List Bool
  | 0 => []
  | n+1 => y (p+1) :: outputs y (p+1) n

private theorem outputs_get (y : Nat → Bool) (p : Nat) (word : List Bool)
    (h : ∀ i, i < word.length → y (p+1+i) = word.getD i false) :
    outputs y p word.length = word := by
  induction word generalizing p with
  | nil => rfl
  | cons b word ih =>
    have h0 : y (p+1) = b := by simpa using h 0 (by simp)
    simp only [List.length_cons, outputs, h0, List.cons.injEq, true_and]
    apply ih
    intro i hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i+1) (by simpa using hi)

private theorem read_back {x y : Nat → Bool}
    (h : ∀ p, x p = rule (y (p+1)) (x (p+1)) (x (p+2))) (p n : Nat) :
    (outputs y p n).foldr stepBack (x (p+n), x (p+n+1)) = (x p, x (p+1)) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hp : p+(n+1) = p+1+n := by omega
    simp only [outputs, hp, List.foldr_cons, ih, stepBack]
    exact Prod.ext (h p).symm rfl

private theorem phase_zero : ∀ (j : Fin 12) (s : Fin 3),
    ether3 j s = ether3 (j+4*s) 0 := by decide

private theorem eth_class (j s p t : Nat) : eth j s p t = ether3 (cls j s p t) 0 := by
  unfold eth cls
  have a := phase_zero ⟨(j+p)%12, Nat.mod_lt _ (by decide)⟩
    ⟨(t+s)%3, Nat.mod_lt _ (by decide)⟩
  change ether3 ((j+p)%12) ((t+s)%3) = ether3 ((j+p)%12+4*((t+s)%3)) 0 at a
  rw [ether3_congr (j' := (j+p)%12) (φ' := (t+s)%3) (by omega) (by omega),a]
  apply ether3_congr _ rfl
  omega

private theorem before_bad {x y : Nat → Bool}
    (inv : ∀ p, x p = rule (y (p+1)) (x (p+1)) (x (p+2)))
    {j s d : Nat} (hd : 2 ≤ d) (hc : cls j s d 0 = 10)
    (pre : ∀ p, p < d+8 → y p = eth j s p 1)
    (bit0 : y (d+8) ≠ eth j s (d+8) 1)
    (bit1 : y (d+9) ≠ eth j s (d+9) 1) :
    (∀ p, p < d → x p = eth j s p 0) ∧
    x d ≠ eth j s d 0 ∧ x (d+1) ≠ eth j s (d+1) 0 := by
  have classAt (i : Nat) : cls j s (d-2+i) 1 = i % 12 := by unfold cls at hc ⊢; omega
  let word := [false,false,true,false,false,true,true,true,true,false,true]
  have sample : ∀ i, i < word.length → y (d-2+1+i) = word.getD i false := by
    intro i hi
    have iw : i < 11 := hi
    have digit (p : Nat) (h : p = d-2+(1+i)) : eth j s p 1 = ether3 (1+i) 0 := by
      rw [h, eth_class, classAt]
      exact ether3_congr (by omega) rfl
    if h : i < 9 then
      rw [pre _ (by omega), digit _ (by omega)]
      have table : ∀ k : Fin 9, ether3 (1+k) 0 = word.getD k false := by decide
      exact table ⟨i,h⟩
    else
      rcases (by omega : i = 9 ∨ i = 10) with rfl | rfl
      · rw [show d-2+1+9 = d+8 by omega]
        have h := ne_eth bit0
        rw [digit (d+8) (by omega)] at h
        exact h
      · rw [show d-2+1+10 = d+9 by omega]
        have h := ne_eth bit1
        rw [digit (d+9) (by omega)] at h
        exact h
  have hword := outputs_get y (d-2) word sample
  have left := read_back inv (d-2) 11
  change (outputs y (d-2) word.length).foldr stepBack _ = _ at left
  rw [hword] at left
  have final : ∀ a b : Bool, word.foldr stepBack (a,b) = (true,true) := by decide
  have hleft : (x (d-2), x (d-1)) = (true,true) := by
    rw [final, show d-2+1 = d-1 by omega] at left
    exact left.symm
  have rword : outputs y d 9 = word.drop 2 := by
    change outputs y d (word.drop 2).length = word.drop 2
    apply outputs_get y d (word.drop 2)
    intro i hi
    have len : (word.drop 2).length = 9 := rfl
    rw [len] at hi
    have h := sample (i+2) (show i+2 < 11 by omega)
    rw [show d-2+1+(i+2) = d+1+i by omega] at h
    have table : ∀ k : Fin 9, word.getD (k+2) false = (word.drop 2).getD k false := by decide
    exact h.trans (table ⟨i,hi⟩)
  have right := read_back inv d 9
  rw [rword] at right
  have rightPair : ∀ a b : Bool, (word.drop 2).foldr stepBack (a,b) = (false,true) := by decide
  rw [rightPair] at right
  have ec (i : Nat) : eth j s (d-2+i) 0 = ether3 (8+i) 0 := by
    rw [eth_class]
    apply ether3_congr _ rfl
    unfold cls at hc ⊢
    omega
  have spread : ∀ n p, p+n = d-2 →
      x p = eth j s p 0 ∧ x (p+1) = eth j s (p+1) 0 := by
    intro n
    induction n with
    | zero =>
      intro p hp
      have eq : p = d-2 := by omega
      subst p
      exact ⟨(congrArg Prod.fst hleft).trans (ec 0).symm,
        (show x (d-2+1) = true by rw [show d-2+1 = d-1 by omega]; exact congrArg Prod.snd hleft).trans (ec 1).symm⟩
    | succ n ih =>
      intro p hp
      obtain ⟨a,b⟩ := ih (p+1) (by omega)
      refine ⟨?_,a⟩
      rw [inv p, pre _ (by omega), a, b, eth_rule, rule_cancel]
  refine ⟨fun p hp => ?_, ?_, ?_⟩
  · if he : p = d-1 then
      subst p
      simpa [show d-2+1 = d-1 by omega] using (spread 0 (d-2) (by omega)).2
    else
      exact (spread (d-2-p) p (by omega)).1
  · have value : x d = false := (congrArg Prod.fst right).symm
    rw [value, ← show d-2+2 = d by omega, ec 2]
    decide
  · have value : x (d+1) = true := (congrArg Prod.snd right).symm
    rw [value, ← show d-2+3 = d+1 by omega, ec 3]
    decide

/-- The full history driven by ether column j in phase s. -/
def driven (j s : Nat) (R : Nat → Bool) := drv (fun t => eth j s 0 t) R

private theorem wall (j s t : Nat) (R : Nat → Bool) : driven j s R t 0 = eth j s 0 t :=
  drv_col0 _ _ _

private theorem eth_shift (j s p t : Nat) : eth j s p (t+1) = eth j (s+1) p t := by
  unfold eth
  rw [show t+1+s = t+(s+1) by omega]

private theorem shift (j s : Nat) (R Y : Nat → Bool)
    (h : ∀ p, 1 ≤ p → driven j s R 1 p = Y p) (t p : Nat) :
    driven j s R (t+1) p = driven j (s+1) Y t p := by
  induction t generalizing p with
  | zero =>
    cases p with
    | zero => rw [wall,wall,eth_shift]
    | succ p => exact (h _ (by omega)).trans (drv_init _ _ _ (by omega)).symm
  | succ t ih =>
    cases p with
    | zero => rw [wall,wall,eth_shift]
    | succ p =>
      change rule (driven j s R (t+1) p) (driven j s R (t+1) (p+1))
          (driven j s R (t+1) (p+2)) =
        rule (driven j (s+1) Y t p) (driven j (s+1) Y t (p+1))
          (driven j (s+1) Y t (p+2))
      rw [ih,ih,ih]

/-- Any finite row with an exceptional front has a finite predecessor with
the exceptional front eight places west, when the phase is moved back by one.
The support bound drops by one. -/
theorem extend_back {j s d B : Nat} {Y : Nat → Bool}
    (hd : 2 ≤ d) (hc : cls j s d 0 = 10)
    (white : ∀ p, B < p → Y p = false)
    (F : Front (driven j (s+1) Y) j (s+1) 0 (d+8))
    (bad : IsB (driven j (s+1) Y) j (s+1) 0 (d+8)) :
    ∃ R, (∀ p, B ≤ p → R p = false) ∧
      Front (driven j s R) j s 0 d ∧ IsB (driven j s R) j s 0 d ∧
      ∀ t p, driven j s R (t+1) p = driven j (s+1) Y t p := by
  let X := back Y B
  let last := driven j (s+1) Y
  have agree (p : Nat) (hp : 0 < p) : last 0 p = Y p := drv_init _ _ _ hp
  -- The value of the output at site zero is immaterial to the inverse.
  let Z : Nat → Bool := last 0
  have eqY (p : Nat) : Z (p+1) = Y (p+1) := agree _ (by omega)
  have inv (p : Nat) : X p = rule (Z (p+1)) (X (p+1)) (X (p+2)) := by
    rw [eqY]
    exact back_eq white p
  have hbad : last 0 (d+9) ≠ eth j (s+1) (d+9) 0 := by
    unfold IsB isBad at bad
    simp only [Bool.and_eq_true] at bad
    have u := bad.2
    unfold ubit at u
    exact bne_iff_ne.mp u
  obtain ⟨pre,b0,b1⟩ := before_bad inv hd hc
    (fun p hp => (F.1 p hp).trans (eth_shift _ _ _ _).symm)
    (by rw [eth_shift]; exact F.2)
    (by rw [eth_shift]; exact hbad)
  have init (p : Nat) (hp : 0 < p) : driven j s X 0 p = X p := drv_init _ _ _ hp
  have all (p : Nat) : driven j s X 0 p = X p := by
    cases p with
    | zero => rw [wall, pre 0 (by omega)]
    | succ p => exact init _ (by omega)
  refine ⟨X, fun p h => back_white _ h, ⟨fun p hp => (all p).trans (pre p hp), ?_⟩, ?_, ?_⟩
  · rwa [all]
  · unfold IsB isBad ubit
    rw [hc, all]
    simpa using bne_iff_ne.mpr b1
  · apply shift
    intro p hp
    obtain ⟨a,rfl⟩ : ∃ a, p=a+1 := ⟨p-1,by omega⟩
    change rule (driven j s X 0 a) (driven j s X 0 (a+1)) (driven j s X 0 (a+2)) = Y (a+1)
    rw [all,all,all, inv a, rule_cancel, eqY]

private def terminal (j s d p : Nat) : Bool :=
  if p < d then eth j s p 0 else p == d+1 || p == d+4

private theorem terminal_step {j s d : Nat} (hd : 2 ≤ d) (hc : cls j s d 0 = 10) :
    let F := driven j s (terminal j s d)
    Front F j s 0 d ∧ IsB F j s 0 d ∧ Front F j s 1 (d+2) ∧ IsRec F j s 1 (d+2) := by
  intro F
  have evo : IsR30 F := drv_isR30 _ _
  have ef (i : Nat) : eth j s (d-2+i) 0 = ether3 (8+i) 0 := by
    rw [eth_class]
    apply ether3_congr _ rfl
    unfold cls at hc ⊢
    omega
  have ef' (i : Nat) : eth j s (d-2+i) 1 = ether3 i 0 := by
    rw [eth_class]
    apply ether3_congr _ rfl
    unfold cls at hc ⊢
    omega
  have init (p : Nat) : F 0 p = terminal j s d p := by
    cases p with
    | zero => rw [show F 0 0 = eth j s 0 0 from wall .., terminal, ite_eq_left (by omega)]
    | succ p => exact drv_init _ _ _ (by omega)
  have eqr (p : Nat) (hp : p < d) : F 0 p = eth j s p 0 := by rw [init,terminal,ite_eq_left hp]
  have near (i : Nat) (hi : i < 7) :
      F 0 (d-2+i) = ([true,true,false,true,false,false,true] : List Bool).getD i false := by
    rw [init,terminal]
    by_cases low : i < 2
    · rw [ite_eq_left (by omega), ef]
      have ans : ∀ k : Fin 2, ether3 (8+k) 0 = ([true,true,false,true,false,false,true] : List Bool).getD k false := by decide
      exact ans ⟨i,low⟩
    · rw [ite_eq_right (by omega)]
      have ans : ∀ k : Fin 5, ((k.val == 1) || (k.val == 4)) =
          ([true,true,false,true,false,false,true] : List Bool).getD (k+2) false := by decide
      have eq1 : (d-2+i == d+1) = (i-2 == 1) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]; omega
      have eq2 : (d-2+i == d+4) = (i-2 == 4) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]; omega
      rw [eq1,eq2]
      simpa [show i-2+2 = i by omega] using ans ⟨i-2,by omega⟩
  have cut (i : Nat) (hi : i < 5) :
      F 1 (d-1+i) = ([false,false,true,true,true] : List Bool).getD i false := by
    have eq : d-1+i = (d-2+i)+1 := by omega
    rw [eq, evo, near _ (by omega),
      show d-2+i+1 = d-2+(i+1) by omega, near _ (by omega),
      show d-2+i+2 = d-2+(i+2) by omega, near _ (by omega)]
    have ans : ∀ k : Fin 5,
        rule (([true,true,false,true,false,false,true] : List Bool).getD k false)
          (([true,true,false,true,false,false,true] : List Bool).getD (k+1) false)
          (([true,true,false,true,false,false,true] : List Bool).getD (k+2) false) =
          ([false,false,true,true,true] : List Bool).getD k false := by decide
    exact ans ⟨i,hi⟩
  have localbit (i : Nat) : eth j s (d-1+i) 1 = ether3 (1+i) 0 := by
    rw [show d-1+i = d-2+(1+i) by omega,ef']
  have oldFront : Front F j s 0 d := ⟨eqr, by
    rw [← show d-2+2 = d by omega, near _ (by omega), ef]; decide⟩
  have oldBad : IsB F j s 0 d := by
    unfold IsB isBad ubit
    rw [hc, ← show d-2+3 = d+1 by omega, near _ (by omega), ef]
    decide
  have nextFront : Front F j s 1 (d+2) := ⟨fun p hp => by
    by_cases l : p < d-1
    · exact prefix_step (drv_isR30 _ _) (wall ..) eqr p (by omega)
    · obtain ⟨i, e, hi⟩ : ∃ i, p=d-1+i ∧ i < 3 := ⟨p-(d-1),by omega,by omega⟩
      rw [e,cut _ (by omega),localbit]
      have tab : ∀ k : Fin 3, ([false,false,true,true,true] : List Bool).getD k false = ether3 (1+k) 0 := by decide
      exact tab ⟨i,hi⟩,
    by rw [← show d-1+3 = d+2 by omega,cut _ (by omega),localbit]; decide⟩
  have c : cls j s (d+2) 1 = 4 := by unfold cls at hc ⊢; omega
  refine ⟨oldFront,oldBad,nextFront,?_⟩
  unfold IsRec ubit
  rw [c, ← show d-1+4 = d+2+1 by omega, cut _ (by omega),localbit]
  decide

/-- A finite row realizes n consecutive eight-column advances, followed by
a two-column advance into the recurrent class. -/
theorem family (j : Nat) : ∀ n d s : Nat, 2 ≤ d → cls j s d 0 = 10 →
    ∃ R, (∀ p, d+7*n+4 < p → R p = false) ∧
      (∀ k, k ≤ n → Front (driven j s R) j s k (d+8*k) ∧
        IsB (driven j s R) j s k (d+8*k)) ∧
      Front (driven j s R) j s (n+1) (d+8*n+2) ∧
      IsRec (driven j s R) j s (n+1) (d+8*n+2) := by
  intro n
  induction n with
  | zero =>
    intro d s hd hc
    obtain ⟨hf,hb,hn,hr⟩ := terminal_step hd hc
    refine ⟨terminal j s d, ?_, fun k hk => ?_, by simpa using hn, by simpa using hr⟩
    · intro p hp
      unfold terminal
      rw [ite_eq_right (by omega)]
      simp [show p ≠ d+1 by omega, show p ≠ d+4 by omega]
    · have eq : k = 0 := by omega
      subst k
      simpa using And.intro hf hb
  | succ n ih =>
    intro d s hd hc
    have next : cls j (s+1) (d+8) 0 = 10 := by unfold cls at hc ⊢; omega
    obtain ⟨Y,hy,chain,hf,hr⟩ := ih (d+8) (s+1) (by omega) next
    have start := chain 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at start
    obtain ⟨R,hw,h0,hb,eval⟩ := extend_back hd hc hy start.1 start.2
    have cs (p t : Nat) : cls j s p (t+1) = cls j (s+1) p t := by
      unfold cls
      congr 1
      omega
    have ft (t p : Nat) (h : Front (driven j (s+1) Y) j (s+1) t p) :
        Front (driven j s R) j s (t+1) p :=
      ⟨fun q hq => by rw [eval,eth_shift]; exact h.1 q hq,
        by rw [eval,eth_shift]; exact h.2⟩
    have ut (t p : Nat) : ubit (driven j s R) j s (t+1) p =
        ubit (driven j (s+1) Y) j (s+1) t p := by
      unfold ubit
      rw [eval,eth_shift]
    refine ⟨R, fun p hp => hw p (by omega), ?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero => simpa using And.intro h0 hb
      | succ k =>
        have eq : d+8*(k+1) = d+8+8*k := by omega
        obtain ⟨a,b⟩ := chain k (by omega)
        rw [eq]
        exact ⟨ft _ _ a, by unfold IsB at *; rwa [cs,ut]⟩
    · rw [show d+8*(n+1)+2 = d+8+8*n+2 by omega]
      exact ft _ _ hf
    · rw [show d+8*(n+1)+2 = d+8+8*n+2 by omega]
      unfold IsRec at *
      rwa [cs,ut]

private theorem return_front {F : Nat → Nat → Bool} {j s : Nat} (hF : IsR30 F)
    (h0 : ∀ t, F t 0 = eth j s 0 t) {d : Nat} (hd : 7 ≤ d) :
    ∀ n t, Front F j s t (d+4*n) → IsRec F j s t (d+4*n) →
      Front F j s (t+10*n) d := by
  intro n
  induction n with
  | zero => intro t h _; simpa using h
  | succ n ih =>
    intro t h r
    obtain ⟨hf,hr,_⟩ := ten_ticks hF (fun u _ => h0 u) h r (by omega)
    rw [show d+4*(n+1)-4 = d+4*n by omega] at hf hr
    simpa only [show t+10+10*n = t+10*(n+1) by omega] using ih (t+10) hf hr

private theorem example_row (w : List Bool) (trap : List Nat) (j s d g n : Nat)
    (align : ∀ k, ether3 j k = wordAt3 w k) (hd : 14 < d)
    (hc : cls j s d 0 = 10) (hg : (s+1)%3 = g%3)
    (outside : code (fun _ p => ether3 (j+p) g) 0 14 ∉ trap) :
    ∃ R, (∀ p, 7*n+d+4 < p → R p = false) ∧
      ¬ InTrap trap (half w R s) (21*n+1) := by
  obtain ⟨R,hwhite,_,hf,hr⟩ := family j n d s (by omega) hc
  let F := driven j s R
  have eq : d+8*n+2 = d+2+4*(2*n) := by omega
  rw [eq] at hf hr
  have last := return_front (drv_isR30 _ _) (wall j s · R) (show 7 ≤ d+2 by omega) (2*n) (n+1) hf hr
  rw [show n+1+10*(2*n) = 21*n+1 by omega] at last
  have same : code F (21*n+1) 14 = code (fun _ p => ether3 (j+p) g) 0 14 := by
    unfold code
    congr 1
    apply Rule30Ether.seg_congr
    intro i hi
    exact (last.1 (i+1) (by omega)).trans (ether3_congr rfl (by omega))
  have run : half w R s = F := by
    have hWall : (fun t => wordAt3 w (t+s)) = (fun t => eth j s 0 t) := by
      funext t
      unfold eth
      rw [Nat.add_zero, align]
    exact congrArg (fun c => drv c R) hWall
  exact ⟨R,fun p hp => hwhite p (by omega), by rwa [run,InTrap,same]⟩

set_option maxRecDepth 10000 in
/-- Arbitrarily large finite rows beside 001 stay outside `trap001` at
gate ticks 21n+1, with support at most 7n+26. -/
theorem delayed_001 (n : Nat) :
    ∃ R, (∀ p, 7*n+26 < p → R p = false) ∧
      ¬ InTrap trap001 (half w001 R 0) (21*n+1) := by
  have out : code (fun _ p => ether3 p 1) 0 14 ∉ trap001 := by decide +kernel
  simpa using example_row w001 trap001 0 0 22 1 n
    (aligned3_spec (w := w001) (j0 := 0) (s := 0) (by decide))
    (by decide) (by decide) (by decide) (by simpa using out)

set_option maxRecDepth 10000 in
/-- Beside 011 the same gate ticks can miss the trap with support at most 7n+31. -/
theorem delayed_011 (n : Nat) :
    ∃ R, (∀ p, 7*n+31 < p → R p = false) ∧
      ¬ InTrap trap011 (half w011 R 2) (21*n+1) := by
  have out : code (fun _ p => ether3 (11+p) 0) 0 14 ∉ trap011 := by decide +kernel
  simpa using example_row w011 trap011 11 2 27 0 n
    (aligned3_spec (w := w011) (j0 := 11) (s := 0) (by decide))
    (by decide) (by decide) (by decide) out

private theorem affine_arith {p q r c : Nat} (h : p < 3*q) :
    let n := p*c+r
    p*(7*n+c)+r ≤ q*(21*n+1) := by
  intro n
  have a := Nat.mul_le_mul_right n (show 7*p+1 ≤ 21*q by omega)
  have l : p*(7*n+c)+r = (7*p+1)*n := by
    rw [Nat.mul_add, Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, Nat.mul_comm p 7]
    dsimp [n]
    omega
  have u : q*(21*n+1) = 21*q*n+q := by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm q 21]
  rw [l,u]
  exact Nat.le_trans a (Nat.le_add_right ..)

/-- The slope three of `finite_enters_001` in `Rule30PeriodThreeEntry` is optimal. -/
theorem sharp_001 {p q r : Nat}
    (h : ∀ (R : Nat → Bool) (D : Nat), (∀ x, D < x → R x = false) → ∀ φ t, (t+φ)%3 = 1 →
      p*D+r ≤ q*t → InTrap trap001 (half w001 R φ) t) : 3*q ≤ p := by
  apply Nat.le_of_not_lt
  intro lt
  obtain ⟨R,hw,out⟩ := delayed_001 (p*26+r)
  exact out (h R _ hw 0 _ (by omega) (affine_arith lt))

/-- The slope three of `finite_enters_011` in `Rule30PeriodThreeEntry` is optimal. -/
theorem sharp_011 {p q r : Nat}
    (h : ∀ (R : Nat → Bool) (D : Nat), (∀ x, D < x → R x = false) → ∀ φ t, (t+φ)%3 = 0 →
      p*D+r ≤ q*t → InTrap trap011 (half w011 R φ) t) : 3*q ≤ p := by
  apply Nat.le_of_not_lt
  intro lt
  obtain ⟨R,hw,out⟩ := delayed_011 (p*31+r)
  exact out (h R _ hw 2 _ (by omega) (affine_arith lt))

/-- A trap miss within 95 ticks of 3D exists for every support allowance D ≥ 26. -/
theorem late_001 {D : Nat} (hD : 26 ≤ D) :
    ∃ R t, (∀ p, D < p → R p = false) ∧ t % 3 = 1 ∧ 3*D ≤ t+95 ∧
      ¬ InTrap trap001 (half w001 R 0) t := by
  let n := (D-26)/7
  obtain ⟨R,hw,out⟩ := delayed_001 n
  refine ⟨R,21*n+1,fun p hp => hw p (by dsimp [n]; omega),by omega,?_ ,out⟩
  dsimp [n]
  omega

/-- A trap miss within 110 ticks of 3D exists for every support allowance D ≥ 31. -/
theorem late_011 {D : Nat} (hD : 31 ≤ D) :
    ∃ R t, (∀ p, D < p → R p = false) ∧ (t+2)%3 = 0 ∧ 3*D ≤ t+110 ∧
      ¬ InTrap trap011 (half w011 R 2) t := by
  let n := (D-31)/7
  obtain ⟨R,hw,out⟩ := delayed_011 n
  refine ⟨R,21*n+1,fun p hp => hw p (by dsimp [n]; omega),by omega,?_ ,out⟩
  dsimp [n]
  omega

/-! ### Any tail -/

/-- Invert a row that is the row `T` from `B` on, by sweeping west. -/
def backTail (T y : Nat → Bool) (B p : Nat) : Bool :=
  if p < B then rule (y (p+1)) (backTail T y B (p+1)) (backTail T y B (p+2)) else T p
termination_by B-p
decreasing_by all_goals omega

theorem backTail_tail (T y : Nat → Bool) {B p : Nat} (h : B ≤ p) : backTail T y B p = T p := by
  rw [backTail, ite_eq_right (by omega)]

theorem backTail_eq {T T' y : Nat → Bool} {B : Nat} (hT : ∀ p, T' (p+1) = rule (T p) (T (p+1)) (T (p+2)))
    (tail : ∀ p, B < p → y p = T' p) (p : Nat) :
    backTail T y B p = rule (y (p+1)) (backTail T y B (p+1)) (backTail T y B (p+2)) := by
  by_cases h : p < B
  · rw [backTail, ite_eq_left h]
  · rw [backTail_tail T y (by omega), tail _ (by omega), backTail_tail T y (by omega),
      backTail_tail T y (by omega), hT, rule_cancel]

/-- `extend_back` with any tail that is itself a row of Rule 30 and its successor. -/
theorem extend_back_tail {j s d B : Nat} {Y T T' : Nat → Bool} (hT : ∀ p, T' (p+1) = rule (T p) (T (p+1)) (T (p+2)))
    (hd : 2 ≤ d) (hc : cls j s d 0 = 10)
    (tail : ∀ p, B < p → Y p = T' p)
    (F : Front (driven j (s+1) Y) j (s+1) 0 (d+8))
    (bad : IsB (driven j (s+1) Y) j (s+1) 0 (d+8)) :
    ∃ R, (∀ p, B ≤ p → R p = T p) ∧
      Front (driven j s R) j s 0 d ∧ IsB (driven j s R) j s 0 d ∧
      ∀ t p, driven j s R (t+1) p = driven j (s+1) Y t p := by
  let X := backTail T Y B
  let last := driven j (s+1) Y
  have agree (p : Nat) (hp : 0 < p) : last 0 p = Y p := drv_init _ _ _ hp
  let Z : Nat → Bool := last 0
  have eqY (p : Nat) : Z (p+1) = Y (p+1) := agree _ (by omega)
  have inv (p : Nat) : X p = rule (Z (p+1)) (X (p+1)) (X (p+2)) := by
    rw [eqY]
    exact backTail_eq hT tail p
  have hbad : last 0 (d+9) ≠ eth j (s+1) (d+9) 0 := by
    unfold IsB isBad at bad
    simp only [Bool.and_eq_true] at bad
    have u := bad.2
    unfold ubit at u
    exact bne_iff_ne.mp u
  obtain ⟨pre,b0,b1⟩ := before_bad inv hd hc
    (fun p hp => (F.1 p hp).trans (eth_shift _ _ _ _).symm)
    (by rw [eth_shift]; exact F.2)
    (by rw [eth_shift]; exact hbad)
  have init (p : Nat) (hp : 0 < p) : driven j s X 0 p = X p := drv_init _ _ _ hp
  have all (p : Nat) : driven j s X 0 p = X p := by
    cases p with
    | zero => rw [wall, pre 0 (by omega)]
    | succ p => exact init _ (by omega)
  refine ⟨X, fun p h => backTail_tail _ _ h, ⟨fun p hp => (all p).trans (pre p hp), ?_⟩, ?_, ?_⟩
  · rwa [all]
  · unfold IsB isBad ubit
    rw [hc, all]
    simpa using bne_iff_ne.mpr b1
  · apply shift
    intro p hp
    obtain ⟨a,rfl⟩ : ∃ a, p=a+1 := ⟨p-1,by omega⟩
    change rule (driven j s X 0 a) (driven j s X 0 (a+1)) (driven j s X 0 (a+2)) = Y (a+1)
    rw [all,all,all, inv a, rule_cancel, eqY]

private theorem cone {c x y : Nat → Bool} {N : Nat} (h : ∀ p, p ≤ N → x p = y p) (t : Nat) :
    ∀ p, p+t ≤ N → drv c x t p = drv c y t p := by
  induction t with
  | zero =>
    intro p hp
    cases p with
    | zero => rfl
    | succ p => rw [drv_init _ _ _ (by omega), drv_init _ _ _ (by omega)]; exact h _ (by omega)
  | succ t ih =>
    intro p hp
    cases p with
    | zero => rw [drv_col0, drv_col0]
    | succ p =>
      change rule (drv c x t p) (drv c x t (p+1)) (drv c x t (p+2)) =
        rule (drv c y t p) (drv c y t (p+1)) (drv c y t (p+2))
      rw [ih p (by omega), ih (p+1) (by omega), ih (p+2) (by omega)]

/-- `family` with any tail. Let `bg s` be rows with `bg (s+1)` the successor of `bg s`. Some row agrees with `bg s` beyond
`d+7n+4` and makes `n` advances of eight columns, then one of two columns into the recurrent class. -/
theorem family_tail (j : Nat) {bg : Nat → Nat → Bool}
    (hbg : ∀ s p, bg (s+1) (p+1) = rule (bg s p) (bg s (p+1)) (bg s (p+2))) : ∀ n d s : Nat, 2 ≤ d → cls j s d 0 = 10 →
    ∃ R, (∀ p, d+7*n+4 < p → R p = bg s p) ∧
      (∀ k, k ≤ n → Front (driven j s R) j s k (d+8*k) ∧
        IsB (driven j s R) j s k (d+8*k)) ∧
      Front (driven j s R) j s (n+1) (d+8*n+2) ∧
      IsRec (driven j s R) j s (n+1) (d+8*n+2) := by
  intro n
  induction n with
  | zero =>
    intro d s hd hc
    obtain ⟨hf,hb,hn,hr⟩ := terminal_step hd hc
    let R := fun p => if p ≤ d+4 then terminal j s d p else bg s p
    have same : ∀ p, p ≤ d+4 → R p = terminal j s d p := fun p hp => ite_eq_left hp
    have e0 (p : Nat) (hp : p ≤ d+4) : driven j s R 0 p = driven j s (terminal j s d) 0 p :=
      cone same 0 p hp
    have e1 (p : Nat) (hp : p ≤ d+3) : driven j s R 1 p = driven j s (terminal j s d) 1 p :=
      cone same 1 p (by omega)
    refine ⟨R, fun p hp => ite_eq_right (by omega), fun k hk => ?_, ?_, ?_⟩
    · have eq : k = 0 := by omega
      subst k
      rw [Nat.mul_zero, Nat.add_zero]
      refine ⟨⟨fun p hp => (e0 p (by omega)).trans (hf.1 p hp), ?_⟩, ?_⟩
      · rw [e0 d (by omega)]; exact hf.2
      · unfold IsB ubit at hb ⊢; rw [e0 (d+1) (by omega)]; exact hb
    · rw [Nat.mul_zero, Nat.add_zero]
      exact ⟨fun p hp => (e1 p (by omega)).trans (hn.1 p hp), by rw [e1 (d+2) (by omega)]; exact hn.2⟩
    · rw [Nat.mul_zero, Nat.add_zero]
      unfold IsRec ubit at hr ⊢; rw [e1 (d+2+1) (by omega)]; exact hr
  | succ n ih =>
    intro d s hd hc
    have next : cls j (s+1) (d+8) 0 = 10 := by unfold cls at hc ⊢; omega
    obtain ⟨Y,hy,chain,hf,hr⟩ := ih (d+8) (s+1) (by omega) next
    have start := chain 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at start
    obtain ⟨R,hw,h0,hb,eval⟩ := extend_back_tail (hbg s) hd hc hy start.1 start.2
    have cs (p t : Nat) : cls j s p (t+1) = cls j (s+1) p t := by
      unfold cls
      congr 1
      omega
    have ft (t p : Nat) (h : Front (driven j (s+1) Y) j (s+1) t p) :
        Front (driven j s R) j s (t+1) p :=
      ⟨fun q hq => by rw [eval,eth_shift]; exact h.1 q hq,
        by rw [eval,eth_shift]; exact h.2⟩
    have ut (t p : Nat) : ubit (driven j s R) j s (t+1) p =
        ubit (driven j (s+1) Y) j (s+1) t p := by
      unfold ubit
      rw [eval,eth_shift]
    refine ⟨R, fun p hp => hw p (by omega), ?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero => simpa using And.intro h0 hb
      | succ k =>
        have eq : d+8*(k+1) = d+8+8*k := by omega
        obtain ⟨a,b⟩ := chain k (by omega)
        rw [eq]
        exact ⟨ft _ _ a, by unfold IsB at *; rwa [cs,ut]⟩
    · rw [show d+8*(n+1)+2 = d+8+8*n+2 by omega]
      exact ft _ _ hf
    · rw [show d+8*(n+1)+2 = d+8+8*n+2 by omega]
      unfold IsRec at *
      rwa [cs,ut]

/-! ### How long the ether is held -/

/-- The row of `family_tail` shows the ether on every column west of `d` at every tick up to `21n + 5`. -/
theorem holds_tail (j : Nat) {bg : Nat → Nat → Bool}
    (hbg : ∀ s p, bg (s+1) (p+1) = rule (bg s p) (bg s (p+1)) (bg s (p+2))) (n : Nat) {d s : Nat} (hd : 2 ≤ d)
    (hc : cls j s d 0 = 10) :
    ∃ R, (∀ p, d+7*n+4 < p → R p = bg s p) ∧ driven j s R 0 d ≠ eth j s d 0 ∧
      ∀ t, t ≤ 21*n+5 → ∀ p, p < d → driven j s R t p = eth j s p t := by
  obtain ⟨R,ht,chain,hf,hr⟩ := family_tail j hbg n d s hd hc
  have start := (chain 0 (by omega)).1
  rw [Nat.mul_zero, Nat.add_zero] at start
  refine ⟨R, ht, start.2, fun t hT p hp => ?_⟩
  rcases Nat.lt_or_ge n t with late | early
  · have q0 : psi (driven j s R) j s (n+1) (d+8*n+2) = 4 := by
      have c : cls j s (d+8*n+2) (n+1) = 4 := by unfold cls at hc ⊢; omega
      unfold psi psiR
      rw [c]
      rfl
    have key : ∀ m, n+1+m ≤ 21*n+5 → ∃ E, Front (driven j s R) j s (n+1+m) E ∧
        IsRec (driven j s R) j s (n+1+m) E ∧
        5*E+2*m+psi (driven j s R) j s (n+1+m) E = 5*(d+8*n+2)+4 := by
      intro m
      induction m with
      | zero => intro _; exact ⟨_, hf, hr, by rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero, q0]⟩
      | succ m ih =>
        intro hm
        obtain ⟨E,fE,rE,eE⟩ := ih (by omega)
        have q := psi_le rE
        obtain ⟨E',fE',rE',-,-,eE'⟩ :=
          rigid_step (F := driven j s R) (drv_isR30 _ _) (wall j s _ R) (by omega) fE rE
        exact ⟨E', fE', rE', by rw [show n+1+(m+1) = n+1+m+1 by omega]; omega⟩
    obtain ⟨E,fE,rE,eE⟩ := key (t-(n+1)) (by omega)
    rw [show n+1+(t-(n+1)) = t by omega] at fE rE eE
    have q := psi_le rE
    exact fE.1 p (by omega)
  · exact ((chain t early).1).1 p (by omega)

/-- The bound `3 w + 6` of `Rule30EtherThreeErosion.erosion3_fin` has the least slope. Beside every ether column, for every `n`,
some row is ether on the columns `1..k` and beyond `k + w`, where `w = 7n + 5`, is not the ether, and has ether on the columns
`1..k` at every tick up to `21n + 5 = 3w - 10`. -/
theorem erosion_slope (j s n : Nat) :
    ∃ (R : Nat → Bool) (k : Nat), 1 ≤ k ∧
      (∀ p, k+(7*n+5) < p → driven j s R 0 p = eth j s p 0) ∧
      driven j s R 0 (k+1) ≠ eth j s (k+1) 0 ∧
      ∀ t, t ≤ 21*n+5 → ∀ p, p ≤ k → driven j s R t p = eth j s p t := by
  let d := 2+(8+11*(j+4*s))%12
  have hd : 2 ≤ d := Nat.le_add_right ..
  have hc : cls j s d 0 = 10 := by
    unfold cls
    change (j+(2+(8+11*(j+4*s))%12)+4*(0+s))%12 = 10
    omega
  have hbg : ∀ s p, eth j (s+1) (p+1) 0 = rule (eth j s p 0) (eth j s (p+1) 0) (eth j s (p+2) 0) := fun s p => by
    rw [← eth_shift, eth_rule]
  obtain ⟨R,ht,h0,h⟩ := holds_tail j (bg := fun s p => eth j s p 0) hbg n hd hc
  refine ⟨R, d-1, by omega, fun p hp => ?_, by rwa [show d-1+1 = d by omega], fun t hT p hp => h t hT p (by omega)⟩
  rw [show driven j s R 0 p = R p from drv_init _ _ _ (by omega), ht p (by omega)]

/-- A finite half beside 011 can read one colour, either one, at every white tick of the drive that begins a period up to
`21n + 5`, with white beyond `7n + 17`, from any phase. -/
theorem constant_gate_011 (b : Bool) (n φ : Nat) :
    ∃ R : Nat → Bool, (∀ p, 7*n+17 < p → R p = false) ∧
      ∀ t, t ≤ 21*n+5 → (t+φ)%3 = 0 → half w011 R φ t 1 = b := by
  obtain ⟨j,align,colour⟩ : ∃ j, (∀ k, ether3 j k = wordAt3 w011 k) ∧ ether3 (j+1) 0 = b := by
    cases b
    · exact ⟨11, aligned3_spec (w := w011) (j0 := 11) (s := 0) (by decide), by decide⟩
    · exact ⟨2, aligned3_spec (w := w011) (j0 := 2) (s := 0) (by decide), by decide⟩
  let d := 2+(8+11*(j+4*φ))%12
  have hd : 2 ≤ d := Nat.le_add_right ..
  have hd' : d ≤ 13 := by
    change 2+(8+11*(j+4*φ))%12 ≤ 13
    omega
  have hc : cls j φ d 0 = 10 := by
    unfold cls
    change (j+(2+(8+11*(j+4*φ))%12)+4*(0+φ))%12 = 10
    omega
  obtain ⟨R,ht,-,h⟩ := holds_tail j (bg := fun _ _ => false) (fun _ _ => rfl) n hd hc
  refine ⟨R, fun p hp => ht p (by omega), fun t hT hg => ?_⟩
  have run : half w011 R φ = driven j φ R := by
    have hWall : (fun t => wordAt3 w011 (t+φ)) = (fun t => eth j φ 0 t) := by
      funext t
      unfold eth
      rw [Nat.add_zero, align]
    exact congrArg (fun c => drv c R) hWall
  rw [run, h t hT 1 (by omega), ← colour]
  exact ether3_congr rfl (by omega)

/-- So any affine deadline for the other colour beside 011 has slope at least three. -/
theorem gate_slope_011 {p q r : Nat} (b : Bool)
    (h : ∀ (R : Nat → Bool) (D : Nat), (∀ x, D < x → R x = false) → ∀ φ,
      ∃ t, q*t ≤ p*D+r ∧ (t+φ)%3 = 0 ∧ half w011 R φ t 1 = !b) : 3*q ≤ p := by
  apply Nat.le_of_not_lt
  intro lt
  let n := 17*p+r
  obtain ⟨R,hw,const⟩ := constant_gate_011 b n 0
  obtain ⟨t,hq,g,hb⟩ := h R _ hw 0
  have late : 21*n+6 ≤ t := by
    apply Nat.le_of_not_lt
    intro early
    rw [const t (by omega) g] at hb
    cases b <;> exact absurd hb (by decide)
  have a := Nat.mul_le_mul_right (7*n) (show p+1 ≤ 3*q by omega)
  have c := Nat.mul_le_mul_left q late
  have e1 : (p+1)*(7*n) = 7*(p*n)+7*n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  have e2 : 3*q*(7*n) = 21*(q*n) := by
    rw [Nat.mul_mul_mul_comm]
  have e3 : q*(21*n+6) = 21*(q*n)+6*q := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm q 6]
  have e4 : p*(7*n+17)+r = 7*(p*n)+(17*p+r) := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm p 17, Nat.add_assoc]
  have e5 : 17*p+r = n := rfl
  omega

/-! ### An endless run -/

private def Often (P : Nat → Prop) : Prop := ∀ n, ∃ i, n ≤ i ∧ P i

private theorem often_split {P : Nat → Prop} (h : Often P) (b : Nat → Bool) :
    ∃ v, Often fun i => P i ∧ b i = v := by
  by_cases h1 : Often fun i => P i ∧ b i = true
  · exact ⟨true, h1⟩
  · refine ⟨false, fun n => ?_⟩
    unfold Often at h1
    simp only [Classical.not_forall, not_exists] at h1
    obtain ⟨u, hu⟩ := h1
    obtain ⟨i, hi, pi⟩ := h (max n u)
    exact ⟨i, by omega, pi, Bool.eq_false_iff.mpr fun e => hu i ⟨by omega, pi, e⟩⟩

private structure Pool where
  pred : Nat → Prop
  often : Often pred

private noncomputable def pools (bits : Nat → Nat → Bool) : Nat → Pool
  | 0 => ⟨fun _ => True, fun n => ⟨n, Nat.le_refl _, trivial⟩⟩
  | n+1 => ⟨_, (often_split (pools bits n).often (fun i => bits i n)).choose_spec⟩

private theorem limit (bits : Nat → Nat → Bool) :
    ∃ x : Nat → Bool, ∀ n, Often fun i => ∀ p, p < n → bits i p = x p := by
  let x := fun n => (often_split (pools bits n).often (fun i => bits i n)).choose
  have fits (n i : Nat) (h : (pools bits n).pred i) : ∀ p, p < n → bits i p = x p := by
    induction n with
    | zero => intro p hp; omega
    | succ n ih =>
      change (pools bits n).pred i ∧ bits i n = x n at h
      intro p hp
      by_cases eq : p = n
      · exact eq ▸ h.2
      · exact ih h.1 p (by omega)
  exact ⟨x, fun n bound => by
    obtain ⟨i,hi,h⟩ := (pools bits n).often bound
    exact ⟨i,hi,fits n i h⟩⟩

/-- **An endless exceptional run.** Some right half keeps the exceptional front for ever, eight columns east at each tick. -/
theorem endless (j : Nat) {d s : Nat} (hd : 2 ≤ d) (hc : cls j s d 0 = 10) :
    ∃ R, ∀ k, Front (driven j s R) j s k (d+8*k) ∧ IsB (driven j s R) j s k (d+8*k) := by
  let row := fun n => (family j n d s hd hc).choose
  have spec := fun n => (family j n d s hd hc).choose_spec
  obtain ⟨R,lim⟩ := limit row
  refine ⟨R, fun k => ?_⟩
  obtain ⟨n,hn,same⟩ := lim (d+9*k+2) k
  obtain ⟨f,b⟩ := (spec n).2.1 k hn
  have eq (p : Nat) (hp : p ≤ d+8*k+1) : driven j s R k p = driven j s (row n) k p :=
    cone (N := d+9*k+1) (fun q hq => (same q (by omega)).symm) k p (by omega)
  refine ⟨⟨fun p hp => (eq p (by omega)).trans (f.1 p hp), ?_⟩, ?_⟩
  · rw [eq _ (by omega)]; exact f.2
  · unfold IsB ubit at b ⊢; rw [eq _ (by omega)]; exact b

/-- **An infinite right side need not erode the ether.** Beside every ether column, for arbitrarily large `k`, there is a right
half that differs from the ether first at column `k + 1` and whose columns `1..k` are the ether for ever. Column `p` is the
ether at every tick `t` with `p ≤ k + 8 t`. -/
theorem not_eroded (j s K : Nat) :
    ∃ (R : Nat → Bool) (k : Nat), K < k ∧ driven j s R 0 (k+1) ≠ eth j s (k+1) 0 ∧
      ∀ t p, p ≤ k+8*t → driven j s R t p = eth j s p t := by
  let d := K+2+(8+11*(j+4*s+K))%12
  have hd : K+2 ≤ d := Nat.le_add_right ..
  have hc : cls j s d 0 = 10 := by
    unfold cls
    change (j+(K+2+(8+11*(j+4*s+K))%12)+4*(0+s))%12 = 10
    omega
  obtain ⟨R,h⟩ := endless j (by omega) hc
  have h0 := (h 0).1.2
  rw [Nat.mul_zero, Nat.add_zero] at h0
  exact ⟨R, d-1, by omega, by rwa [show d-1+1 = d by omega], fun t p hp => (h t).1.1 p (by omega)⟩

private theorem stays (w : List Bool) (trap : List Nat) (j s d g : Nat)
    (align : ∀ k, ether3 j k = wordAt3 w k) (hd : 14 < d)
    (hc : cls j s d 0 = 10)
    (outside : code (fun _ p => ether3 (j+p) g) 0 14 ∉ trap) :
    ∃ R, half w R s 0 d ≠ eth j s d 0 ∧ ∀ t, (t+s)%3 = g%3 → ¬ InTrap trap (half w R s) t := by
  obtain ⟨R,h⟩ := endless j (by omega) hc
  have run : half w R s = driven j s R := by
    have hWall : (fun t => wordAt3 w (t+s)) = (fun t => eth j s 0 t) := by
      funext t
      unfold eth
      rw [Nat.add_zero, align]
    exact congrArg (fun c => drv c R) hWall
  have h0 := (h 0).1.2
  rw [Nat.mul_zero, Nat.add_zero] at h0
  refine ⟨R, by rw [run]; exact h0, fun t ht => ?_⟩
  have same : code (driven j s R) t 14 = code (fun _ p => ether3 (j+p) g) 0 14 := by
    unfold code
    congr 1
    apply Rule30Ether.seg_congr
    intro i hi
    exact ((h t).1.1 (i+1) (by omega)).trans (ether3_congr rfl (by omega))
  rwa [run, InTrap, same]

set_option maxRecDepth 10000 in
/-- Beside 001 a right half that is not the ether stays outside the trap at every gate tick. -/
theorem stays_001 : ∃ R, half w001 R 0 0 22 ≠ ether3 22 0 ∧ ∀ t, t%3 = 1 → ¬ InTrap trap001 (half w001 R 0) t := by
  have out : code (fun _ p => ether3 p 1) 0 14 ∉ trap001 := by decide +kernel
  obtain ⟨R,h0,h⟩ := stays w001 trap001 0 0 22 1
    (aligned3_spec (w := w001) (j0 := 0) (s := 0) (by decide))
    (by decide) (by decide) (by simpa using out)
  exact ⟨R, by simpa [eth] using h0, fun t ht => h t (by omega)⟩

set_option maxRecDepth 10000 in
/-- Beside 011 likewise. -/
theorem stays_011 : ∃ R, half w011 R 2 0 27 ≠ ether3 38 2 ∧ ∀ t, (t+2)%3 = 0 → ¬ InTrap trap011 (half w011 R 2) t := by
  have out : code (fun _ p => ether3 (11+p) 0) 0 14 ∉ trap011 := by decide +kernel
  obtain ⟨R,h0,h⟩ := stays w011 trap011 11 2 27 0
    (aligned3_spec (w := w011) (j0 := 11) (s := 0) (by decide))
    (by decide) (by decide) out
  exact ⟨R, by simpa [eth] using h0, fun t ht => h t (by omega)⟩

end Ruliology.CellularAutomata.Rule30EtherThreeSharpSlope
