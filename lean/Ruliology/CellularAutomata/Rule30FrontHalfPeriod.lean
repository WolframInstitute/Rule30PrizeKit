module
public import Ruliology.CellularAutomata.Rule30RightPrefixBound
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

/-! A three-bit anchor embeds the alternating stripe-front dynamics in ordinary
right diagonals. The generic right-bounded prefix clock then bounds its return.
Front dynamics and its old universal return are from the official kit; prefix
half-rate accounting reuses the kit's RecordCharge proof. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30FrontHalfPeriod
open Rule30RightProfiles Rule30RightPrefixClock Rule30RightPrefixBound
open Rule30ZeroBoundaryStripeFront Rule30ZeroBoundaryStripeFrontLift
open Rule30RecordCharge
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def code (W : Nat) : Nat := (W <<< 3) ||| 5
def seed (W : Nat) (p : Int) : Bool :=
  if 0 < p then false else (code W).testBit (-p).toNat
def D (W : Nat) (j : Int) (t : Nat) : Bool := rightDiag (seed W) j t
def phase (t : Nat) : Bool := decide (t % 2 = 1)

theorem seed_right (W : Nat) : ∀ p, 0 < p → seed W p = false := by
  intro p hp
  exact ite_eq_left hp

theorem D_init (W j : Nat) : D W (j : Int) 0 = (code W).testBit j := by
  simp [D,rightDiag,Rule30Realization.evol,seed]

theorem code_low (W : Nat) :
    (code W).testBit 0 = true ∧ (code W).testBit 1 = false ∧
    (code W).testBit 2 = true := by
  simp [code,Nat.testBit_or,Nat.testBit_shiftLeft,
    show (5:Nat).testBit 1=false by decide +kernel,
    show (5:Nat).testBit 2=true by decide +kernel]

theorem code_high (W i : Nat) : (code W).testBit (i+3) = W.testBit i := by
  have hi : (5:Nat).testBit (i+3)=false :=
    Rule30ZeroBoundarySmall.testBit_ge_of_lt (by decide +kernel : 5 < 2^3) (by omega)
  simp [code,Nat.testBit_or,Nat.testBit_shiftLeft,hi]

theorem D_white (W t : Nat) (j : Int) (hj : j < 0) : D W j t = false := by
  exact right_white (seed W) 0 (seed_right W) t j (by simpa using hj)

theorem D_step (W : Nat) (j : Int) (t : Nat) :
    D W j (t+1) = xor (D W j t) (D W (j-1) t || D W (j-2) t) :=
  rightDiag_step (seed W) j t

theorem D_zero (W t : Nat) : D W 0 t = true := by
  induction t with
  | zero => exact (D_init W 0).trans (code_low W).1
  | succ t ih =>
    rw [D_step, D_white W t (0-1) (by omega), D_white W t (0-2) (by omega),ih]
    rfl

theorem phase_next (t : Nat) : phase (t+1) = !phase t := by
  unfold phase
  have h := Nat.mod_two_eq_zero_or_one t
  rcases h with h | h <;> simp [Nat.add_mod,h]

theorem anchors (W t : Nat) : D W 1 t = phase t ∧ D W 2 t = !phase t := by
  induction t with
  | zero =>
    constructor
    · exact (D_init W 1).trans (code_low W).2.1
    · exact (D_init W 2).trans (code_low W).2.2
  | succ t ih =>
    rw [D_step,D_step,show (1:Int)-1=0 by omega,show (1:Int)-2= -1 by omega,
      show (2:Int)-1=1 by omega,show (2:Int)-2=0 by omega,D_zero,
      D_white W t (-1) (by omega),ih.1,ih.2,phase_next]
    cases phase t <;> decide +kernel

theorem orb_phase (K W p t : Nat) (hp : p<2) :
    (orb K t (W,p)).2 = (p+t)%2 := by
  induction t with
  | zero => simp [orb,Nat.mod_eq_of_lt hp]
  | succ t ih =>
    simp only [orb,fS,ih]
    have h := Nat.mod_two_eq_zero_or_one (p+t)
    rcases h with h | h <;> omega

theorem orb_bit (K W t : Nat) : ∀ i, i<K →
    (orb K t (W,0)).1.testBit i = D W ((i+3:Nat):Int) t := by
  induction t with
  | zero =>
    intro i _
    simp only [orb,D_init,code_high]
  | succ t ih =>
    intro i hi
    have hp : (orb K t (W,0)).2<2 := by rw [orb_phase K W 0 t (by omega)]; omega
    have hz : decide ((orb K t (W,0)).2=0) = !phase t := by
      rw [orb_phase K W 0 t (by omega)]
      have h := Nat.mod_two_eq_zero_or_one t
      rcases h with h | h <;> simp [phase,h]
    have ho : decide ((orb K t (W,0)).2=1) = phase t := by
      simp [orb_phase,phase]
    have ha : (if i=0 then decide ((orb K t (W,0)).2=0)
      else (orb K t (W,0)).1.testBit (i-1)) = D W (((i+3:Nat):Int)-1) t := by
      by_cases h0 : i=0
      · subst i
        simpa [hz] using (anchors W t).2.symm
      · rw [ite_eq_right h0,ih (i-1) (by omega)]
        congr 1
        omega
    have hb : (if i=0 then decide ((orb K t (W,0)).2=1)
      else if i=1 then decide ((orb K t (W,0)).2=0)
      else (orb K t (W,0)).1.testBit (i-2)) = D W (((i+3:Nat):Int)-2) t := by
      by_cases h0 : i=0
      · subst i
        simpa [ho] using (anchors W t).1.symm
      · rw [ite_eq_right h0]
        by_cases h1 : i=1
        · subst i
          simpa [hz] using (anchors W t).2.symm
        · rw [ite_eq_right h1,ih (i-2) (by omega)]
          congr 1
          omega
    simp only [orb,fS]
    rw [testBit_fstep K _ _ i hp,show decide (i<K)=true from decide_eq_true hi,
      Bool.true_and,ih i hi,ha,hb,D_step]

theorem B_pos (K : Nat) : 1 ≤ B (K+2) := by
  unfold B
  omega

theorem half_period_even (K : Nat) : 2^B (K+2)%2=0 := by
  obtain ⟨e,he⟩ : ∃e,B (K+2)=e+1 := ⟨B (K+2)-1,by have := B_pos K;omega⟩
  rw [he,Nat.pow_succ]
  omega

/-- Universal front return from phase zero. This concerns a finite front window,
not extinction of its accompanying infinite stripe tail. -/
theorem front_half_period_zero (K W : Nat) (hW : W<2^K) :
    orb K (2^B (K+2)) (W,0) = (W,0) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i<K
    · rw [orb_bit K W _ i hi]
      have h := right_bounded_prefix_half (seed W) 0 (seed_right W) (K+2)
        ((i+3:Nat):Int) (by omega) 0
      rw [Nat.zero_add] at h
      change D W ((i+3:Nat):Int) (2^B (K+2)) = D W ((i+3:Nat):Int) 0 at h
      rw [D_init,code_high] at h
      exact h
    · have a := orbit_bound (p:=0) hW (2^B (K+2))
      rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt a (by omega),
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)]
  · rw [orb_phase K W 0 _ (by omega)]
    simpa only [Nat.zero_add] using half_period_even K

/-- A return persists along an orbit. This is the elementary orbit identity
also used in the stripe-structure contribution (PR45). -/
theorem return_shift {K P t : Nat} {s : Nat × Nat} (h : orb K P s=s) :
    orb K P (orb K t s)=orb K t s := by
  rw [← orb_add, Nat.add_comm t P,orb_add,h]

/-- Every bounded front state, in either phase, returns by the half-rate clock.
The exponent uses three extra anchor diagonals; for small widths the older
2^K universal return may be smaller. -/
theorem front_half_period (K W p : Nat) (hW : W<2^K) (hp : p<2) :
    orb K (2^B (K+2)) (W,p) = (W,p) := by
  by_cases hk : K=0
  · subst K
    have hw : W=0 := by simpa using hW
    subst W
    apply Prod.ext
    · have h := orbit_bound (K:=0) (a:=0) (p:=p) (by decide +kernel) (2^B 2)
      simpa using h
    · rw [orb_phase 0 0 p _ hp,Nat.add_mod,half_period_even 0,Nat.add_zero,
        Nat.mod_eq_of_lt hp]
      exact Nat.mod_eq_of_lt hp
  · rcases (show p=0 ∨ p=1 by omega) with rfl | rfl
    · exact front_half_period_zero K W hW
    · have kpos : 0<K := by omega
      have kp : K-1+1=K := by omega
      have old := universal_front_period (K-1) W 1 (by simpa only [kp] using hW) (by omega)
      rw [kp] at old
      let q := 2^K
      have qpos : 0<q := Nat.two_pow_pos K
      have qeven : q%2=0 := by
        dsimp [q]
        rw [← kp,Nat.pow_succ]
        omega
      let v := orb K (q-1) (W,1)
      have vp : v.2=0 := by
        dsimp [v]
        rw [orb_phase K W 1 (q-1) (by omega)]
        have hq : 1+(q-1)=q := by omega
        rw [hq,qeven]
      have vw : v.1<2^K := orbit_bound (p:=1) hW (q-1)
      have veq : v=(v.1,0) := Prod.ext rfl vp
      have vret : orb K (2^B (K+2)) v=v := by
        rw [veq]
        exact front_half_period_zero K v.1 vw
      have next : orb K 1 v=(W,1) := by
        dsimp [v]
        rw [← orb_add,show q-1+1=q by omega]
        exact old
      have h := return_shift (t:=1) vret
      rw [next] at h
      exact h

end Ruliology.CellularAutomata.Rule30FrontHalfPeriod
