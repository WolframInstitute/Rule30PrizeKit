module
public import Ruliology.CellularAutomata.Rule30GatePastCover

/-! Conditional reduction from arbitrary finite-past closing to absence of
finite gate rows. The closing hypothesis is not proved here. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GateTailReduction
open Rule30ZeroBoundary Rule30PastStrip Rule30GatePastCover
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def EventuallyEq (f g : Nat → Bool) : Prop := ∃ N, ∀ r, N ≤ r → f r=g r
def HomoclinicClosing : Prop := ∀ G H : Nat → Bool,
  GateLegal G → GateLegal H → EventuallyEq G H →
  EventuallyEq (lam (oddTrace G)) (lam (oddTrace H))
def AllPastClosing : Prop := ∀ n : Nat, ∀ G : Nat → Bool, ∀ p q : Fin (2^n),
  GateLegal G → GateLegal (prependN n p G) → GateLegal (prependN n q G) →
  EventuallyEq (lam (oddTrace (prependN n p G))) (lam (oddTrace (prependN n q G)))

def code (G : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => 2^n*bitNat (G n)+code G n

theorem code_bound (G : Nat → Bool) : ∀ n, code G n < 2^n := by
  intro n
  induction n with
  | zero => change 0<1; decide
  | succ n ih =>
      rw [code,Nat.pow_succ]
      cases G n <;> simp [bitNat] <;> omega

theorem code_bits (G : Nat → Bool) : ∀ n i, i < n → Nat.testBit (code G n) i = G i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      rw [code,Nat.testBit_two_pow_mul_add _ (code_bound G n)]
      by_cases h : i < n
      · rw [ite_eq_left h]
        exact ih i h
      · rw [ite_eq_right h]
        have eq : i=n := by omega
        subst i
        simp only [Nat.sub_self]
        cases hb : G n <;> rfl

theorem gate_shift_legal (G : Nat → Bool) (hg : GateLegal G) (n : Nat) :
    GateLegal (fun r => G (n+r)) := by
  intro r
  have eq : window (fun s => G (n+s)) r = window G (n+r) := by
    apply window_congr
    intro j hj
    rw [Nat.add_assoc]
  rw [eq]
  exact hg (n+r)

theorem homoclinic_of_all_pasts (closing : AllPastClosing) : HomoclinicClosing := by
  intro G H hg hh htail
  obtain ⟨N,htail⟩ := htail
  let p : Fin (2^N) := ⟨code G N,code_bound G N⟩
  let q : Fin (2^N) := ⟨code H N,code_bound H N⟩
  let future := fun r => G (N+r)
  have gp : prependN N p future = G := by
    funext r
    unfold prependN
    by_cases hr : r < N
    · rw [ite_eq_left hr]
      exact code_bits G N r hr
    · rw [ite_eq_right hr]
      dsimp [future]
      congr 1
      omega
  have hq : prependN N q future = H := by
    funext r
    unfold prependN
    by_cases hr : r < N
    · rw [ite_eq_left hr]
      exact code_bits H N r hr
    · rw [ite_eq_right hr]
      dsimp [future]
      rw [show N+(r-N)=r by omega]
      exact htail r (by omega)
  have hc := closing N future p q (gate_shift_legal G hg N)
    (by rw [gp]; exact hg) (by rw [hq]; exact hh)
  simpa only [gp,hq] using hc

theorem all_pasts_of_homoclinic (closing : HomoclinicClosing) : AllPastClosing := by
  intro n G p q hg hp hq
  apply closing _ _ hp hq
  refine ⟨n,?_⟩
  intro r hr
  unfold prependN
  rw [ite_eq_right (by omega),ite_eq_right (by omega)]

theorem closing_equivalence : HomoclinicClosing ↔ AllPastClosing :=
  ⟨all_pasts_of_homoclinic,homoclinic_of_all_pasts⟩

theorem last_black_nonzero (L : Nat → Bool) (hnz : ∃ k, 1≤k ∧ L k=true) :
    ∀ W, (∀ k, W<k → L k=false) →
      ∃ m, 1≤m ∧ L m=true ∧ ∀ k, m<k → L k=false := by
  intro W
  induction W with
  | zero =>
      intro hz
      obtain ⟨k,hk,hb⟩ := hnz
      have := hz k (by omega)
      rw [hb] at this
      contradiction
  | succ W ih =>
      intro hz
      cases hw : L (W+1)
      · apply ih
        intro k hk
        by_cases h : W+1<k
        · exact hz k h
        · have eq : k=W+1 := by omega
          rw [eq]
          exact hw
      · exact ⟨W+1,by omega,hw,fun k hk => hz k hk⟩

/-- A finite row sharing a temporal boundary future with a width-W row also
has width at most W. This uses actual equal future rows and exact edge growth. -/
theorem support_bound_of_common_future (A B : Nat → Bool) (W T : Nat)
    (ha : ∀ k, W<k → A k=false) (hb : FinSupp B)
    (trace : ∀ t, T≤t → zrow A t 1 = zrow B t 1) :
    ∀ k, W<k → B k=false := by
  intro k hk
  cases hbk : B k
  · rfl
  · exfalso
    obtain ⟨WB,hWB⟩ := hb
    obtain ⟨m,hm,hedge,hwhite⟩ := last_black_nonzero B ⟨k,by omega,hbk⟩ WB hWB
    have hkm : k≤m := by
      by_cases h : k≤m
      · exact h
      · have := hwhite k (by omega)
        rw [hbk] at this
        contradiction
    have black := (zrow_edge hm hedge hwhite T).1
    have white := zrow_fin ha T (m+T) (by omega)
    have eq := zrow_det A B (m+T) T (fun i _ => trace (T+i) (by omega))
    rw [white,black] at eq
    contradiction

def periodicGate (r : Nat) : Bool := decide (r%5=0)
theorem periodic_gate_period (r : Nat) : periodicGate (r+5)=periodicGate r := by
  unfold periodicGate
  have h : (r+5)%5=r%5 := by omega
  rw [h]

def PeriodicSplicing : Prop := ∀ G : Nat → Bool, GateLegal G → ∀ K : Nat,
  ∃ H : Nat → Bool, GateLegal H ∧ EventuallyEq G H ∧ ∀ r, r<K → H r=periodicGate r

theorem periodic_prefix_clock (H : Nat → Bool) (K : Nat)
    (pref : ∀ r, r<K → H r=periodicGate r) :
    ∀ t, t+10 < 2*K → oddTrace H (t+10)=oddTrace H t := by
  intro t ht
  unfold oddTrace
  rw [show (t+10)%2=t%2 by omega]
  by_cases he : t%2=0
  · rw [ite_eq_left he,ite_eq_left he,pref ((t+10)/2) (by omega),pref (t/2) (by omega)]
    rw [show (t+10)/2=t/2+5 by omega,periodic_gate_period]
  · rw [ite_eq_right he,ite_eq_right he]

/-- This is conditional on both named hypotheses. The splicing hypothesis
will be discharged by a finite overlap-graph certificate; closing stays open. -/
theorem gate_rows_infinite_of_closing_and_splicing
    (closing : HomoclinicClosing) (splice : PeriodicSplicing) :
    ∀ G : Nat → Bool, GateLegal G → ¬ FinSupp (lam (oddTrace G)) := by
  intro G hg hfinite
  obtain ⟨W,hW⟩ := hfinite
  let K := W+20
  obtain ⟨H,hh,hevent,hprefix⟩ := splice G hg K
  obtain ⟨N,hN⟩ := hevent
  obtain ⟨M,hM⟩ := closing G H hg hh ⟨N,hN⟩
  have finiteH : FinSupp (lam (oddTrace H)) := by
    refine ⟨max W M,?_⟩
    intro k hk
    rw [← hM k (by omega)]
    exact hW k (by omega)
  have boundary : ∀ t, 2*N≤t →
      zrow (lam (oddTrace G)) t 1 = zrow (lam (oddTrace H)) t 1 := by
    intro t ht
    rw [(realization (oddTrace G)).1 t,(realization (oddTrace H)).1 t]
    unfold oddTrace
    by_cases he : t%2=0
    · rw [ite_eq_left he,ite_eq_left he,hN (t/2) (by omega)]
    · rw [ite_eq_right he,ite_eq_right he]
  have hbound := support_bound_of_common_future _ _ W (2*N) hW finiteH boundary
  have hzero : H 0=true := by
    rw [hprefix 0 (by dsimp [K]; omega)]
    rfl
  have htwo : lam (oddTrace H) 2=true := by
    change xor (oddTrace H 1) (oddTrace H 0 || false)=true
    simp [oddTrace,hzero]
  obtain ⟨m,hm,hblack,hwhite⟩ := last_black_nonzero _ ⟨2,by omega,htwo⟩ W hbound
  have hmW : m≤W := by
    by_cases h : m≤W
    · exact h
    · have := hbound m (by omega)
      rw [hblack] at this
      contradiction
  have clock := jen_clock hm hblack hwhite (T:=0) (ℓ:=2*K-1) (P:=10) (by decide)
    (fun t _ ht => by
      rw [(realization (oddTrace H)).1 (t+10),(realization (oddTrace H)).1 t]
      exact periodic_prefix_clock H K hprefix t (by dsimp [K] at *; omega))
  dsimp [K] at clock
  omega

def Successor (a b : Nat) : Prop := (a >>> 1) = (b &&& 127)
instance successorDecidable (a b : Nat) : Decidable (Successor a b) := by
  unfold Successor
  infer_instance

def pack8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Nat :=
  bitNat b0+2*bitNat b1+4*bitNat b2+8*bitNat b3+
  16*bitNat b4+32*bitNat b5+64*bitNat b6+128*bitNat b7

private theorem overlap_certificate : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    Successor (pack8 b0 b1 b2 b3 b4 b5 b6 b7) (pack8 b1 b2 b3 b4 b5 b6 b7 b8) := by
  decide +kernel

theorem window_successor (G : Nat → Bool) (r : Nat) :
    Successor (window G r) (window G (r+1)) := by
  have h := overlap_certificate (G r) (G (r+1)) (G (r+2)) (G (r+3)) (G (r+4))
    (G (r+5)) (G (r+6)) (G (r+7)) (G (r+8))
  simpa [window,pack8,Nat.add_assoc] using h

private theorem mask_bits : ∀ j : Fin 7, Nat.testBit 127 j = true := by decide +kernel
theorem successor_bits (a b : Nat) (h : Successor a b) (j : Fin 7) :
    Nat.testBit b j = Nat.testBit a (j.val+1) := by
  have eq := congrArg (fun v => Nat.testBit v j) h
  simp only [Nat.testBit_shiftRight,Nat.testBit_and,mask_bits j,Bool.and_true] at eq
  simpa only [Nat.add_comm] using eq.symm

theorem stream_bits (W : Nat → Nat) (hs : ∀ r, Successor (W r) (W (r+1))) :
    ∀ j, j<8 → ∀ r, Nat.testBit (W (r+j)) 0 = Nat.testBit (W r) j := by
  intro j
  induction j with
  | zero => intro hj r; rfl
  | succ j ih =>
      intro hj r
      have one := ih (by omega) (r+1)
      have two := successor_bits (W r) (W (r+1)) (hs r) ⟨j,by omega⟩
      rw [show r+1+j=r+(j+1) by omega] at one
      exact one.trans two

private theorem recode_certificate : ∀ w ∈ words,
    pack8 (Nat.testBit w 0) (Nat.testBit w 1) (Nat.testBit w 2) (Nat.testBit w 3)
      (Nat.testBit w 4) (Nat.testBit w 5) (Nat.testBit w 6) (Nat.testBit w 7) = w := by
  decide +kernel

theorem stream_gate_legal (W : Nat → Nat) (hm : ∀ r, W r ∈ words)
    (hs : ∀ r, Successor (W r) (W (r+1))) :
    GateLegal (fun r => Nat.testBit (W r) 0) := by
  intro r
  have eq : window (fun r => Nat.testBit (W r) 0) r = W r := by
    change pack8 (Nat.testBit (W r) 0) (Nat.testBit (W (r+1)) 0)
      (Nat.testBit (W (r+2)) 0) (Nat.testBit (W (r+3)) 0)
      (Nat.testBit (W (r+4)) 0) (Nat.testBit (W (r+5)) 0)
      (Nat.testBit (W (r+6)) 0) (Nat.testBit (W (r+7)) 0) = W r
    rw [stream_bits W hs 1 (by omega) r,stream_bits W hs 2 (by omega) r,
      stream_bits W hs 3 (by omega) r,stream_bits W hs 4 (by omega) r,
      stream_bits W hs 5 (by omega) r,stream_bits W hs 6 (by omega) r,stream_bits W hs 7 (by omega) r]
    exact recode_certificate (W r) (hm r)
  rw [eq]
  exact hm r

def pattern (i : Fin 10) : Nat := words[i.val]?.getD 0
private theorem pattern_coverage : ∀ w ∈ words, ∃ i : Fin 10, pattern i=w := by decide +kernel
def bridgeLength : Nat := 40
def paths : List (List Nat) := [[8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8], [8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9], [8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16], [8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18], [8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33], [8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36], [8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66], [8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72], [8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132], [8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144], [9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8], [9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9], [9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16], [9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18], [9, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33], [9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36], [9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66], [9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72], [9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132], [9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16, 8], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16], [16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132], [16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16, 8], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16], [18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132], [18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16, 8], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33], [33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132], [33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16, 8], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33], [36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132], [36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144], [66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16, 8], [66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9], [66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16], [66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18], [66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33], [66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36], [66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66], [66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72], [66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132], [66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144], [72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16, 8], [72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9], [72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16], [72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18], [72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33], [72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36], [72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66], [72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72], [72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132], [72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144], [132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16, 8], [132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9], [132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16], [132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18], [132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33], [132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36], [132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66], [132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72], [132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132], [132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144], [144, 72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16, 8], [144, 72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9], [144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 16], [144, 72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18], [144, 72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33], [144, 72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36], [144, 72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66], [144, 72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72], [144, 72, 36, 18, 9, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132, 66, 33, 16, 8, 132], [144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144, 72, 36, 18, 9, 132, 66, 33, 144]]
def bridge (a b : Fin 10) (r : Nat) : Nat :=
  ((paths[10*a.val+b.val]?.getD [])[r]?.getD 0)

private theorem bridges_valid : ∀ a b : Fin 10,
    bridge a b 0=pattern a ∧ bridge a b bridgeLength=pattern b ∧
    (∀ r : Fin (bridgeLength+1), bridge a b r ∈ words) ∧
    (∀ r : Fin bridgeLength, Successor (bridge a b r) (bridge a b (r.val+1))) := by
  decide +kernel

private theorem periodic_windows : ∀ r : Fin 5, window periodicGate r ∈ words := by decide +kernel
theorem periodic_gate_legal : GateLegal periodicGate := by
  intro r
  have eq : window periodicGate r = window periodicGate (r%5) := by
    apply window_congr
    intro j hj
    unfold periodicGate
    have h : (r+j)%5=(r%5+j)%5 := by omega
    rw [h]
  rw [eq]
  exact periodic_windows ⟨r%5,by omega⟩

theorem periodic_splicing : PeriodicSplicing := by
  intro G hg K
  let N := K+bridgeLength
  have hL : 0<bridgeLength := by decide
  obtain ⟨a,ha⟩ := pattern_coverage (window periodicGate K) (periodic_gate_legal K)
  obtain ⟨b,hb⟩ := pattern_coverage (window G N) (hg N)
  obtain ⟨first,last,members,edges⟩ := bridges_valid a b
  have first' : bridge a b 0=window periodicGate K := first.trans ha
  have last' : bridge a b bridgeLength=window G N := last.trans hb
  let W := fun r => if r<K then window periodicGate r
    else if r<N then bridge a b (r-K) else window G r
  have onP : ∀ r, r≤K → W r=window periodicGate r := by
    intro r hr
    by_cases h : r<K
    · dsimp only [W]
      rw [ite_eq_left h]
    · have eq : r=K := by omega
      subst r
      dsimp only [W]
      rw [ite_eq_right (by omega),ite_eq_left (by dsimp [N]; omega),Nat.sub_self]
      exact first'
  have onB : ∀ r, K≤r → r≤N → W r=bridge a b (r-K) := by
    intro r hr hn
    by_cases h : r<N
    · dsimp only [W]
      rw [ite_eq_right (by omega),ite_eq_left h]
    · have eq : r=N := by omega
      subst r
      dsimp only [W]
      rw [ite_eq_right (by dsimp [N]; omega),ite_eq_right (by omega)]
      rw [show N-K=bridgeLength by dsimp [N]; omega]
      exact last'.symm
  have onG : ∀ r, N≤r → W r=window G r := by
    intro r hr
    dsimp only [W]
    rw [ite_eq_right (by dsimp [N] at *; omega),ite_eq_right (by omega)]
  have wm : ∀ r, W r ∈ words := by
    intro r
    by_cases hp : r≤K
    · rw [onP r hp]
      exact periodic_gate_legal r
    · by_cases hn : r≤N
      · rw [onB r (by omega) hn]
        exact members ⟨r-K,by dsimp [N] at hn; omega⟩
      · rw [onG r (by omega)]
        exact hg r
  have ws : ∀ r, Successor (W r) (W (r+1)) := by
    intro r
    by_cases hp : r<K
    · rw [onP r (by omega),onP (r+1) (by omega)]
      exact window_successor periodicGate r
    · by_cases hn : r<N
      · rw [onB r (by omega) (by omega),onB (r+1) (by omega) (by omega)]
        have hidx : r+1-K=(r-K)+1 := by omega
        rw [hidx]
        exact edges ⟨r-K,by dsimp [N] at hn; omega⟩
      · rw [onG r (by omega),onG (r+1) (by omega)]
        exact window_successor G r
  let H := fun r => Nat.testBit (W r) 0
  refine ⟨H,stream_gate_legal W wm ws,⟨N,?_⟩,?_⟩
  · intro r hr
    dsimp only [H]
    rw [onG r hr]
    exact (window_bits G r ⟨0,by decide⟩).symm
  · intro r hr
    dsimp only [H]
    rw [onP r (by omega)]
    exact window_bits periodicGate r ⟨0,by decide⟩

/-- The sole remaining hypothesis here is the unproved arbitrary-length
closing claim. The gate splicing and exact-width bridge are proved. -/
theorem gate_rows_infinite_of_all_past_closing (closing : AllPastClosing) :
    ∀ G : Nat → Bool, GateLegal G → ¬ FinSupp (lam (oddTrace G)) :=
  gate_rows_infinite_of_closing_and_splicing (homoclinic_of_all_pasts closing) periodic_splicing

def FiniteCoverFamily : Prop := ∀ n : Nat, ∃ trees : Nat → CoverTree,
  ∀ w ∈ words, checkTree n 8 w (trees w)=true

theorem all_pasts_of_finite_covers (covers : FiniteCoverFamily) : AllPastClosing := by
  intro n G p q hg hp hq
  obtain ⟨trees,checks⟩ := covers n
  let B := bound (trees 8)+bound (trees 9)+bound (trees 16)+bound (trees 18)+bound (trees 33)+
    bound (trees 36)+bound (trees 66)+bound (trees 72)+bound (trees 132)+bound (trees 144)
  have bounds : ∀ w ∈ words, bound (trees w)≤B := by
    intro w hw
    have hcases : w=8 ∨ w=9 ∨ w=16 ∨ w=18 ∨ w=33 ∨ w=36 ∨ w=66 ∨ w=72 ∨ w=132 ∨ w=144 := by
      simpa [words] using hw
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [B] <;> omega
  exact ⟨B,root_cover n B trees checks bounds G p q hg hp hq⟩

/-- A proof-producing search that supplies finite checked covers for every n
would suffice. No such unbounded family is supplied by the finite examples. -/
theorem gate_rows_infinite_of_finite_covers (covers : FiniteCoverFamily) :
    ∀ G : Nat → Bool, GateLegal G → ¬ FinSupp (lam (oddTrace G)) :=
  gate_rows_infinite_of_all_past_closing (all_pasts_of_finite_covers covers)

end Ruliology.CellularAutomata.Rule30GateTailReduction
