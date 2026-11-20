module

public import Ruliology.CellularAutomata.Rule30RootedWhiteReturns
public import Ruliology.CellularAutomata.Rule30ThreePhaseReturn

/-! Least prefix clocks and unbounded resets in three successive phases of a pointed strip. -/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30RecurrentStrip
open Ruliology.CellularAutomata.Rule30AgedLeftDiagonals
open Ruliology.CellularAutomata.Rule30RootedWhiteReturns

def Clock (d : Nat → Column) (m p : Nat) := ∀ i, i ≤ m → PeriodFrom (d i) 0 p

private theorem divides_clock {d m p q} (hp : 0 < p) (h : Clock d m p)
    (least : ∀ r, 0 < r → Clock d m r → p ≤ r) (other : Clock d m q) : p ∣ q := by
  apply Nat.dvd_of_mod_eq_zero
  by_cases hz : q%p = 0
  · exact hz
  have hr : Clock d m (q%p) := by
    intro i hi t ht
    have e := period_mul (h i hi) (q/p) (t + q%p) (by omega)
    have split : q%p + q/p*p = q := by simpa [Nat.mul_comm] using Nat.mod_add_div q p
    rw [Nat.add_assoc, split] at e
    exact e.symm.trans (other i hi t ht)
  have := least (q%p) (by omega) hr
  have := Nat.mod_lt q hp
  omega

/-- The least positive common period through each wheel is a power of two. -/
theorem dyadic_prefix_clock {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0 = true)
    (recurrent : ∀ i, ∃ q, 0 < q ∧ PeriodFrom (d i) 0 q) (m : Nat) :
    ∃ e, Clock d m (2^e) ∧ ∀ q, 0 < q → Clock d m q → 2^e ≤ q := by
  have edge (t : Nat) : d 0 t = true := by
    induction t with
    | zero => exact h0
    | succ t ih => exact (hd.1 t).trans ih
  have front (t : Nat) : d 1 t = true := by
    obtain ⟨q,hq,per⟩ := recurrent 1
    obtain ⟨u, hu⟩ : ∃ u, t+q=u+1 := ⟨t+q-1, by omega⟩
    rw [← per t (by omega), hu, hd.2.1, edge, Bool.true_or]
  induction m with
  | zero =>
    refine ⟨0, ?_, fun _ hq _ => hq⟩
    intro i hi t _
    have h : i=0 := by omega
    simp [h, edge]
  | succ m ih =>
    by_cases hm : m=0
    · subst m
      refine ⟨0, ?_, fun _ hq _ => hq⟩
      intro i hi t _
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [edge, front]
    obtain ⟨e, cp, least⟩ := ih
    let p := 2^e
    have hp : 0 < p := Nat.two_pow_pos _
    by_cases inherit : PeriodFrom (d (m+1)) 0 p
    · refine ⟨e, ?_, fun q hq cq => least q hq (fun i hi => cq i (by omega))⟩
      intro i hi
      by_cases h : i=m+1
      · exact h ▸ inherit
      · exact cp i (by omega)
    obtain ⟨j,hmj,_,cj,_,anti⟩ := first_clock_loss hd h0 recurrent hp (by omega : 1≤m) cp
    have hj : j=m := by
      by_cases hu : m+1≤j
      · exact (inherit (cj _ hu)).elim
      · omega
    subst j
    refine ⟨e+1, ?_, ?_⟩
    · intro i hi t ht
      change d i (t + 2^(e+1)) = d i t
      rw [Nat.pow_succ, ← show p = 2^e from rfl, show t+p*2=t+p+p by omega]
      by_cases last : i=m+1
      · simp [last, anti]
      · rw [cp i (by omega) (t+p) (by omega), cp i (by omega) t ht]
    · intro q hq cq
      have dq := divides_clock hp cp least (fun i hi => cq i (by omega))
      obtain ⟨k,hk⟩ := dq
      have hne : q ≠ p := by
        rintro rfl
        exact inherit (cq _ (by omega))
      have hk2 : 2 ≤ k := by
        by_cases k0 : k=0
        · simp [k0] at hk; omega
        by_cases k1 : k=1
        · simp [k1] at hk; contradiction
        omega
      rw [Nat.pow_succ, hk]
      exact Nat.mul_le_mul_left p hk2

open Ruliology.CellularAutomata.Rule30ThreePhaseReturn

/-- A closed run at a single tick, including both white endpoints. -/
def Reset (r : Nat → Bool) (j n : Nat) : Prop :=
  n % 3 = 1 ∧ r j = false ∧ (∀ k, k < n → r (j+1+k) = true) ∧ r (j+1+n) = false

private def trailing (r : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i+1 => if r (i+1) then trailing r i + 1 else 0

private theorem trailing_spec (r : Nat → Bool) (hw : r 0 = false) (i : Nat) :
    ∃ j, j + trailing r i = i ∧ r j = false ∧
      ∀ k, k < trailing r i → r (j+1+k) = true := by
  induction i with
  | zero => exact ⟨0,rfl,hw,fun k h => by simp [trailing] at h⟩
  | succ i ih =>
    obtain ⟨j,hj,hz,hb⟩ := ih
    cases h : r (i+1) with
    | false => exact ⟨i+1,by simp [trailing,h],h,fun k hk => by simp [trailing,h] at hk⟩
    | true =>
      simp only [trailing,h, ↓reduceIte]
      refine ⟨j, by omega, hz, ?_⟩
      intro k hk
      by_cases lt : k < trailing r i
      · exact hb k lt
      · rwa [show j+1+k=i+1 by omega]

private def pack (a b c : Bool) : C := BitVec.ofBool c ++ BitVec.ofBool b ++ BitVec.ofBool a
private def bits (f : Nat → Bool) := pack (f 0) (f 1) (f 2)

private theorem read_pack : ∀ a b c : Bool,
    (pack a b c).getLsbD 0 = a ∧ (pack a b c).getLsbD 1 = b ∧ (pack a b c).getLsbD 2 = c := by
  decide +kernel

private theorem read_bits (f : Nat → Bool) (i : Fin 3) : (bits f).getLsbD i.val = f i.val := by
  obtain ⟨a,b,c⟩ := read_pack (f 0) (f 1) (f 2)
  rcases (show i.val=0 ∨ i.val=1 ∨ i.val=2 by omega) with h|h|h <;> simp only [h,bits] <;> assumption

private theorem eq_bits : ∀ a b : C,
    (∀ i : Fin 3, a.getLsbD i.val = b.getLsbD i.val) → a = b := by decide +kernel

private theorem guard_clock : ∀ a b c : C,
    c.getLsbD 1 = xor (a.getLsbD 0) (b.getLsbD 0 || c.getLsbD 0) →
    c.getLsbD 2 = xor (a.getLsbD 1) (b.getLsbD 1 || c.getLsbD 1) →
    (c >>> 1) &&& 3 = (a ^^^ (b ||| c)) &&& 3 := by decide +kernel

private def col (r : Nat → Nat → Bool) (i : Nat) := bits (fun t => r t i)
private def mask (r : Nat → Nat → Bool) (i k : Nat) := bits (fun t => decide (trailing (r t) i % 3 = k))
private def state (r : Nat → Nat → Bool) (u : Nat) : State :=
  ⟨col r (u+1), col r (u+2), mask r (u+2) 1, mask r (u+2) 2⟩

private theorem state_start (r : Nat → Nat → Bool) (h : ∀ t, r t 2 = true) :
    state r 0 = start (col r 1) := by
  have startBits (t : Nat) : trailing (r t) 2 = (if r t 1 then 2 else 1) := by
    cases e : r t 1 <;> simp [trailing,h,e]
  simp only [state,start,State.mk.injEq,true_and]
  refine ⟨eq_bits _ _ (fun i => ?_), eq_bits _ _ (fun i => ?_), eq_bits _ _ (fun i => ?_)⟩
  · rw [col,read_bits,h]
    rcases (show i.val=0 ∨ i.val=1 ∨ i.val=2 by omega) with h|h|h <;> rw [h] <;> rfl
  · simp only [mask,col,read_bits,BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and, startBits]
    cases r i.val 1 <;> decide
  · simp only [mask,col,read_bits,startBits]
    cases r i.val 1 <;> decide

private theorem state_step (r : Nat → Nat → Bool) (hw : ∀ t, r t 0 = false)
    (law : ∀ t j, r (t+1) (j+2) = xor (r t j) (r t (j+1) || r t (j+2)))
    (safe : ∀ t, t < 3 → ∀ j n, ¬ Reset (r t) j n) (u : Nat) :
    step (state r u) (col r (u+3)) = some (state r (u+1)) := by
  have clk := guard_clock (col r (u+1)) (col r (u+2)) (col r (u+3))
  have bit (i k : Nat) (h : k<3) : (col r i).getLsbD k = r k i := read_bits _ ⟨k,h⟩
  have hclk := clk (by simpa only [bit _ _ (by decide : 0<3),bit _ _ (by decide : 1<3)] using law 0 (u+1))
    (by simpa only [bit _ _ (by decide : 1<3),bit _ _ (by decide : 2<3)] using law 1 (u+1))
  have hsafe (i : Fin 3) (ho : trailing (r i.val) (u+2) % 3 = 1) : r i.val (u+3) = true := by
    cases hc : r i.val (u+3) with
    | true => rfl
    | false =>
      obtain ⟨j,hj,hz,hb⟩ := trailing_spec _ (hw _) (u+2)
      exact (safe _ i.isLt j _ ⟨ho,hz,hb, by rwa [show j+1+trailing (r i.val) (u+2)=u+3 by omega]⟩).elim
  have noClose : mask r (u+2) 1 &&& ~~~(col r (u+3)) = 0 := by
    apply eq_bits
    intro i
    simp only [mask,col,BitVec.getLsbD_and,BitVec.getLsbD_not,read_bits,i.isLt,decide_true,Bool.true_and]
    by_cases ho : trailing (r i.val) (u+2)%3=1
    · simp [ho,hsafe i ho]
    · simp [ho]
  have extend (i : Fin 3) : trailing (r i.val) (u+3) =
      (if r i.val (u+3) then trailing (r i.val) (u+2) + 1 else 0) := rfl
  simp only [step,state,hclk,noClose]
  simp [State.mk.injEq,Nat.add_assoc]
  constructor <;> apply eq_bits <;> intro i <;>
    simp only [mask,col,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_or,read_bits,
      i.isLt,decide_true,Bool.true_and, extend] <;>
    cases r i.val (u+3) <;> simp <;> try omega
  by_cases h1 : trailing (r i.val) (u+2)%3=1 <;>
    by_cases h2 : trailing (r i.val) (u+2)%3=2 <;> simp [h1,h2] <;> omega

private def segment (f : Nat → C) (u : Nat) : Nat → List C
  | 0 => []
  | k+1 => f u :: segment f (u+1) k

private theorem scan_segment (r : Nat → Nat → Bool)
    (ok : ∀ u, step (state r u) (col r (u+3)) = some (state r (u+1))) (u k : Nat)
    (tail : List C) : scan (state r u) (segment (col r) (u+3) k ++ tail) =
      scan (state r (u+k)) tail := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    simp only [segment,List.cons_append,scan,ok,Option.bind_some]
    exact (ih (u+1)).trans (by rw [show u+1+k=u+(k+1) by omega])

private theorem beyond {d : Nat → Column} (hd : Recurrence d)
    (anchors : ∀ lo, ∃ j, lo≤j ∧ (∀ t, d j t=false) ∧ (∀ t, d (j+2) t=true)) (s lo : Nat) :
    ∃ t j n, t<3 ∧ lo≤j ∧ Reset (fun i => d i (s+t)) j n := by
  apply Classical.byContradiction
  intro missing
  obtain ⟨a,ha,white,black⟩ := anchors lo
  obtain ⟨b,hb,whiteB,_⟩ := anchors (a+3)
  let r := fun t i => d (a+i) (s+t)
  have hw (t) : r t 0=false := white _
  have hblack (t) : r t 2=true := black _
  have law (t j) : r (t+1) (j+2) = xor (r t j) (r t (j+1) || r t (j+2)) := by
    simpa [r,Nat.add_assoc] using hd.2.2 (a+j) (s+t)
  have safe (t) (ht : t<3) (j n) (hit : Reset (r t) j n) : False := by
    apply missing
    refine ⟨t,a+j,n,ht,by omega,?_⟩
    simpa [Reset,r,Nat.add_assoc] using hit
  have ok := state_step r hw law safe
  let k := b-(a+3)
  have hz : col r (k+3) = 0 := by
    apply eq_bits
    intro i
    have h : a+(k+3)=b := by dsimp [k]; omega
    rw [col,read_bits]
    simp [r,h,whiteB]
  have trap := three_phase_return (col r 1) (segment (col r) 3 k)
    (col r (k+4)) (col r (k+5)) (col r (k+6))
  rw [← state_start r hblack, ← hz, ← show 0+3=3 from rfl, scan_segment r ok, Nat.zero_add] at trap
  simp only [scan,ok,Option.bind_some] at trap
  contradiction

/-- One fixed member of any three successive ticks contains closed runs of
length one modulo three at arbitrarily great depths on the same strip. -/
theorem one_of_three_unbounded {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0=true)
    (clocks : ∀ m, ∃ p, 0<p ∧ Clock d m p) (s : Nat) :
    ∃ t, t<3 ∧ ∀ lo, ∃ j n, lo≤j ∧ Reset (fun i => d i (s+t)) j n := by
  classical
  apply Classical.byContradiction
  intro absent
  have cap (t) (ht : t<3) : ∃ lo, ∀ j n, lo≤j → ¬Reset (fun i => d i (s+t)) j n := by
    apply Classical.byContradiction
    intro h
    apply absent
    refine ⟨t,ht,fun lo => Classical.byContradiction fun hn => h ?_⟩
    exact ⟨lo, fun j n hj hr => hn ⟨j,n,hj,hr⟩⟩
  obtain ⟨a,ha⟩ := cap 0 (by decide)
  obtain ⟨b,hb⟩ := cap 1 (by decide)
  obtain ⟨c,hc⟩ := cap 2 (by decide)
  obtain ⟨t,j,n,ht,hj,h⟩ := beyond hd (unbounded_anchors hd h0 clocks) s (max a (max b c))
  rcases (show t=0 ∨ t=1 ∨ t=2 by omega) with rfl|rfl|rfl
  · exact ha j n (by omega) h
  · exact hb j n (by omega) h
  · exact hc j n (by omega) h

end Ruliology.CellularAutomata.Rule30RecurrentStrip
