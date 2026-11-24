module

public import Ruliology.CellularAutomata.Rule30PulsePairs
public import Ruliology.CellularAutomata.Rule30PairedColumnRuns
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers

/-!
# Initial left mass for periodic paired-pulse clocks

Three completed blocks synchronize the masked readout. A pure period P
contains each complete block in at most P ticks. Apply the paired-column
white-run bound starting at time 3P+2 and pull the white triangle back
to row zero. Every interval of 8P+3 initial cells at depths at least two
then contains a black cell, uniformly over the prescribed right half.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30PulsePairSupport
open Rule30PulsePairs Rule30Realization Rule30FiniteConfigs Rule30PairedColumnRuns

private def count (q : Fin 84) := min 6 (2*(q.val/21)+(decide (18≤q.val%21)).toNat)
private theorem step_count : ∀ (q : Fin 84) (b : Bool), legal q b=true →
    count (move q b)=min 6 (count q + b.toNat) := by decide +kernel
private theorem saturated : ∀ q, count q=6 → 63≤q.val := by decide +kernel
private theorem bounded : ∀ q, count q≤6 := by decide +kernel

private theorem capture_by {c : Nat → Bool} {P : Nat} (pos : 0<P)
    (tiles : Tiled c) (per : ∀ t, c (t+P)=c t) :
    ∀ u, 3*P≤u → 63≤(cursor c u).val := by
  have legalC := follows_of_tiled tiles
  obtain ⟨a,start,blocks⟩ := tiles
  let v := fun t => count (cursor c t)
  have step (t : Nat) : v (t+1)=min 6 (v t+(c t).toNat) := step_count _ _ (legalC t)
  have mono (s t : Nat) (h : s≤t) : v s≤v t := by
    have more (k : Nat) : v s≤v (s+k) := by
      induction k with
      | zero => exact Nat.le_refl _
      | succ k ih =>
        have eq := step (s+k)
        have le : v (s+k)≤6 := bounded _
        rw [show s+(k+1)=s+k+1 by omega,eq]
        omega
    simpa only [show s+(t-s)=t by omega] using more (t-s)
  have lengthBound (n : Nat) : a (n+1)≤a n+P := by
    obtain ⟨r,hr,last,word⟩ := blocks n
    by_cases short : P≤r
    · have e := per (a n+(r-P))
      rw [show a n+(r-P)+P=a n+r by omega,word r (by omega),word (r-P) (by omega)] at e
      simp [show r-P≠r by omega,show r-P≠r+3 by omega] at e
    · by_cases enough : r+4≤P
      · omega
      · have e := per (a n+(r+3-P))
        rw [show a n+(r+3-P)+P=a n+(r+3) by omega,word (r+3) (by omega),
          word (r+3-P) (by omega)] at e
        simp [show r+3-P≠r by omega,show r+3-P≠r+3 by omega] at e
  have byTime (n : Nat) : a n≤n*P := by
    induction n with
    | zero => simp [start]
    | succ n ih => have h := lengthBound n; rw [Nat.succ_mul]; omega
  have gain (n : Nat) : min 6 (2*n)≤v (a n) := by
    induction n with
    | zero => omega
    | succ n ih =>
      obtain ⟨r,_,endAt,word⟩ := blocks n
      have black (k : Nat) (hk : k=r ∨ k=r+3) : c (a n+k)=true :=
        (word k (by omega)).trans (decide_eq_true hk)
      have m := mono (a n) (a n+r) (by omega)
      have p := step (a n+r)
      rw [black r (Or.inl rfl)] at p
      have m' := mono (a n+r+1) (a n+(r+3)) (by omega)
      have p' := step (a n+(r+3))
      rw [black _ (Or.inr rfl),show a n+(r+3)+1=a (n+1) by omega] at p'
      simp only [Bool.toNat_true] at p p'
      omega
  intro u hu
  have h := gain 3
  have m := mono (a 3) u (Nat.le_trans (byTime 3) hu)
  exact saturated _ (by have le : v u≤6 := bounded _; change v u=6; omega)

/-- Pull the existing paired-column bound back through any common transient.
The depth is measured from the original center at position zero. -/
theorem initial_gap {x : Int → Bool} {A P : Nat} (hp : 2≤P)
    (left : ∀ t, A≤t → evol x (t+P) (-1)=evol x t (-1))
    (center : ∀ t, A≤t → evol x (t+P) 0=evol x t 0)
    (nonzero : ∃ t, A≤t ∧ evol x t (-1)=true)
    (d len : Nat) (depth : 2≤d)
    (white : ∀ k, d≤k → k<d+len → x (-(k:Int))=false) : len≤2*A+2*P-2 := by
  let y := shiftConfig (fun p => evol x A p) (-1)
  have eq (t : Nat) (p : Int) : evol y t p=evol x (A+t) (p+(-1)) := by
    rw [show y=shiftConfig (fun p => evol x A p) (-1) from rfl,evol_shiftConfig,
      Rule30ZeroBoundaryBarriers.evol_restart]
  have p0 : PerAll y 0 P := by
    intro t; rw [eq,eq,show A+(t+P)=A+t+P by omega]; exact (left _ (by omega)).symm
  have p1 : PerAll y 1 P := by
    intro t; rw [eq,eq,show A+(t+P)=A+t+P by omega]; exact (center _ (by omega)).symm
  obtain ⟨t,ht,nz⟩ := nonzero
  have e := zero_run_le y P hp p0 p1 ⟨t-A,by rw [eq,show A+(t-A)=t by omega]; exact nz⟩
    (d+A-1) (len-2*A) (by omega) (by
      intro k lo hi
      change evol x A (-(k:Int)+(-1))=false
      rw [show -(k:Int)+(-1)=-((k+1:Nat):Int) by omega]
      exact triangle x d len white A (k+1) (by omega) (by omega))
  omega

/-- Positive initial mass, independent of the right half. The clock is
aligned at the beginning of a long gap and has period P from launch. -/
theorem forced_gap_bound (c : Nat → Bool) (R : Int → Bool) {P : Nat} (hp : 2≤P)
    (per : ∀ t, c (t+P)=c t) (tiles : Tiled c) (d len : Nat) (depth : 2≤d)
    (white : ∀ k, d≤k → k<d+len → conf R c (-(k:Int))=false) : len≤8*P+2 := by
  let x := conf R c
  have hit : ∀ t, evol x t 0=c t := (realize R c).2
  have eq : (fun k => evol x (0+k) 0)=c := funext fun k => by simpa using hit k
  have follow := follows_of_tiled tiles
  have late := capture_by (by omega) tiles per
  have pattern (k : Nat) (hk : 3*P≤k) (w : c (k+2)=false) :
      evol x (k+2) 1=(!c k && !c (k+1)) := by
    have e := readout_from x 0 0 (eq ▸ follow) (3*P) (eq ▸ late) k hk
    simpa [hit,w] using e
  let A := 3*P+2
  have same (t : Nat) (ht : A≤t) : evol x (t+P) (-1)=evol x t (-1) := by
    rw [show (-1:Int)=0-1 by decide,Rule30FiniteMaskedJen.evol_left',Rule30FiniteMaskedJen.evol_left',
      Rule30FiniteMaskedJen.orCol,Rule30FiniteMaskedJen.orCol]
    simp only [hit,show t+P+1=(t+1)+P by omega,per]
    cases w : c t with
    | true => simp
    | false =>
      have u := pattern (t-2) (by unfold A at ht; omega) (by rwa [show t-2+2=t by unfold A at ht; omega])
      have wp : c (t+P)=false := (per t).trans w
      have v := pattern (t-2+P) (by unfold A at ht; omega) (by rwa [show t-2+P+2=t+P by unfold A at ht; omega])
      rw [show t-2+2=t by unfold A at ht; omega] at u
      rw [show t-2+P+2=t+P by unfold A at ht; omega,show t-2+P+1=t-2+1+P by omega,per,per] at v
      simp only [Int.zero_add,Bool.false_or]
      rw [v,u]
  obtain ⟨a,_,blocks⟩ := tiles
  have lower (n : Nat) : n≤a n := by
    induction n with
    | zero => omega
    | succ n ih => obtain ⟨r,_,e,_⟩ := blocks n; omega
  obtain ⟨r,_,_,word⟩ := blocks A
  have b : c (a A+r)=true := (word _ (by omega)).trans (by simp)
  have w : c (a A+(r+1))=false := (word _ (by omega)).trans (by simp)
  have on : evol x (a A+r) (-1)=true := by
    rw [show (-1:Int)=0-1 by decide,Rule30FiniteMaskedJen.evol_left',Rule30FiniteMaskedJen.orCol]
    simp [hit,b,show a A+r+1=a A+(r+1) by omega,w]
  have h := initial_gap hp same (fun t _ => by rw [hit,hit,per])
    ⟨a A+r,by have := lower A; omega,on⟩ d len depth white
  unfold A at h
  omega

end Ruliology.CellularAutomata.Rule30PulsePairSupport
