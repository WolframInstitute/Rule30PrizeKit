module

public import Ruliology.CellularAutomata.Rule30MaskedJen

/-!
# Physical time-shift defects and bounded mismatch episodes

For the single-seed pattern, a hypothetical center period P from T gives a
uniform bound on uninterrupted 2P-shift mismatches in physical column one:
every 2P+1 readings after T+2P contain a zero mismatch. The proof retains the
actual time-shift relation and cancels two identical P-blocks of center forcing.

The module also identifies true mismatch births, derives the exact physical
recurrence, and counts at least one masked defect in each disjoint doubling
window. Padded doubling blocks contain distinct true births: for fixed
n0 >= T+2P and n0 >= 4P, their count before 4^m*n0 is at least 2m-1.
The count excludes the final source tick, so every resulting mismatch occurs
strictly before the horizon. Conditional Problem1 interfaces state fixed upper
budgets that would contradict these lower counts; neither upper budget is proved.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30PhysicalDefects
open Ruliology.CellularAutomata Rule30Jen Rule30Prize

def maskedDefect (Q t : Nat) : Bool :=
  !(cell t 0) && xor (cell t 1) (cell (t-Q) 1)

/-- The number of true values in the half-open interval `[lo,hi)`.
The count is zero when `hi ≤ lo`. -/
def intervalCount (p : Nat → Bool) (lo hi : Nat) : Nat :=
  (List.range' lo (hi-lo)).countP p

def defectCount (Q n0 X : Nat) : Nat := intervalCount (maskedDefect Q) n0 X

theorem intervalCount_split (p : Nat → Bool) {a b c : Nat}
    (hab : a≤b) (hbc : b≤c) :
    intervalCount p a c = intervalCount p a b + intervalCount p b c := by
  unfold intervalCount
  rw [show c-a=(b-a)+(c-b) by omega, ← List.range'_append_1, List.countP_append]
  rw [show a+(b-a)=b by omega]

theorem intervalCount_pos (p : Nat → Bool) {a b s : Nat}
    (has : a≤s) (hsb : s<b) (hp : p s=true) : 1≤intervalCount p a b := by
  apply List.one_le_countP_iff.mpr
  refine ⟨s, List.mem_range'.mpr ⟨s-a, by omega, ?_⟩, hp⟩
  omega

theorem periodic_multiple {T P Q : Nat}
    (hc : ∀ t, T≤t → cell (t+P) 0=cell t 0) (hPQ : P∣Q) :
    ∀ t, T≤t → cell (t+Q) 0=cell t 0 := by
  obtain ⟨k,rfl⟩ := hPQ
  induction k with
  | zero => simp
  | succ k ih =>
      intro t ht
      rw [Nat.mul_succ, ← Nat.add_assoc, hc _ (by omega), ih t ht]

theorem defect_window {T Q : Nat} (hQ : 0<Q)
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0)
    (n : Nat) (hn : T+Q≤n) : 1≤defectCount Q n (2*n) := by
  obtain ⟨s,hns,hsn,hw,hd⟩ := Rule30MaskedJen.periodic_window hQ hc n hn
  apply intervalCount_pos _ hns hsn
  unfold maskedDefect
  rw [hw]
  cases h1 : cell s 1 <;> cases h2 : cell (s-Q) 1 <;> simp_all

/-- One distinct masked defect per disjoint doubling window. -/
theorem doubling_lower {T Q n0 : Nat} (hQ : 0<Q)
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0) (hn0 : T+Q≤n0) (k : Nat) :
    k≤defectCount Q n0 (2^k*n0) := by
  induction k with
  | zero => simp [defectCount, intervalCount]
  | succ k ih =>
      have hp : n0≤2^k*n0 := by
        have hh := Nat.mul_le_mul_right n0 (Nat.one_le_pow k 2 (by decide))
        simpa using hh
      have hw := defect_window hQ hc (2^k*n0) (by omega)
      have he : 2^(k+1)*n0=2*(2^k*n0) := by
        simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
      rw [he]
      unfold defectCount at ih hw ⊢
      rw [intervalCount_split _ hp (by omega)]
      omega

/-- The exact base-four lower bound, including the empty interval at `m=0`. -/
theorem base_four_lower {T Q n0 : Nat} (hQ : 0<Q)
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0) (hn0 : T+Q≤n0) (m : Nat) :
    2*m≤defectCount Q n0 (4^m*n0) := by
  have h := doubling_lower hQ hc hn0 (2*m)
  simpa only [Nat.pow_mul, show (2:Nat)^2=4 by decide] using h

/-- A conditional interface to official Problem 1. The fixed upper budget is
the missing mathematical premise; this theorem does not establish that budget. -/
theorem problem1_of_fixed_budget
    (upper : ∀ T P : Nat, 0<P →
      (∀ t, T≤t → cell (t+P) 0=cell t 0) →
      ∃ Q n0 C M : Nat, 0<Q ∧ P∣Q ∧ T+Q≤n0 ∧
        ∀ m, M≤m → defectCount Q n0 (4^m*n0)≤C+m) : Problem1 := by
  rintro ⟨T,P,hP,hc⟩
  obtain ⟨Q,n0,C,M,hQ,hPQ,hn0,hu⟩ := upper T P hP hc
  have hq := periodic_multiple hc hPQ
  have lo := base_four_lower hQ hq hn0 (M+C+1)
  have hi := hu (M+C+1) (by omega)
  omega

def mismatch (Q t : Nat) : Bool := xor (cell t 1) (cell (t-Q) 1)
def persists (t : Nat) : Bool := !(cell t 2)
def forcing (Q t : Nat) : Bool :=
  !(cell (t-Q) 1) && xor (cell t 2) (cell (t-Q) 2)

theorem or_difference (r z ro zo : Bool) :
    xor (r || z) (ro || zo) =
      xor ((!z) && xor r ro) ((!ro) && xor z zo) := by
  cases r <;> cases z <;> cases ro <;> cases zo <;> rfl

/-- Literal physical mismatch recurrence. The local agreement premise is
enough; the following theorem obtains it from eventual center periodicity. -/
theorem mismatch_step {Q t : Nat} (hQt : Q≤t)
    (hc : cell t 0=cell (t-Q) 0) :
    mismatch Q (t+1)=xor (persists t && mismatch Q t) (forcing Q t) := by
  unfold mismatch persists forcing
  rw [show t+1-Q=(t-Q)+1 by omega]
  change xor (xor (cell t 0) (cell t 1 || cell t 2))
    (xor (cell (t-Q) 0) (cell (t-Q) 1 || cell (t-Q) 2)) = _
  rw [hc]
  have cancel (a b c : Bool) : xor (xor a b) (xor a c)=xor b c := by
    cases a <;> cases b <;> cases c <;> rfl
  rw [cancel, or_difference]

theorem periodic_mismatch_step {T Q : Nat}
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0)
    (t : Nat) (ht : T+Q≤t) :
    mismatch Q (t+1)=xor (persists t && mismatch Q t) (forcing Q t) := by
  apply mismatch_step (by omega)
  have hh := hc (t-Q) (by omega)
  simpa only [show t-Q+Q=t by omega] using hh

/-- On the valid time domain the masked defect is exactly a defect of the
effective OR boundary, not a defect of an unrelated moving observation. -/
theorem maskedDefect_eq_or_difference {T Q : Nat}
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0)
    (t : Nat) (ht : T+Q≤t) :
    maskedDefect Q t = xor (Rule30MaskedJen.orCol 0 t) (Rule30MaskedJen.orCol 0 (t-Q)) := by
  have he := hc (t-Q) (by omega)
  rw [show t-Q+Q=t by omega] at he
  unfold maskedDefect Rule30MaskedJen.orCol
  rw [he]
  simp only [Int.zero_add]
  cases cell (t-Q) 0 <;> cases cell t 1 <;> cases cell (t-Q) 1 <;> rfl


theorem xor_same_left (c a b : Bool) : xor (xor c a) (xor c b)=xor a b := by
  cases c <;> cases a <;> cases b <;> rfl

theorem or_of_live_defect (r z ro zo : Bool)
    (h0 : xor r ro=true) (h1 : xor (r || z) (ro || zo)=true) : (r || z)=r := by
  cases r <;> cases z <;> cases ro <;> cases zo <;> simp_all

/-- On an uninterrupted physical mismatch, the right bit is toggled only
by the shared center bit. The two histories are the same history Q apart. -/
theorem live_mismatch_step {T Q : Nat}
    (hc : ∀ s, T≤s → cell (s+Q) 0=cell s 0)
    (t : Nat) (ht : T+Q≤t)
    (h0 : mismatch Q t=true) (h1 : mismatch Q (t+1)=true) :
    cell (t+1) 1=xor (cell t 0) (cell t 1) := by
  have hs := periodic_mismatch_step hc t ht
  rw [h1] at hs
  change true=xor ((!cell t 2) && xor (cell t 1) (cell (t-Q) 1))
    ((!cell (t-Q) 1) && xor (cell t 2) (cell (t-Q) 2)) at hs
  rw [← or_difference] at hs
  have hh := or_of_live_defect (cell t 1) (cell t 2) (cell (t-Q) 1) (cell (t-Q) 2) h0 hs.symm
  change xor (cell t 0) (cell t 1 || cell t 2)=xor (cell t 0) (cell t 1)
  rw [hh]

/-- Two identical finite blocks of XOR drivers cancel. No infinite period
or whole-state return is supplied for x. -/
theorem xor_two_blocks (x c : Nat → Bool) (P t : Nat)
    (hc : ∀ j, j<P → c (t+P+j)=c (t+j))
    (hx : ∀ j, j<2*P → x (t+j+1)=xor (c (t+j)) (x (t+j))) :
    x (t+2*P)=x t := by
  have hd : ∀ j, j≤P → xor (x (t+P+j)) (x (t+j))=xor (x (t+P)) (x t) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        rw [show t+P+(j+1)=t+(P+j)+1 by omega,
          show t+(j+1)=t+j+1 by omega, hx (P+j) (by omega), hx j (by omega),
          show t+(P+j)=t+P+j by omega, hc j (by omega), xor_same_left]
        exact ih (by omega)
  have h := hd P (by omega)
  rw [show t+P+P=t+2*P by omega] at h
  have cancel (a b d : Bool) (hh : xor a b=xor b d) : a=d := by
    cases a <;> cases b <;> cases d <;> simp_all
  exact cancel _ _ _ h

/-- Q=2P is chosen once. The Q+1 readings include BOTH endpoints.
Every uninterrupted true mismatch episode after T+Q therefore has at
most Q readings; no common reset of physical column two is assumed. -/
theorem bounded_mismatch_episode {T P : Nat} (_hP : 0<P)
    (hc : ∀ s, T≤s → cell (s+P) 0=cell s 0)
    (t : Nat) (ht : T+2*P≤t) :
    ∃ j, j≤2*P ∧ mismatch (2*P) (t+j)=false := by
  apply Classical.byContradiction
  intro hn
  have hall : ∀ j, j≤2*P → mismatch (2*P) (t+j)=true := by
    intro j hj
    cases hh : mismatch (2*P) (t+j)
    · exact (hn ⟨j,hj,hh⟩).elim
    · rfl
  have hpq : P∣2*P := ⟨2,by omega⟩
  have hq := periodic_multiple hc hpq
  have hs : ∀ j, j<2*P → cell (t+j+1) 1=xor (cell (t+j) 0) (cell (t+j) 1) := by
    intro j hj
    apply live_mismatch_step hq (t+j) (by omega) (hall j (by omega))
    simpa only [Nat.add_assoc] using hall (j+1) (by omega)
  have he := xor_two_blocks (fun s => cell s 1) (fun s => cell s 0) P t
    (fun j _ => by
      have hh := hc (t+j) (by omega)
      simpa only [show t+j+P=t+P+j by omega] using hh) hs
  have hf := hall (2*P) (by omega)
  unfold mismatch at hf
  rw [show t+2*P-2*P=t by omega,he] at hf
  cases cell t 1 <;> simp_all

/-- The exact physical event whose frequency remains to be controlled. -/
theorem true_birth_iff {T Q : Nat}
    (hc : ∀ s, T≤s → cell (s+Q) 0=cell s 0)
    (t : Nat) (ht : T+Q≤t) :
    (mismatch Q t=false ∧ mismatch Q (t+1)=true) ↔
      (cell t 1=false ∧ cell (t-Q) 1=false ∧ cell t 2≠cell (t-Q) 2) := by
  rw [periodic_mismatch_step hc t ht]
  unfold mismatch persists forcing
  cases cell t 1 <;> cases cell (t-Q) 1 <;> cases cell t 2 <;> cases cell (t-Q) 2 <;> decide


def trueBirth (Q t : Nat) : Bool :=
  !(mismatch Q t) && mismatch Q (t+1)

/-- The half-open source interval [n0,X-1), empty if X-1≤n0. -/
def birthCount (Q n0 X : Nat) : Nat :=
  intervalCount (trueBirth Q) n0 (X-1)

theorem zero_one_between (p : Nat → Bool) (z s : Nat)
    (hzs : z≤s) (hz : p z=false) (hs : p s=true) :
    ∃ u, z≤u ∧ u<s ∧ p u=false ∧ p (u+1)=true := by
  have hd : ∀ d, p (z+d)=true →
      ∃ u, z≤u ∧ u<z+d ∧ p u=false ∧ p (u+1)=true := by
    intro d
    induction d with
    | zero => intro h; simp [hz] at h
    | succ d ih =>
        intro h
        cases hp : p (z+d)
        · refine ⟨z+d,by omega,by omega,hp,?_⟩
          simpa only [Nat.add_assoc] using h
        · obtain ⟨u,hzu,hus,hu,hn⟩ := ih hp
          exact ⟨u,hzu,by omega,hu,hn⟩
  simpa only [show z+(s-z)=s by omega] using hd (s-z) (by
    simpa only [show z+(s-z)=s by omega] using hs)

/-- A reset followed by an actual MaskedJen witness forces a distinct birth.
The birth's successor is strictly inside the padded doubling window. -/
theorem birth_window {T P : Nat} (hP : 0<P)
    (hc : ∀ t, T≤t → cell (t+P) 0=cell t 0)
    (n : Nat) (hn : T+2*P≤n) :
    ∃ u, n≤u ∧ u+1<2*(n+2*P) ∧ trueBirth (2*P) u=true := by
  obtain ⟨j,hj,hz⟩ := bounded_mismatch_episode hP hc n hn
  have hPQ : P∣2*P := ⟨2,by omega⟩
  have hq := periodic_multiple hc hPQ
  obtain ⟨s,hns,hsn,_hw,hd⟩ :=
    Rule30MaskedJen.periodic_window (show 0<2*P by omega) hq (n+2*P) (by omega)
  have hs : mismatch (2*P) s=true := by
    unfold mismatch
    cases h1 : cell s 1 <;> cases h2 : cell (s-2*P) 1 <;> simp [h1,h2] at hd ⊢
  obtain ⟨u,hzu,hus,hu,hu1⟩ :=
    zero_one_between (mismatch (2*P)) (n+j) s (by omega) hz hs
  refine ⟨u,by omega,by omega,?_⟩
  simp [trueBirth,hu,hu1]

def blockStart (Q n0 : Nat) : Nat → Nat
  | 0 => n0
  | k+1 => 2*(blockStart Q n0 k+Q)

theorem blockStart_ge (Q n0 k : Nat) : n0≤blockStart Q n0 k := by
  induction k with
  | zero => exact Nat.le_refl n0
  | succ k ih => simp only [blockStart]; omega

theorem blockStart_formula (Q n0 k : Nat) :
    blockStart Q n0 k+2*Q=2^k*(n0+2*Q) := by
  induction k with
  | zero => simp [blockStart]
  | succ k ih =>
      calc
        blockStart Q n0 (k+1)+2*Q = 2*(blockStart Q n0 k+2*Q) := by
          simp only [blockStart]; omega
        _ = 2*(2^k*(n0+2*Q)) := by rw [ih]
        _ = 2^(k+1)*(n0+2*Q) := by
          simp only [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm 2]

theorem intervalCount_mono_hi (p : Nat → Bool) {a b c : Nat}
    (hab : a≤b) (hbc : b≤c) : intervalCount p a b≤intervalCount p a c := by
  rw [intervalCount_split p hab hbc]
  omega

/-- Disjoint padded blocks count births, not repeated live-mismatch readings. -/
theorem block_birth_lower {T P n0 : Nat} (hP : 0<P)
    (hc : ∀ t, T≤t → cell (t+P) 0=cell t 0) (hn0 : T+2*P≤n0) (k : Nat) :
    k≤intervalCount (trueBirth (2*P)) n0 (blockStart (2*P) n0 k) := by
  induction k with
  | zero => simp [blockStart,intervalCount]
  | succ k ih =>
      have hb := blockStart_ge (2*P) n0 k
      obtain ⟨u,hu,hu1,hbirth⟩ := birth_window hP hc
        (blockStart (2*P) n0 k) (by omega)
      have hw : 1≤intervalCount (trueBirth (2*P))
          (blockStart (2*P) n0 k) (blockStart (2*P) n0 (k+1)) := by
        apply intervalCount_pos _ hu ?_ hbirth
        simp only [blockStart]
        omega
      rw [intervalCount_split _ hb (by simp only [blockStart]; omega)]
      omega

/-- All parameters, particularly Q=2P, are fixed before m. The bound includes
m=0 and respects the excluded final source tick X-1. -/
theorem base_four_birth_lower {T P n0 : Nat} (hP : 0<P)
    (hc : ∀ t, T≤t → cell (t+P) 0=cell t 0)
    (hn0 : T+2*P≤n0) (hsize : 4*P≤n0) (m : Nat) :
    2*m≤birthCount (2*P) n0 (4^m*n0)+1 := by
  cases m with
  | zero => omega
  | succ m =>
      have hb := blockStart_formula (2*P) n0 (2*m+1)
      have he : 2^(2*m+1)*2=4^(m+1) := by
        calc
          2^(2*m+1)*2 = 2^((2*m+1)+1) := (Nat.pow_succ 2 (2*m+1)).symm
          _ = 2^(2*(m+1)) := by rw [show (2*m+1)+1=2*(m+1) by omega]
          _ = 4^(m+1) := by
            simp only [Nat.pow_mul,show (2:Nat)^2=4 by decide]
      have hmul := Nat.mul_le_mul_left (2^(2*m+1))
        (show n0+2*(2*P)≤2*n0 by omega)
      rw [show 2^(2*m+1)*(2*n0)=(2^(2*m+1)*2)*n0 from
        (Nat.mul_assoc _ _ _).symm,he] at hmul
      have hend : blockStart (2*P) n0 (2*m+1)≤4^(m+1)*n0-1 := by omega
      have lo := block_birth_lower hP hc hn0 (2*m+1)
      have hm := intervalCount_mono_hi (trueBirth (2*P))
        (blockStart_ge (2*P) n0 (2*m+1)) hend
      unfold birthCount
      omega

/-- Exact physical interpretation of a counted event on the valid tail. -/
theorem trueBirth_physical_iff {T P : Nat}
    (hc : ∀ t, T≤t → cell (t+P) 0=cell t 0)
    (t : Nat) (ht : T+2*P≤t) :
    trueBirth (2*P) t=true ↔
      (cell t 1=false ∧ cell (t-2*P) 1=false ∧ cell t 2≠cell (t-2*P) 2) := by
  have hPQ : P∣2*P := ⟨2,by omega⟩
  have hh := true_birth_iff (periodic_multiple hc hPQ) t ht
  simpa [trueBirth] using hh

/-- The unproved upper-frequency premise is the remaining obligation.
It chooses n0,C,M once for each hypothetical period, before every horizon. -/
theorem problem1_of_fixed_birth_budget
    (upper : ∀ T P : Nat, 0<P →
      (∀ t, T≤t → cell (t+P) 0=cell t 0) →
      ∃ n0 C M : Nat, T+2*P≤n0 ∧ 4*P≤n0 ∧
        ∀ m, M≤m → birthCount (2*P) n0 (4^m*n0)≤C+m) : Problem1 := by
  rintro ⟨T,P,hP,hc⟩
  obtain ⟨n0,C,M,hn0,hsize,hu⟩ := upper T P hP hc
  have lo := base_four_birth_lower hP hc hn0 hsize (M+C+2)
  have hi := hu (M+C+2) (by omega)
  omega
end Ruliology.CellularAutomata.Rule30PhysicalDefects
