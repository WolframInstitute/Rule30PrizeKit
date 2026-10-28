module

public import Ruliology.CellularAutomata.Rule30FiniteDiagonals
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# White cells in sufficiently old intervals of left diagonals

For every Rule 30 configuration `x` that is white left of an integer anchor,
`Rule30FiniteDiagonals.Ld x anchor j t` reads position `anchor - t + j` at time `t`.
For any `lo >= 1`, put `P = 2^lo` and `B = lo + 2*P`. At every age
`A >= resetAge lo = 2*P^2+P-1`, some left diagonal with index in `[lo,B]`
is white (`Ld_white_witness_after_reset`).
The initial configuration to the right of the anchor is arbitrary; the anchor
itself need not be black. No finite support or finite-width certificate is used.

The proof starts with the explicit clock onset: coordinate `i` has period
`2^i` from time `2^i-1`. A hypothetical black interval resets successive
coordinates. Each reset occurs within the first known driver period, so the
common period P crosses one coordinate at an onset cost of P. After 2*P
coordinates, a return to black contradicts the interval's white causal interior.
The original `2^B-1` statements and reset-backshift helpers remain available.

The abstract recurrence theorems apply to any Boolean array satisfying the
triangular left-diagonal recurrence. `Ld_recurrence` supplies the exact bridge
from the pinned configuration dynamics. These are statements about moving
diagonal coordinates, not eventual periodicity or nonperiodicity of a fixed
physical column.

Sources: the Boolean transducer argument is
`Rule30Diagonals.transducer_periodic`; the exact `Ld` definition, white-left
hypothesis, and recurrence are from `Rule30FiniteDiagonals`. The interval bound
combines those ingredients with the literal Rule 30 causal cone.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30AgedLeftDiagonals

def Recurrence (b : Nat → Nat → Bool) : Prop :=
  (∀ t, b 0 (t+1) = b 0 t) ∧
  (∀ t, b 1 (t+1) = (b 0 t || b 1 t)) ∧
  (∀ i t, b (i+2) (t+1) = xor (b i t) (b (i+1) t || b (i+2) t))

def PeriodFrom (x : Nat → Bool) (T P : Nat) : Prop :=
  ∀ t, T ≤ t → x (t+P) = x t

theorem period_mono {x : Nat → Bool} {T U P : Nat}
    (h : PeriodFrom x T P) (hTU : T ≤ U) : PeriodFrom x U P :=
  fun _ ht => h _ (Nat.le_trans hTU ht)

theorem period_mul {x : Nat → Bool} {T P : Nat} (h : PeriodFrom x T P)
    (k t : Nat) (ht : T ≤ t) : x (t+k*P) = x t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, h _ (by omega), ih]

theorem period_double {x : Nat → Bool} {T P : Nat} (h : PeriodFrom x T P) :
    PeriodFrom x T (2*P) := by
  intro t ht
  rw [show t+2*P=t+P+P by omega, h _ (by omega), h t ht]

/-- Uniform onset inherited from the general left-recurrence clock theorem. -/
theorem uniform_period {b : Nat → Nat → Bool} (h : Recurrence b) :
    ∀ i, PeriodFrom (b i) (2^i-1) (2^i) :=
  Rule30FiniteDiagonals.left_recurrence_uniform_period b h.1 h.2.1 h.2.2

/-- A reset gives eventual P-periodicity. Known Q-periodicity pulls it back
to the stated onset T; no backward transfer is assumed without that clock. -/
theorem reset_inherits {x l g : Nat → Bool} {T P Q A : Nat}
    (hx : ∀ t, x (t+1) = xor (l t) (g t || x t))
    (hl : PeriodFrom l T P) (hg : PeriodFrom g T P)
    (hq : PeriodFrom x T Q) (hQ : 0 < Q)
    (hA : T ≤ A) (hblack : g A = true) : PeriodFrom x T P := by
  have start : x (A+1+P) = x (A+1) := by
    rw [show A+1+P=A+P+1 by omega, hx, hx, hl A hA, hg A hA, hblack]
    simp
  have future : ∀ s, x (A+1+s+P) = x (A+1+s) := by
    intro s
    induction s with
    | zero => simpa using start
    | succ s ih =>
      rw [show A+1+(s+1)+P=(A+1+s+P)+1 by omega,
        show A+1+(s+1)=(A+1+s)+1 by omega, hx, hx,
        hl _ (by omega), hg _ (by omega), ih]
  intro t ht
  have hlarge : A+1 ≤ (A+1)*Q := by
    have hh := Nat.mul_le_mul_left (A+1) (show 1 ≤ Q by omega)
    simpa using hh
  have hf := future (t+(A+1)*Q-(A+1))
  rw [show A+1+(t+(A+1)*Q-(A+1))=t+(A+1)*Q by omega] at hf
  rw [show t+(A+1)*Q+P=t+P+(A+1)*Q by omega,
    period_mul hq (A+1) (t+P) (by omega), period_mul hq (A+1) t ht] at hf
  exact hf

theorem rec_at {b : Nat → Nat → Bool} (h : Recurrence b) (i t : Nat) (hi : 2 ≤ i) :
    b i (t+1) = xor (b (i-2) t) (b (i-1) t || b i t) := by
  have hh := h.2.2 (i-2) t
  simpa [show i-2+2=i by omega, show i-2+1=i-1 by omega] using hh

/-- A black interval becomes a white interior after one tick; its white
interior then shrinks by two cells on the left per tick. -/
theorem black_erodes {b : Nat → Nat → Bool} (h : Recurrence b) {lo hi A : Nat}
    (hb : ∀ i, lo ≤ i → i ≤ hi → b i A = true) :
    ∀ n i, lo+2*(n+1) ≤ i → i ≤ hi → b i (A+(n+1)) = false := by
  intro n
  induction n with
  | zero =>
    intro i hlo hhi
    rw [show A+(0+1)=A+1 by omega, rec_at h i A (by omega),
      hb (i-2) (by omega) (by omega), hb (i-1) (by omega) (by omega), hb i (by omega) hhi]
    rfl
  | succ n ih =>
    intro i hlo hhi
    rw [show A+(n+1+1)=(A+(n+1))+1 by omega, rec_at h i (A+(n+1)) (by omega),
      ih (i-2) (by omega) (by omega), ih (i-1) (by omega) (by omega), ih i (by omega) hhi]
    rfl

/-- Across a black interval, the leftmost two clocks propagate unchanged.
The observed black phases give resets; uniform longer clocks justify moving
the inherited period back to the common onset. -/
theorem black_interval_period {b : Nat → Nat → Bool} (h : Recurrence b)
    (a B A : Nat) (haB : a+1 ≤ B) (hA : 2^B-1 ≤ A)
    (hb : ∀ i, a+1 ≤ i → i ≤ B → b i A = true) :
    PeriodFrom (b B) (2^B-1) (2^(a+1)) := by
  have up : ∀ i, i ≤ B → PeriodFrom (b i) (2^B-1) (2^i) := by
    intro i hi
    exact period_mono (uniform_period h i)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) hi) 1)
  have base0 : PeriodFrom (b a) (2^B-1) (2^(a+1)) := by
    rw [show 2^(a+1)=2*2^a by rw [Nat.pow_succ]; omega]
    exact period_double (up a (by omega))
  have base1 := up (a+1) haB
  have pairs : ∀ k, a+k+1 ≤ B →
      PeriodFrom (b (a+k)) (2^B-1) (2^(a+1)) ∧
      PeriodFrom (b (a+k+1)) (2^B-1) (2^(a+1)) := by
    intro k
    induction k with
    | zero => intro _; simpa using And.intro base0 base1
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hn := reset_inherits (x := b (a+k+2)) (l := b (a+k)) (g := b (a+k+1))
        (fun t => h.2.2 (a+k) t) hp.1 hp.2 (up (a+k+2) (by omega))
        (Nat.two_pow_pos _) hA (hb (a+k+1) (by omega) (by omega))
      simpa [Nat.add_assoc] using And.intro hp.2 hn
  have hh := (pairs (B-a-1) (by omega)).2
  simpa [show a+(B-a-1)+1=B by omega] using hh

/-- Uniform arbitrary-interval obstruction. Starting at index a+1 avoids
special negative-boundary notation. Equivalently, for lo>=1 the right endpoint
is lo+2^(lo+1), and the onset is 2^endpoint-1. -/
theorem no_aged_black_interval {b : Nat → Nat → Bool} (h : Recurrence b)
    (a A : Nat) (hA : 2^(a+1+2^(a+2))-1 ≤ A) :
    ¬ (∀ i, a+1 ≤ i → i ≤ a+1+2^(a+2) → b i A = true) := by
  intro hb
  let B := a+1+2^(a+2)
  let P := 2^(a+1)
  have hP : 0 < P := Nat.two_pow_pos _
  have hB : B = a+1+2*P := by
    dsimp [B, P]
    rw [show a+2=(a+1)+1 by omega, Nat.pow_succ]
    omega
  have hp := black_interval_period h a B A (by omega) hA hb
  have he := black_erodes h hb (P-1) B (by omega) (Nat.le_refl _)
  rw [show P-1+1=P by omega] at he
  have hper := hp A hA
  change b B (A+P) = b B A at hper
  rw [he, hb B (by omega) (Nat.le_refl _)] at hper
  cases hper

theorem aged_white_witness {b : Nat → Nat → Bool} (h : Recurrence b)
    (a A : Nat) (hA : 2^(a+1+2^(a+2))-1 ≤ A) :
    ∃ i, a+1 ≤ i ∧ i ≤ a+1+2^(a+2) ∧ b i A = false := by
  classical
  apply Classical.byContradiction
  intro hn
  apply no_aged_black_interval h a A hA
  intro i hi hj
  cases hc : b i A
  · exact (hn ⟨i,hi,hj,hc⟩).elim
  · rfl


/-! ### The literal left diagonals of a configuration with a white left side -/

/-- The pinned `Ld` dynamics satisfy the abstract recurrence. Only the initial
white-left condition is needed; the anchor need not be black. -/
theorem Ld_recurrence {x : Int → Bool} {anchor : Int}
    (hleft : ∀ p, p < anchor → x p = false) :
    Recurrence (Rule30FiniteDiagonals.Ld x anchor) :=
  ⟨Rule30FiniteDiagonals.Ld_zero_succ hleft,
    Rule30FiniteDiagonals.Ld_one_succ hleft,
    fun i t => Rule30FiniteDiagonals.Ld_step (x := x) (lo := anchor) i t⟩

/-- At every sufficiently old age, a bounded interval of left-diagonal
indices contains a white cell. The interval start is any positive natural. -/
theorem Ld_aged_white_witness {x : Int → Bool} {anchor : Int}
    (hleft : ∀ p, p < anchor → x p = false)
    (lo A : Nat) (hlo : 1 ≤ lo) (hA : 2^(lo+2^(lo+1))-1 ≤ A) :
    ∃ i, lo ≤ i ∧ i ≤ lo+2^(lo+1) ∧
      Rule30FiniteDiagonals.Ld x anchor i A = false := by
  obtain ⟨a, rfl⟩ : ∃ a, lo = a+1 := ⟨lo-1, by omega⟩
  simpa [Nat.add_assoc] using aged_white_witness (Ld_recurrence hleft) a A hA

/-- The same white witness in literal evolution coordinates. Its physical
position is `anchor - A + i`, moving with the left-edge diagonal frame. -/
theorem evol_aged_white_witness {x : Int → Bool} {anchor : Int}
    (hleft : ∀ p, p < anchor → x p = false)
    (lo A : Nat) (hlo : 1 ≤ lo) (hA : 2^(lo+2^(lo+1))-1 ≤ A) :
    ∃ i : Nat, lo ≤ i ∧ i ≤ lo+2^(lo+1) ∧
      Rule30Realization.evol x A (anchor - (A : Int) + (i : Int)) = false := by
  simpa only [Rule30FiniteDiagonals.Ld] using
    Ld_aged_white_witness hleft lo A hlo hA

/-! ### A forward-reset onset without an output-period premise -/

/-- A black reset occurs within the first known driver period. Its output is
P-periodic from T+P, without any prior periodicity assumption on the output. -/
theorem reset_first_period {x l g : Nat → Bool} {T P A : Nat}
    (hx : ∀ t, x (t+1) = xor (l t) (g t || x t))
    (hl : PeriodFrom l T P) (hg : PeriodFrom g T P)
    (hP : 0 < P) (hA : T ≤ A) (hblack : g A = true) :
    PeriodFrom x (T+P) P := by
  let R := T+(A-T)%P
  have hr0 : T ≤ R := by dsimp [R]; omega
  have hr1 : R < T+P := by
    have hm := Nat.mod_lt (A-T) hP
    dsimp [R]
    omega
  have he : R+((A-T)/P)*P = A := by
    have hd := Nat.mod_add_div (A-T) P
    rw [Nat.mul_comm P ((A-T)/P)] at hd
    dsimp [R]
    omega
  have hb : g R = true := by
    have hh := period_mul hg ((A-T)/P) R hr0
    rw [he,hblack] at hh
    exact hh.symm
  have start : x (R+1+P) = x (R+1) := by
    rw [show R+1+P=R+P+1 by omega,hx,hx,hl R hr0,hg R hr0,hb]
    simp
  have future : ∀ s, x (R+1+s+P) = x (R+1+s) := by
    intro s
    induction s with
    | zero => simpa using start
    | succ s ih =>
        rw [show R+1+(s+1)+P=(R+1+s+P)+1 by omega,
          show R+1+(s+1)=(R+1+s)+1 by omega,hx,hx,
          hl _ (by omega),hg _ (by omega),ih]
  intro t ht
  have hf := future (t-(R+1))
  simpa only [show R+1+(t-(R+1))=t by omega] using hf

/-- A common P-clock crosses a black interval at an onset cost of P per
coordinate. Only the two base clocks use the general uniform clock bound. -/
theorem black_interval_period_forward {b : Nat → Nat → Bool} (h : Recurrence b)
    (a B A : Nat) (haB : a+1 ≤ B)
    (hA : (2^(a+1)-1)+(B-a-1)*2^(a+1) ≤ A)
    (hb : ∀ i, a+1 ≤ i → i ≤ B → b i A = true) :
    PeriodFrom (b B) ((2^(a+1)-1)+(B-a-1)*2^(a+1)) (2^(a+1)) := by
  let P := 2^(a+1)
  let T := P-1
  have hP : 0 < P := Nat.two_pow_pos _
  have base0 : PeriodFrom (b a) T P := by
    have hp : PeriodFrom (b a) T (2^a) :=
      period_mono (uniform_period h a)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega)) 1)
    have hd := period_double hp
    have he : P=2*2^a := by dsimp [P]; rw [Nat.pow_succ]; omega
    simpa only [← he] using hd
  have base1 : PeriodFrom (b (a+1)) T P := uniform_period h (a+1)
  have pairs : ∀ k, a+k+1 ≤ B →
      PeriodFrom (b (a+k)) (T+k*P) P ∧
      PeriodFrom (b (a+k+1)) (T+k*P) P := by
    intro k
    induction k with
    | zero => intro _; simpa using And.intro base0 base1
    | succ k ih =>
        intro hk
        have hp := ih (by omega)
        have hmul : k*P ≤ (B-a-1)*P := Nat.mul_le_mul_right P (by omega)
        have hTA : T+k*P ≤ A := by change T+(B-a-1)*P ≤ A at hA; omega
        have hn := reset_first_period
          (x := b (a+k+2)) (l := b (a+k)) (g := b (a+k+1))
          (fun t => h.2.2 (a+k) t) hp.1 hp.2 hP hTA
          (hb (a+k+1) (by omega) (by omega))
        change PeriodFrom (b (a+k+1)) (T+(k+1)*P) P ∧
          PeriodFrom (b (a+k+2)) (T+(k+1)*P) P
        have hon : T+(k+1)*P=(T+k*P)+P := by rw [Nat.succ_mul]; omega
        rw [hon]
        exact ⟨period_mono hp.2 (by omega),hn⟩
  have hh := (pairs (B-a-1) (by omega)).2
  simpa only [show a+(B-a-1)+1=B by omega] using hh

/-- With P=2^lo, this is 2*P^2+P-1. -/
def resetAge (lo : Nat) : Nat := (2^lo-1)+2*2^lo*2^lo

/-- At the forward-reset onset, an interval of 2P+1 simultaneous black
cells contradicts its own inherited P-clock and the white causal interior. -/
theorem no_black_interval_after_reset {b : Nat → Nat → Bool} (h : Recurrence b)
    (a A : Nat) (hA : resetAge (a+1) ≤ A) :
    ¬ (∀ i, a+1 ≤ i → i ≤ a+1+2^(a+2) → b i A = true) := by
  intro hb
  let B := a+1+2^(a+2)
  let P := 2^(a+1)
  have hP : 0 < P := Nat.two_pow_pos _
  have hB : B=a+1+2*P := by
    dsimp [B,P]
    rw [show a+2=(a+1)+1 by omega,Nat.pow_succ]
    omega
  have hBA : B-a-1=2*P := by omega
  have hT : (2^(a+1)-1)+(B-a-1)*2^(a+1)=resetAge (a+1) := by
    rw [hBA]
    rfl
  have hp := black_interval_period_forward h a B A (by omega)
    (by rw [hT]; exact hA) hb
  have he := black_erodes h hb (P-1) B (by omega) (Nat.le_refl _)
  rw [show P-1+1=P by omega] at he
  have hper := hp A (by rw [hT]; exact hA)
  change b B (A+P)=b B A at hper
  rw [he,hb B (by omega) (Nat.le_refl _)] at hper
  cases hper

theorem white_witness_after_reset {b : Nat → Nat → Bool} (h : Recurrence b)
    (lo A : Nat) (hlo : 1 ≤ lo) (hA : resetAge lo ≤ A) :
    ∃ i, lo ≤ i ∧ i ≤ lo+2^(lo+1) ∧ b i A=false := by
  classical
  apply Classical.byContradiction
  intro hn
  have he : lo-1+1=lo := by omega
  have he2 : lo-1+2=lo+1 := by omega
  apply no_black_interval_after_reset h (lo-1) A (by simpa only [he] using hA)
  intro i hi hj
  rw [he] at hi
  rw [he,he2] at hj
  cases hc : b i A
  · exact (hn ⟨i,hi,hj,hc⟩).elim
  · rfl

/-- The literal Ld witness has the improved age and arbitrary right-hand
initial data. The white-left anchor itself need not be black. -/
theorem Ld_white_witness_after_reset {x : Int → Bool} {anchor : Int}
    (hleft : ∀ p, p < anchor → x p=false)
    (lo A : Nat) (hlo : 1 ≤ lo) (hA : resetAge lo ≤ A) :
    ∃ i, lo ≤ i ∧ i ≤ lo+2^(lo+1) ∧
      Rule30FiniteDiagonals.Ld x anchor i A=false :=
  white_witness_after_reset (Ld_recurrence hleft) lo A hlo hA

theorem evol_white_witness_after_reset {x : Int → Bool} {anchor : Int}
    (hleft : ∀ p, p < anchor → x p=false)
    (lo A : Nat) (hlo : 1 ≤ lo) (hA : resetAge lo ≤ A) :
    ∃ i : Nat, lo ≤ i ∧ i ≤ lo+2^(lo+1) ∧
      Rule30Realization.evol x A (anchor-(A:Int)+(i:Int))=false := by
  simpa only [Rule30FiniteDiagonals.Ld] using Ld_white_witness_after_reset hleft lo A hlo hA


end Rule30AgedLeftDiagonals
end Ruliology.CellularAutomata
