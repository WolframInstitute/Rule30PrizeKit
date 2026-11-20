module

public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30Prize

/-! # Dyadic center pulses of the right-edge sources

In right-edge coordinates a Rule 90 step is the XOR of the same depth and
the depth two places earlier. Rule 30 adds a source at depth `d+1`
exactly when adjacent cells at depths `d,d-1` read black, white. `strip_pulse`
places an isolated pulse on every finite strip from the right edge. The
same pulse and quiet interval hold with cutoff increasing linearly in the
exponent. `center_decomposition` accounts for the remaining sources, and
`deep_must_differ` states their necessary compensation for a repeated reading.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30EdgeSourcePulse
open Rule30Diagonals Rule30Jen

abbrev Row := Int → Bool
def step (x : Row) (j : Int) := xor (x j) (x (j-2))
def free : Nat → Row → Row
  | 0, x => x
  | n+1, x => step (free n x)
def run (b : Nat → Row) : Nat → Row
  | 0 => fun _ => false
  | n+1 => fun j => xor (step (run b n) j) (b n j)

private theorem free_add (a n : Nat) (x : Row) : free (a+n) x = free n (free a x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg step ih

private theorem free_xor (n : Nat) (x y : Row) (j : Int) :
    free n (fun i => xor (x i) (y i)) j = xor (free n x j) (free n y j) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [free, step, ih]
    cases free n x j <;> cases free n y j <;> cases free n x (j-2) <;> cases free n y (j-2) <;> rfl

private theorem frobenius (k : Nat) (x : Row) (j : Int) :
    free (2^k) x j = xor (x j) (x (j-2*(2^k : Nat))) := by
  induction k generalizing x j with
  | zero => rfl
  | succ k ih =>
    rw [show 2^(k+1) = 2^k + 2^k by simp [Nat.pow_succ, Nat.mul_two], free_add, ih, ih, ih]
    push_cast
    rw [show j-2*(2:Int)^k-2*2^k = j-2*(2^k+2^k) by omega]
    generalize x j = a
    generalize x (j-2*(2:Int)^k) = b
    generalize x (j-2*((2:Int)^k+2^k)) = c
    cases a <;> cases b <;> cases c <;> rfl

private theorem split_run (b : Nat → Row) (a n : Nat) (j : Int) :
    run b (a+n) j = xor (free n (run b a) j) (run (fun i => b (a+i)) n j) := by
  induction n generalizing j with
  | zero => simp [free, run]
  | succ n ih =>
    change xor (xor (run b (a+n) j) (run b (a+n) (j-2))) (b (a+n) j) = _
    rw [ih j, ih (j-2)]
    simp only [free, step, run]
    generalize free n (run b a) j = u
    generalize free n (run b a) (j-2) = v
    generalize run (fun i => b (a+i)) n j = w
    generalize run (fun i => b (a+i)) n (j-2) = z
    cases u <;> cases v <;> cases w <;> cases z <;> cases b (a+n) j <;> rfl

private theorem run_out (b : Nat → Row) (D : Nat)
    (h : ∀ s j, j < 0 ∨ (D:Int)+1 < j → b s j = false) (n : Nat) (j : Int)
    (hj : j < 0 ∨ (D:Int)+2*n < j) : run b n j = false := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [run, step, ih j (by omega), ih (j-2) (by omega), h n j (by omega)]
    rfl

private theorem free_out (x : Row) (L H : Int)
    (h : ∀ j, j < L ∨ H < j → x j = false) (n : Nat) (j : Int)
    (hj : j < L ∨ H+2*n < j) : free n x j = false := by
  induction n generalizing j with
  | zero => exact h j (by omega)
  | succ n ih => simp [free, step, ih j (by omega), ih (j-2) (by omega)]

/-- The forcing at the *new* depth j, from true singleton diagonal j-1. -/
def source (D t : Nat) (j : Int) : Bool :=
  if 1 ≤ j ∧ j ≤ (D:Int)+1 then
    R (j-1).toNat t && !(if j=1 then false else R (j-2).toNat t)
  else false

private theorem src_out (D t : Nat) (j : Int) (h : j < 0 ∨ (D:Int)+1 < j) :
    source D t j = false := by unfold source; split <;> simp_all <;> omega

private theorem period_le (d D t : Nat) (hd : d ≤ D) : R d (t+2^D) = R d t := by
  induction D generalizing t with
  | zero =>
    obtain rfl : d=0 := by omega
    exact R_periodic 0 t
  | succ D ih =>
    by_cases e : d = D+1
    · subst d; exact R_periodic _ _
    · rw [show 2^(D+1) = 2^D+2^D by simp [Nat.pow_succ, Nat.mul_two], ← Nat.add_assoc,
          ih _ (by omega), ih _ (by omega)]

private theorem periodic_src (D t : Nat) : source D (2^D+t) = source D t := by
  funext j
  unfold source
  split <;> rename_i h
  · rw [Nat.add_comm, period_le _ _ _ (by omega), period_le _ _ _ (by omega)]
  · rfl

private theorem all_one (D : Nat) :
    ∀ d ≤ D, R d (2^D-1) = true := by
  intro d
  induction d with
  | zero => intro _; exact R_zero _
  | succ d ih =>
    intro hd
    let t := 2^D-1
    have hp : 0 < 2^D := Nat.two_pow_pos _
    have ht : t+1=2^D := by dsimp [t]; omega
    have hz : R (d+1) (t+1) = false := by
      rw [ht, ← Nat.zero_add (2^D), period_le _ _ _ hd]
      simp [R, cell] <;> omega
    have prior := ih (by omega)
    change R d t = true at prior
    change R (d+1) t = true
    cases d with
    | zero => rw [R_one_succ] at hz; cases h : R 1 t <;> simp_all
    | succ d =>
      rw [R_step, prior] at hz
      cases h : R (d+2) t <;> simp_all

private def atom (j : Int) : Bool := decide (j=1)

private theorem last_src (D : Nat) : source D (2^D-1) = atom := by
  funext j
  by_cases hj : j=1
  · subst j; simp [source, atom, R_zero] <;> omega
  · unfold source atom
    split
    · simp [hj, all_one D (j-2).toNat (by omega)]
    · simp [hj]

private def ramp (j : Int) : Bool := decide (0 < j ∧ j % 2 = 1)

private theorem ramp_step : step ramp = atom := by
  funext j
  simp only [step, ramp, atom]
  by_cases a : 0 < j ∧ j%2=1
  · by_cases b : 0 < j-2 ∧ (j-2)%2=1
    · have c : j ≠ 1 := by omega
      rw [decide_eq_true a, decide_eq_true b, decide_eq_false c]; rfl
    · have c : j=1 := by omega
      subst j; decide
  · have b : ¬ (0 < j-2 ∧ (j-2)%2=1) := by omega
    have c : j≠1 := by omega
    rw [decide_eq_false a, decide_eq_false b, decide_eq_false c]; rfl

private theorem impulse_out (n : Nat) (j : Int) (h : j < 1 ∨ 1+2*(n:Int) < j) :
    free n atom j = false := by
  apply free_out atom 1 1 _ n j h
  intro i hi; simp [atom]; omega

private theorem fold_period (D t : Nat) (ht : D < t) :
    run (source D) t t = free t (run (source D) (2^D)) ((t:Int)+2*(2^D:Nat)) := by
  let j : Int := (t:Int)+2*(2^D:Nat)
  have h := split_run (source D) t (2^D) j
  rw [Nat.add_comm t, split_run, frobenius] at h
  rw [show (fun i => source D (2^D+i)) = source D by funext i; exact periodic_src D i] at h
  have hz := run_out (fun i => source D (t+i)) D (fun i => src_out D (t+i)) (2^D) j
    (Or.inr (by dsimp [j]; omega))
  rw [hz, show j-2*(2^D:Nat) = (t:Int) by dsimp [j]; omega] at h
  change run (source D) t t = free t (run (source D) (2^D)) j
  generalize free t (run (source D) (2^D)) j = u at h ⊢
  generalize run (source D) t j = v at h
  generalize run (source D) t t = w at h ⊢
  cases u <;> cases v <;> cases w <;> simp_all

/-- Center contribution of actual depth-0 through depth-D oriented 10 events. -/
def stripCenter (D t : Nat) := run (source D) t t

/-- Every cutoff D ≤ k gives one at 2^(k+2)-1, followed by 2^(k+1)-1 zeros. -/
theorem strip_pulse (D k i : Nat) (hDk : D ≤ k) (hi : i < 2^(k+1)) :
    stripCenter D (2^(k+2)-1+i) = decide (i=0) := by
  let p := 2^D
  let M := 2^(k+2)
  let t := M-1+i
  let j : Int := (t:Int)+2*(p:Nat)
  have hp : 0 < p := Nat.two_pow_pos _
  have hD : D < p := Nat.lt_two_pow_self
  have hpK : p ≤ 2^k := Nat.pow_le_pow_right (by decide) hDk
  have hM : M=4*2^k := by dsimp [M]; simp [Nat.pow_succ]; omega
  have hI : i < 2*2^k := by simpa [Nat.pow_succ, Nat.mul_comm] using hi
  have ht : D<t := by dsimp [t]; omega
  change run (source D) t t = _
  rw [fold_period D t ht]
  change free t (run (source D) p) j = _
  let y := run (source D) (p-1)
  have he : run (source D) p = fun a => xor (step y a) (step ramp a) := by
    funext a
    conv => lhs; rw [show p=p-1+1 by omega]
    simp only [run, ramp_step, last_src, y,p]
  rw [he, free_xor]
  have transport (x : Row) : free t (step x) j =
      xor (free i x j) (free i x (j-2*(M:Nat))) := by
    change free t (free 1 x) j = _
    rw [← free_add, show 1+t=i+M by dsimp [t]; omega, free_add]
    exact frobenius (k+2) _ _
  rw [transport, transport]
  have left : j-2*(M:Nat) < 0 := by dsimp [j,t]; omega
  have right : (D:Int)+2*((p-1:Nat):Int)+2*i < j := by dsimp [j,t]; omega
  have outside := free_out y 0 ((D:Int)+2*((p-1:Nat):Int))
    (run_out _ D (src_out D) (p-1)) i
  rw [outside j (Or.inr right), outside _ (Or.inl left)]
  cases i with
  | zero =>
    change xor (xor false false) (xor (ramp j) (ramp (j-2*(M:Nat)))) = true
    have odd : j % 2 = 1 := by dsimp [j,t]; omega
    have pos : 0 < j := by dsimp [j,t]; omega
    simp [ramp, odd, pos] <;> omega
  | succ i =>
    have e (a : Int) : free (i+1) ramp a = free i atom a := by
      rw [Nat.add_comm, free_add]; change free i (step ramp) a = _; rw [ramp_step]
    rw [e, e, impulse_out _ _ (Or.inr (by dsimp [j,t]; omega)),
      impulse_out _ _ (Or.inl (by omega))]
    rfl

/-- Sources deeper than the cutoff, in the same moving coordinates. -/
def deep (D t : Nat) (j : Int) : Bool :=
  if (D:Int)+1 < j then cell t ((t:Int)-j+1) && !cell t ((t:Int)-j+2) else false

private def origin (j : Int) : Bool := decide (j=0)

private theorem source_split (D t : Nat) (j : Int) :
    xor (source D t j) (deep D t j) =
      (cell t ((t:Int)-j+1) && !cell t ((t:Int)-j+2)) := by
  by_cases h : 1 ≤ j
  · by_cases g : j ≤ (D:Int)+1
    · simp only [source, deep, h, g, and_self, ite_true, Int.not_lt.mpr g, ite_false, Bool.xor_false]
      unfold R
      rw [cell_congr (p:=(t:Int)-((j-1).toNat: Int)) (q:=(t:Int)-j+1) (by omega)]
      by_cases e : j=1
      · subst j; simp [cell_eq_false_of_gt t _ (show (t:Int)<t-1+2 by omega)]
      · rw [ite_eq_right e, cell_congr (p:=(t:Int)-((j-2).toNat: Int)) (q:=(t:Int)-j+2) (by omega)]
    · simp [source, deep, g, Int.lt_of_not_ge g]
  · have g : ¬ ((D:Int)+1 < j) := by omega
    simp [source, deep, h, g, cell_eq_false_of_gt t _ (show (t:Int)<t-j+1 by omega)]

private theorem decomposition (D t : Nat) (j : Int) :
    cell t ((t:Int)-j) =
      xor (free t origin j) (xor (run (source D) t j) (run (deep D) t j)) := by
  induction t generalizing j with
  | zero => simp [free, origin, cell, run]
  | succ t ih =>
    rw [cell_succ' t _ ((t:Int)-j) ((t:Int)-j+1) ((t:Int)-(j-2))
      (by omega) (by omega) (by omega)]
    let a := cell t ((t:Int)-j)
    let b := cell t ((t:Int)-j+1)
    let c := cell t ((t:Int)-(j-2))
    have e : rule a b c = xor (xor a c) (b && !c) := by
      cases a <;> cases b <;> cases c <;> rfl
    change rule a b c = _
    rw [e]
    dsimp only [a,b,c]
    rw [show (t:Int)-(j-2)=t-j+2 by omega, ← source_split D t j,
      ← show (t:Int)-(j-2)=t-j+2 by omega, ih j, ih (j-2)]
    simp only [free, run, step]
    simp only [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

private theorem mirror (n : Nat) (j : Int) :
    free n origin j = free n origin (2*(n:Int)-j) := by
  induction n generalizing j with
  | zero => simp [free, origin]
  | succ n ih =>
    simp only [free, step]
    conv => lhs; rw [ih j, ih (j-2)]
    rw [show 2*((n+1:Nat):Int)-j=2*(n:Int)-(j-2) by omega,
      show 2*(n:Int)-(j-2)-2=2*(n:Int)-j by omega, Bool.xor_comm]

/-- The actual singleton center equals the XOR of the strip and its deeper sources. -/
theorem center_decomposition (D t : Nat) (ht : 0<t) :
    cell t 0 = xor (stripCenter D t) (run (deep D) t t) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have h := decomposition D (n+1) (n+1)
  rw [show ((n+1:Nat):Int)-(n+1)=0 by omega] at h
  have e := mirror n (n+1)
  rw [show 2*(n:Int)-(n+1)=(n+1)-2 by omega] at e
  change cell (n+1) 0 = xor (run (source D) (n+1) ((n:Int)+1)) (run (deep D) (n+1) ((n:Int)+1))
  simpa only [free, step, e, Bool.xor_self, Bool.false_xor] using h

/-- If a proposed period works at the two readings, the deep-source parities must differ. -/
theorem deep_must_differ (D k P : Nat) (hd : D ≤ k) (hp : 0<P) (hs : P<2^(k+1))
    (eqCenter : cell (2^(k+2)-1) 0 = cell (2^(k+2)-1+P) 0) :
    run (deep D) (2^(k+2)-1) (2^(k+2)-1 : Nat) ≠
      run (deep D) (2^(k+2)-1+P) (2^(k+2)-1+P : Nat) := by
  let n := 2^(k+2)-1
  have hn : 0<n := by dsimp [n]; have := Nat.two_pow_pos k; simp [Nat.pow_succ]; omega
  have first := strip_pulse D k 0 hd (Nat.two_pow_pos _)
  have second := strip_pulse D k P hd hs
  change stripCenter D n = true at first
  rw [decide_eq_false (by omega : P≠0)] at second
  change cell n 0 = cell (n+P) 0 at eqCenter
  rw [center_decomposition D n hn, center_decomposition D (n+P) (by omega), first, second] at eqCenter
  intro h
  change run (deep D) n n = run (deep D) (n+P) (n+P : Nat) at h
  rw [h] at eqCenter
  generalize run (deep D) (n+P) (n+P : Nat) = v at eqCenter
  cases v <;> contradiction

end Ruliology.CellularAutomata.Rule30EdgeSourcePulse
