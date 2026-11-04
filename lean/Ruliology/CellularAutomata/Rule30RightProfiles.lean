module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Right-diagonal profiles of rule 30: the 101 shift law and its mod-4 forms

Profiles are `Nat → Bool`. `xr f n` is the XOR of `f 0, …, f (n - 1)`.

* `shift_law`: let `q` be even. Suppose that `d` has period `q`, `a` complements at `q`, `b` has period `2q` and `c`
  complements at `2q`, with `b (t+1) = b t xor (a t || d t)` and `z (t+1) = z t xor (c t || b t)`. Then
  `z (t + 4q) = z t xor eta q d` for every `t`, where `eta q d = parity (q/2) xor E q d` and `E q d` is the XOR of
  `d` at the even ticks `0, 2, …, q - 2`.
* `E_mod4`: for `q ≡ 0 mod 4` and `d (t+1) = d t xor h t`, `E q d` is the XOR of `h (4s) xor h (4s+1)`, `s < q/4`.
* `eta_of_antiperiod`, `eta_false_of_antiperiod`, `eta_four`: if `d` complements at `q/2`, then
  `eta q d = parity (q/2) xor parity (q/4)`. This is `false` for `q ≡ 0 mod 8` and `true` at `q = 4`.
* `eta_false_of_period_half`: if `d` has period `q/2` (`q ≡ 0 mod 4`), then `eta q d = false`.
* `rightDiag_step`, `rightDiag_shift_law`: the right diagonals `D j t = x_t (t - j)` of the kit's
  `Rule30Realization.evol` satisfy `D j (t+1) = D j t xor (D (j-1) t || D (j-2) t)` for every start, so the
  shift law holds on actual diagonals under the same period hypotheses.
* `running_shift`: a running XOR of a `p`-periodic forcing shifts by `xr g p` over `p` steps.

These are conditional profile statements. Turning the doubling letters of a finite seed's prefix periods into the
hypotheses is not formalized here, and `eta_false_of_antiperiod` alone is not a finite-seed word exclusion.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30RightProfiles

/-- XOR of `f 0, …, f (n - 1)`. -/
def xr (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xor (xr f n) (f n)

def parity (n : Nat) : Bool := decide (n % 2 = 1)

theorem parity_succ (n : Nat) : parity (n + 1) = !parity n := by
  unfold parity
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (n + 1) % 2 = 0 := by omega
    simp [h, h']

theorem xr_add (f : Nat → Bool) (n m : Nat) :
    xr f (n + m) = xor (xr f n) (xr (fun i => f (n + i)) m) := by
  induction m with
  | zero => simp [xr]
  | succ m ih =>
    rw [Nat.add_succ]
    simp only [xr]
    rw [ih, Bool.xor_assoc]

theorem xr_xor (f g : Nat → Bool) (n : Nat) :
    xr (fun i => xor (f i) (g i)) n = xor (xr f n) (xr g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xr]
    rw [ih]
    cases xr f n <;> cases xr g n <;> cases f n <;> cases g n <;> rfl

theorem xr_congr {f g : Nat → Bool} (n : Nat) (h : ∀ i, i < n → f i = g i) : xr f n = xr g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xr]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem xr_false (n : Nat) : xr (fun _ => false) n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xr]; rw [ih]; rfl

theorem xr_not (f : Nat → Bool) (n : Nat) : xr (fun i => !f i) n = xor (parity n) (xr f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xr]
    rw [ih, parity_succ]
    cases parity n <;> cases xr f n <;> cases f n <;> rfl

theorem xr_true (n : Nat) : xr (fun _ => true) n = parity n := by
  have := xr_not (fun _ => false) n
  rw [xr_false] at this
  simpa using this

/-- Pair the two halves of a window of length `n + n`. -/
theorem xr_halves (f : Nat → Bool) (n : Nat) :
    xr f (n + n) = xr (fun i => xor (f i) (f (n + i))) n := by
  rw [xr_add, xr_xor]

/-- Pair consecutive terms. -/
theorem xr_pairs (f : Nat → Bool) (m : Nat) :
    xr f (2 * m) = xr (fun k => xor (f (2 * k)) (f (2 * k + 1))) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    simp only [xr]
    rw [ih]
    cases xr (fun k => xor (f (2 * k)) (f (2 * k + 1))) m <;> cases f (2 * m) <;> cases f (2 * m + 1) <;> rfl

/-- A running XOR over `n` steps. -/
theorem integral {z g : Nat → Bool} (h : ∀ t, z (t + 1) = xor (z t) (g t)) (t n : Nat) :
    z (t + n) = xor (z t) (xr (fun i => g (t + i)) n) := by
  induction n with
  | zero => simp [xr]
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 by omega, h, ih]
    simp only [xr]
    rw [Bool.xor_assoc]

/-- A window over a full period has the same XOR wherever it starts. -/
theorem xr_window {g : Nat → Bool} {n : Nat} (hg : ∀ t, g (t + n) = g t) (t : Nat) :
    xr (fun i => g (t + i)) n = xr g n := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e1 : xr (fun i => g (t + i)) (1 + n) = xor (g t) (xr (fun i => g (t + 1 + i)) n) := by
      rw [xr_add]
      simp [xr, Nat.add_assoc]
    have e2 : xr (fun i => g (t + i)) (n + 1) = xor (xr (fun i => g (t + i)) n) (g t) := by
      simp only [xr]
      rw [hg t]
    rw [Nat.add_comm 1 n, e2] at e1
    rw [← ih]
    revert e1
    cases xr (fun i => g (t + i)) n <;> cases g t <;> cases xr (fun i => g (t + 1 + i)) n <;> simp

/-- **Running shift**: a running XOR of a `p`-periodic forcing shifts by the forcing's parity over `p` steps. -/
theorem running_shift {D g : Nat → Bool} {p : Nat} (hs : ∀ t, D (t + 1) = xor (D t) (g t))
    (hg : ∀ t, g (t + p) = g t) (t : Nat) : D (t + p) = xor (D t) (xr g p) := by
  rw [integral hs t p, xr_window hg t]

/-- The XOR of `d` at the even ticks `0, 2, …, q - 2`. -/
def E (q : Nat) (d : Nat → Bool) : Bool := xr (fun s => d (2 * s)) (q / 2)

def eta (q : Nat) (d : Nat → Bool) : Bool := xor (parity (q / 2)) (E q d)

/-- **The 101 shift law.** -/
theorem shift_law (q : Nat) (hq : q % 2 = 0) (d a b c z : Nat → Bool)
    (hd : ∀ t, d (t + q) = d t) (ha : ∀ t, a (t + q) = !a t)
    (hb : ∀ t, b (t + 2 * q) = b t) (hc : ∀ t, c (t + 2 * q) = !c t)
    (hbs : ∀ t, b (t + 1) = xor (b t) (a t || d t))
    (hzs : ∀ t, z (t + 1) = xor (z t) (c t || b t)) :
    ∀ t, z (t + 4 * q) = xor (z t) (eta q d) := by
  obtain ⟨G, hG⟩ : ∃ G : Nat → Bool, ∀ s, G s = (c s || b s) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Nat → Bool, ∀ s, H s = (a s || d s) := ⟨_, fun _ => rfl⟩
  have hzs' : ∀ t, z (t + 1) = xor (z t) (G t) := fun t => by rw [hG]; exact hzs t
  have hbs' : ∀ t, b (t + 1) = xor (b t) (H t) := fun t => by rw [hH]; exact hbs t
  have hGp : ∀ s, G (s + 4 * q) = G s := by
    intro s
    rw [hG, hG, show s + 4 * q = (s + 2 * q) + 2 * q by omega, hc, hc, hb, hb, Bool.not_not]
  -- the window total at time 0
  have step1 : xr G (4 * q) = xr b (2 * q) := by
    rw [show 4 * q = 2 * q + 2 * q by omega, xr_halves]
    rw [xr_congr (2 * q) (g := fun i => !b i) (fun i _ => by
      rw [hG, hG, show 2 * q + i = i + 2 * q by omega, hc, hb]
      cases c i <;> cases b i <;> rfl)]
    have hp : parity (2 * q) = false := by unfold parity; simp
    rw [xr_not, hp, Bool.false_xor]
  have step2 : xr b (2 * q) = xr (fun k => H (2 * k)) q := by
    rw [xr_pairs]
    apply xr_congr
    intro k _
    show xor (b (2 * k)) (b (2 * k + 1)) = H (2 * k)
    rw [hbs']
    cases b (2 * k) <;> cases H (2 * k) <;> rfl
  have step3 : xr (fun k => H (2 * k)) q = eta q d := by
    rw [show q = q / 2 + q / 2 by omega, xr_halves]
    rw [show q / 2 + q / 2 = q by omega]
    rw [xr_congr (q / 2) (g := fun s => !d (2 * s)) (fun s _ => by
      show xor (H (2 * s)) (H (2 * (q / 2 + s))) = !d (2 * s)
      rw [hH, hH, show 2 * (q / 2 + s) = 2 * s + q by omega, ha, hd]
      cases a (2 * s) <;> cases d (2 * s) <;> rfl)]
    rw [xr_not]
    rfl
  intro t
  rw [integral hzs' t (4 * q), xr_window hGp t, step1, step2, step3]

/-- **Mod-4 form** of the even-tick parity. -/
theorem E_mod4 (q : Nat) (hq : q % 4 = 0) (d h : Nat → Bool) (hs : ∀ t, d (t + 1) = xor (d t) (h t)) :
    E q d = xr (fun s => xor (h (4 * s)) (h (4 * s + 1))) (q / 4) := by
  unfold E
  rw [show q / 2 = 2 * (q / 4) by omega, xr_pairs]
  apply xr_congr
  intro s _
  show xor (d (2 * (2 * s))) (d (2 * (2 * s + 1))) = xor (h (4 * s)) (h (4 * s + 1))
  rw [show 2 * (2 * s) = 4 * s by omega, show 2 * (2 * s + 1) = 4 * s + 1 + 1 by omega, hs (4 * s + 1), hs (4 * s)]
  cases d (4 * s) <;> cases h (4 * s) <;> cases h (4 * s + 1) <;> rfl

/-- If `d` complements at `q/2`, the even-tick parity is `parity (q/4)`. -/
theorem E_of_antiperiod (q : Nat) (hq : q % 4 = 0) (d : Nat → Bool) (hd : ∀ t, d (t + q / 2) = !d t) :
    E q d = parity (q / 4) := by
  unfold E
  rw [show q / 2 = q / 4 + q / 4 by omega, xr_halves]
  rw [xr_congr (q / 4) (g := fun _ => true) (fun s _ => by
    show xor (d (2 * s)) (d (2 * (q / 4 + s))) = true
    rw [show 2 * (q / 4 + s) = 2 * s + q / 2 by omega, hd]
    cases d (2 * s) <;> rfl)]
  exact xr_true (q / 4)

theorem eta_of_antiperiod (q : Nat) (hq : q % 4 = 0) (d : Nat → Bool) (hd : ∀ t, d (t + q / 2) = !d t) :
    eta q d = xor (parity (q / 2)) (parity (q / 4)) := by
  unfold eta; rw [E_of_antiperiod q hq d hd]

/-- **The 11011 exclusion**: for `q ≡ 0 mod 8`, a `d` that doubled into `q` gives `eta = false`. -/
theorem eta_false_of_antiperiod (q : Nat) (hq : q % 8 = 0) (d : Nat → Bool)
    (hd : ∀ t, d (t + q / 2) = !d t) : eta q d = false := by
  rw [eta_of_antiperiod q (by omega) d hd]
  unfold parity
  have h1 : (q / 2) % 2 = 0 := by omega
  have h2 : (q / 4) % 2 = 0 := by omega
  simp [h1, h2]

/-- The exception at `q = 4`. -/
theorem eta_four (d : Nat → Bool) (hd : ∀ t, d (t + 2) = !d t) : eta 4 d = true := by
  rw [eta_of_antiperiod 4 (by decide) d hd]
  decide

/-- If `d` has period `q/2`, the even-tick parity vanishes. -/
theorem E_of_period_half (q : Nat) (hq : q % 4 = 0) (d : Nat → Bool) (hd : ∀ t, d (t + q / 2) = d t) :
    E q d = false := by
  unfold E
  rw [show q / 2 = q / 4 + q / 4 by omega, xr_halves]
  rw [xr_congr (q / 4) (g := fun _ => false) (fun s _ => by
    show xor (d (2 * s)) (d (2 * (q / 4 + s))) = false
    rw [show 2 * (q / 4 + s) = 2 * s + q / 2 by omega, hd]
    cases d (2 * s) <;> rfl)]
  exact xr_false (q / 4)

theorem eta_false_of_period_half (q : Nat) (hq : q % 4 = 0) (d : Nat → Bool)
    (hd : ∀ t, d (t + q / 2) = d t) : eta q d = false := by
  unfold eta
  rw [E_of_period_half q hq d hd]
  unfold parity
  have h1 : (q / 2) % 2 = 0 := by omega
  simp [h1]

/-! ### Actual right diagonals -/

/-- Right diagonal `j` of the kit's evolution: `D j t = x_t (t - j)`. -/
def rightDiag (x : Int → Bool) (j : Int) (t : Nat) : Bool := Rule30Realization.evol x t ((t : Int) - j)

theorem rightDiag_step (x : Int → Bool) (j : Int) (t : Nat) :
    rightDiag x j (t + 1) = xor (rightDiag x j t) (rightDiag x (j - 1) t || rightDiag x (j - 2) t) := by
  unfold rightDiag
  show Rule30Jen.rule (Rule30Realization.evol x t (((t + 1 : Nat) : Int) - j - 1))
      (Rule30Realization.evol x t (((t + 1 : Nat) : Int) - j))
      (Rule30Realization.evol x t (((t + 1 : Nat) : Int) - j + 1)) = _
  unfold Rule30Jen.rule
  congr 1
  · congr 1; omega
  · congr 1 <;> congr 1 <;> omega

/-- **The 101 shift law on actual right diagonals.** -/
theorem rightDiag_shift_law (x : Int → Bool) (j : Int) (q : Nat) (hq : q % 2 = 0)
    (hd : ∀ t, rightDiag x (j - 1) (t + q) = rightDiag x (j - 1) t)
    (ha : ∀ t, rightDiag x j (t + q) = !rightDiag x j t)
    (hb : ∀ t, rightDiag x (j + 1) (t + 2 * q) = rightDiag x (j + 1) t)
    (hc : ∀ t, rightDiag x (j + 2) (t + 2 * q) = !rightDiag x (j + 2) t) :
    ∀ t, rightDiag x (j + 3) (t + 4 * q) = xor (rightDiag x (j + 3) t) (eta q (rightDiag x (j - 1))) := by
  apply shift_law q hq (rightDiag x (j - 1)) (rightDiag x j) (rightDiag x (j + 1)) (rightDiag x (j + 2))
    (rightDiag x (j + 3)) hd ha hb hc
  · intro t
    have := rightDiag_step x (j + 1) t
    rwa [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega] at this
  · intro t
    have := rightDiag_step x (j + 3) t
    rwa [show j + 3 - 1 = j + 2 by omega, show j + 3 - 2 = j + 1 by omega] at this

/-! ### Doubling-Word Exclusion Laws, Unconditional `8q`-Periodicity, and Actual Right-Diagonal Profiles -/

/-- **Two-Period Cancellation of Running Shift (`running_shift_double`):** for any `p`-periodic
forcing `g`, two consecutive windows of length `p` cancel in XOR, so `D (t + 2 * p) = D t`. -/
theorem running_shift_double {D g : Nat → Bool} {p : Nat}
    (hs : ∀ t, D (t + 1) = xor (D t) (g t))
    (hg : ∀ t, g (t + p) = g t) (t : Nat) :
    D (t + 2 * p) = D t := by
  have h1 := running_shift hs hg (t + p)
  have h2 := running_shift hs hg t
  rw [show t + 2 * p = (t + p) + p by omega, h1, h2]
  cases D t <;> cases xr g p <;> rfl

/-- **Antiperiod-to-Period Doubling of `d` (`period_of_antiperiod_half`):** if `q` is even and `d`
complements at `q / 2`, then `d` is `q`-periodic (`d (t + q) = d t`). -/
theorem period_of_antiperiod_half (q : Nat) (hq : q % 2 = 0) (d : Nat → Bool)
    (hd : ∀ t, d (t + q / 2) = !d t) (t : Nat) :
    d (t + q) = d t := by
  have h1 := hd (t + q / 2)
  have h2 := hd t
  rw [show t + q = (t + q / 2) + q / 2 by omega, h1, h2, Bool.not_not]

/-- **Period-Half-to-Period Doubling of `d` (`period_of_period_half`):** if `q` is even and `d` has
period `q / 2`, then `d` has period `q` (`d (t + q) = d t`). -/
theorem period_of_period_half (q : Nat) (hq : q % 2 = 0) (d : Nat → Bool)
    (hd : ∀ t, d (t + q / 2) = d t) (t : Nat) :
    d (t + q) = d t := by
  have h1 := hd (t + q / 2)
  have h2 := hd t
  rw [show t + q = (t + q / 2) + q / 2 by omega, h1, h2]

/-- **Unconditional `8q`-Periodicity under the 101 Shift Law (`shift_law_period_eight_q`):** under
the hypotheses of `shift_law`, `z` is unconditionally `8q`-periodic (`z (t + 8 * q) = z t`)
regardless of the value of `eta q d`. -/
theorem shift_law_period_eight_q (q : Nat) (hq : q % 2 = 0) (d a b c z : Nat → Bool)
    (hd : ∀ t, d (t + q) = d t) (ha : ∀ t, a (t + q) = !a t)
    (hb : ∀ t, b (t + 2 * q) = b t) (hc : ∀ t, c (t + 2 * q) = !c t)
    (hbs : ∀ t, b (t + 1) = xor (b t) (a t || d t))
    (hzs : ∀ t, z (t + 1) = xor (z t) (c t || b t)) (t : Nat) :
    z (t + 8 * q) = z t := by
  have h1 := shift_law q hq d a b c z hd ha hb hc hbs hzs (t + 4 * q)
  have h2 := shift_law q hq d a b c z hd ha hb hc hbs hzs t
  rw [show t + 8 * q = (t + 4 * q) + 4 * q by omega, h1, h2]
  cases z t <;> cases eta q d <;> rfl

/-- **Abstract 11011 Exclusion (`shift_law_period_four_q_of_antiperiod`):** when `q ≡ 0 (mod 8)` and
`d` complements at `q / 2`, the 101 shift law forces `z` to have period `4q` (`z (t + 4 * q) = z t`),
preventing a period doubling at `z`. -/
theorem shift_law_period_four_q_of_antiperiod (q : Nat) (hq : q % 8 = 0) (d a b c z : Nat → Bool)
    (hd : ∀ t, d (t + q / 2) = !d t) (ha : ∀ t, a (t + q) = !a t)
    (hb : ∀ t, b (t + 2 * q) = b t) (hc : ∀ t, c (t + 2 * q) = !c t)
    (hbs : ∀ t, b (t + 1) = xor (b t) (a t || d t))
    (hzs : ∀ t, z (t + 1) = xor (z t) (c t || b t)) (t : Nat) :
    z (t + 4 * q) = z t := by
  have hdq := period_of_antiperiod_half q (by omega) d hd
  have hsl := shift_law q (by omega) d a b c z hdq ha hb hc hbs hzs t
  have heta := eta_false_of_antiperiod q hq d hd
  rw [hsl, heta, Bool.xor_false]

/-- **Abstract 01011 Exclusion (`shift_law_period_four_q_of_period_half`):** when `q ≡ 0 (mod 4)`
and `d` has period `q / 2`, the 101 shift law forces `z` to have period `4q` (`z (t + 4 * q) = z t`). -/
theorem shift_law_period_four_q_of_period_half (q : Nat) (hq : q % 4 = 0) (d a b c z : Nat → Bool)
    (hd : ∀ t, d (t + q / 2) = d t) (ha : ∀ t, a (t + q) = !a t)
    (hb : ∀ t, b (t + 2 * q) = b t) (hc : ∀ t, c (t + 2 * q) = !c t)
    (hbs : ∀ t, b (t + 1) = xor (b t) (a t || d t))
    (hzs : ∀ t, z (t + 1) = xor (z t) (c t || b t)) (t : Nat) :
    z (t + 4 * q) = z t := by
  have hdq := period_of_period_half q (by omega) d hd
  have hsl := shift_law q (by omega) d a b c z hdq ha hb hc hbs hzs t
  have heta := eta_false_of_period_half q hq d hd
  rw [hsl, heta, Bool.xor_false]

/-- **The `q = 4` Antiperiod-16 Doubling Law (`shift_law_antiperiod_sixteen_at_four`):** at `q = 4`,
if `d` complements at `2`, `a` complements at `4`, `b` has period `8`, and `c` complements at `8`,
then `z` complements at `16` (`z (t + 16) = !z t`). -/
theorem shift_law_antiperiod_sixteen_at_four (d a b c z : Nat → Bool)
    (hd : ∀ t, d (t + 2) = !d t) (ha : ∀ t, a (t + 4) = !a t)
    (hb : ∀ t, b (t + 8) = b t) (hc : ∀ t, c (t + 8) = !c t)
    (hbs : ∀ t, b (t + 1) = xor (b t) (a t || d t))
    (hzs : ∀ t, z (t + 1) = xor (z t) (c t || b t)) (t : Nat) :
    z (t + 16) = !z t := by
  have hdq := period_of_antiperiod_half 4 (by decide) d hd
  have hsl := shift_law 4 (by decide) d a b c z hdq ha hb hc hbs hzs t
  have heta := eta_four d hd
  rw [show t + 16 = t + 4 * 4 by omega, hsl, heta, Bool.xor_true]

/-- **Actual Right-Diagonal Unconditional `8q`-Periodicity (`rightDiag_period_eight_q`):** under the
hypotheses of `rightDiag_shift_law`, `rightDiag x (j + 3)` has period `8 * q`. -/
theorem rightDiag_period_eight_q (x : Int → Bool) (j : Int) (q : Nat) (hq : q % 2 = 0)
    (hd : ∀ t, rightDiag x (j - 1) (t + q) = rightDiag x (j - 1) t)
    (ha : ∀ t, rightDiag x j (t + q) = !rightDiag x j t)
    (hb : ∀ t, rightDiag x (j + 1) (t + 2 * q) = rightDiag x (j + 1) t)
    (hc : ∀ t, rightDiag x (j + 2) (t + 2 * q) = !rightDiag x (j + 2) t) (t : Nat) :
    rightDiag x (j + 3) (t + 8 * q) = rightDiag x (j + 3) t := by
  have h1 := rightDiag_shift_law x j q hq hd ha hb hc (t + 4 * q)
  have h2 := rightDiag_shift_law x j q hq hd ha hb hc t
  rw [show t + 8 * q = (t + 4 * q) + 4 * q by omega, h1, h2]
  cases rightDiag x (j + 3) t <;> cases eta q (rightDiag x (j - 1)) <;> rfl

/-- **Actual Right-Diagonal 11011 Exclusion (`rightDiag_period_four_q_of_antiperiod_mod8`):** for
`q ≡ 0 (mod 8)`, if `rightDiag x (j - 1)` complements at `q / 2`, `rightDiag x j` complements at `q`,
`rightDiag x (j + 1)` has period `2 * q`, and `rightDiag x (j + 2)` complements at `2 * q`, then
`rightDiag x (j + 3)` has period `4 * q`. -/
theorem rightDiag_period_four_q_of_antiperiod_mod8 (x : Int → Bool) (j : Int) (q : Nat) (hq : q % 8 = 0)
    (hd : ∀ t, rightDiag x (j - 1) (t + q / 2) = !rightDiag x (j - 1) t)
    (ha : ∀ t, rightDiag x j (t + q) = !rightDiag x j t)
    (hb : ∀ t, rightDiag x (j + 1) (t + 2 * q) = rightDiag x (j + 1) t)
    (hc : ∀ t, rightDiag x (j + 2) (t + 2 * q) = !rightDiag x (j + 2) t) (t : Nat) :
    rightDiag x (j + 3) (t + 4 * q) = rightDiag x (j + 3) t := by
  have hdq := period_of_antiperiod_half q (by omega) (rightDiag x (j - 1)) hd
  have hsl := rightDiag_shift_law x j q (by omega) hdq ha hb hc t
  have heta := eta_false_of_antiperiod q hq (rightDiag x (j - 1)) hd
  rw [hsl, heta, Bool.xor_false]

/-- **Actual Right-Diagonal 01011 Exclusion (`rightDiag_period_four_q_of_period_half`):** for
`q ≡ 0 (mod 4)`, if `rightDiag x (j - 1)` has period `q / 2`, `rightDiag x j` complements at `q`,
`rightDiag x (j + 1)` has period `2 * q`, and `rightDiag x (j + 2)` complements at `2 * q`, then
`rightDiag x (j + 3)` has period `4 * q`. -/
theorem rightDiag_period_four_q_of_period_half (x : Int → Bool) (j : Int) (q : Nat) (hq : q % 4 = 0)
    (hd : ∀ t, rightDiag x (j - 1) (t + q / 2) = rightDiag x (j - 1) t)
    (ha : ∀ t, rightDiag x j (t + q) = !rightDiag x j t)
    (hb : ∀ t, rightDiag x (j + 1) (t + 2 * q) = rightDiag x (j + 1) t)
    (hc : ∀ t, rightDiag x (j + 2) (t + 2 * q) = !rightDiag x (j + 2) t) (t : Nat) :
    rightDiag x (j + 3) (t + 4 * q) = rightDiag x (j + 3) t := by
  have hdq := period_of_period_half q (by omega) (rightDiag x (j - 1)) hd
  have hsl := rightDiag_shift_law x j q (by omega) hdq ha hb hc t
  have heta := eta_false_of_period_half q hq (rightDiag x (j - 1)) hd
  rw [hsl, heta, Bool.xor_false]

/-- **Actual Right-Diagonal `q = 4` Antiperiod-16 Law (`rightDiag_antiperiod_sixteen_at_four`):** at
`q = 4`, if `rightDiag x (j - 1)` complements at `2`, `rightDiag x j` complements at `4`,
`rightDiag x (j + 1)` has period `8`, and `rightDiag x (j + 2)` complements at `8`, then
`rightDiag x (j + 3)` complements at `16` (`rightDiag x (j + 3) (t + 16) = !rightDiag x (j + 3) t`). -/
theorem rightDiag_antiperiod_sixteen_at_four (x : Int → Bool) (j : Int)
    (hd : ∀ t, rightDiag x (j - 1) (t + 2) = !rightDiag x (j - 1) t)
    (ha : ∀ t, rightDiag x j (t + 4) = !rightDiag x j t)
    (hb : ∀ t, rightDiag x (j + 1) (t + 8) = rightDiag x (j + 1) t)
    (hc : ∀ t, rightDiag x (j + 2) (t + 8) = !rightDiag x (j + 2) t) (t : Nat) :
    rightDiag x (j + 3) (t + 16) = !rightDiag x (j + 3) t := by
  have hdq := period_of_antiperiod_half 4 (by decide) (rightDiag x (j - 1)) hd
  have hsl := rightDiag_shift_law x j 4 (by decide) hdq ha hb hc t
  have heta := eta_four (rightDiag x (j - 1)) hd
  rw [show t + 16 = t + 4 * 4 by omega, hsl, heta, Bool.xor_true]

end Ruliology.CellularAutomata.Rule30RightProfiles
