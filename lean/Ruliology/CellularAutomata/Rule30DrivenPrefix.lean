module

public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30SpacingRenormalization

/-!
# Packed prefixes of the alternating-driven right half

The packed update represents spatial cells at positions 1,2,..., in low to
high bits. The prefix agreement lemmas retain the exact dependence on the
unrepresented tail. No finite-prefix observation is assumed to be invariant.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DrivenPrefix

open Rule30Jen Rule30Ether Rule30PeriodTwoCoupled Rule30PeriodTwoSideways

def step (b : Bool) (a : Nat) : Nat :=
  ((a <<< 1) ||| b.toNat) ^^^ (a ||| (a >>> 1))

theorem step_bit (b : Bool) (a j : Nat) :
    (step b a).testBit j = xor (if j=0 then b else a.testBit (j-1))
      (a.testBit j || a.testBit (j+1)) := by
  simp only [step,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight,Nat.testBit_bool_toNat]
  cases j <;> simp [Nat.add_comm]

theorem step_agree (b : Bool) {a c k : Nat}
    (h : ∀ j, j<k+1 → a.testBit j=c.testBit j) :
    ∀ j, j<k → (step b a).testBit j=(step b c).testBit j := by
  intro j hj
  rw [step_bit,step_bit,h j (by omega),h (j+1) (by omega)]
  by_cases h0 : j=0
  · simp [h0]
  · simp [h0,h (j-1) (by omega)]

def packed (c : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => step (c t) (packed c a t)

theorem packed_sound (c R : Nat → Bool) (a : Nat)
    (ha : ∀ j, a.testBit j=R (j+1)) : ∀ t j,
    (packed c a t).testBit j=drv c R t (j+1) := by
  intro t
  induction t with
  | zero => intro j; simpa [packed,drv] using ha j
  | succ t ih =>
      intro j
      rw [packed,step_bit]
      cases j with
      | zero => simp [drv,rule,ih,drv_col0]
      | succ j => simp [drv,rule,ih,Nat.add_assoc]

def double (a : Nat) : Nat := step true (step false a)

def white : Nat → Nat
  | 0 => 1
  | n+1 => double (white n)

theorem packed_white : ∀ n, packed altCol 0 (2*n+1)=white n
  | 0 => by decide
  | n+1 => by
      rw [show 2*(n+1)+1=(2*n+1+1)+1 by omega,packed,packed]
      rw [show 2*n+1+1=2*(n+1) by omega,altCol_even,altCol_odd,packed_white]
      rfl

theorem white_sound (n j : Nat) :
    (white n).testBit j=drv altCol empty (2*n+1) (j+1) := by
  rw [← packed_white]
  exact packed_sound altCol empty 0 (by intro j; simp [empty]) (2*n+1) j

theorem white_gate (n : Nat) : (white n).testBit 0=u empty n := white_sound n 0

theorem double_agree {a c k : Nat}
    (h : ∀ j, j<k+2 → a.testBit j=c.testBit j) :
    ∀ j, j<k → (double a).testBit j=(double c).testBit j := by
  exact step_agree true (step_agree false (by intro j hj; exact h j (by omega)))

def iterate (a : Nat) : Nat → Nat
  | 0 => a
  | n+1 => double (iterate a n)

theorem iterate_agree : ∀ n {a c k : Nat},
    (∀ j, j<k+2*n → a.testBit j=c.testBit j) →
    ∀ j, j<k → (iterate a n).testBit j=(iterate c n).testBit j
  | 0,a,c,k,h => by simpa [iterate] using h
  | n+1,a,c,k,h => by
      apply double_agree
      apply iterate_agree n
      intro j hj
      exact h j (by omega)

theorem iterate_white (r n : Nat) : iterate (white r) n=white (r+n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate,ih,show r+(n+1)=(r+n)+1 by omega,white]

theorem double_prefix (a k : Nat) : double a % 2^k=double (a % 2^(k+2)) % 2^k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and]
    apply double_agree (k:=k)
    · intro i hi
      rw [Nat.testBit_mod_two_pow]
      simp [hi]
    · exact hj
  · simp [hj]

theorem iterate_mod_bit (a k n j : Nat) (hj : j+2*n<k) :
    (iterate (a % 2^k) n).testBit j=(iterate a n).testBit j := by
  apply iterate_agree n (k:=j+1)
  · intro i hi
    rw [Nat.testBit_mod_two_pow]
    simp [show i<k by omega]
  · omega

/-- The local gate window needed for exact spacings three or five. -/
def Window (f : Nat → Bool) (r : Nat) : Prop :=
  (f r && f (r+1))=false ∧ (f r && f (r+2))=false ∧
  (f r=true →
    (f (r+3)=true ∧ f (r+4)=false ∧ f (r+5)=false) ∨
    (f (r+3)=false ∧ f (r+4)=false ∧ f (r+5)=true)) ∧
  (f r || f (r+1) || f (r+2) || f (r+3) || f (r+4) || f (r+5))=true

instance (f : Nat → Bool) (r : Nat) : Decidable (Window f r) := inferInstanceAs
  (Decidable ((f r && f (r+1))=false ∧ (f r && f (r+2))=false ∧
  (f r=true →
    (f (r+3)=true ∧ f (r+4)=false ∧ f (r+5)=false) ∨
    (f (r+3)=false ∧ f (r+4)=false ∧ f (r+5)=true)) ∧
  (f r || f (r+1) || f (r+2) || f (r+3) || f (r+4) || f (r+5))=true))

def Observe (a : Nat) : Prop := Window (fun n => (iterate a n).testBit 0) 0

instance (a : Nat) : Decidable (Observe a) := inferInstanceAs
  (Decidable (Window (fun n => (iterate a n).testBit 0) 0))

theorem observe_trim (a : Nat) : Observe (a % 2^18) ↔ Observe a := by
  simp only [Observe,Window,Nat.zero_add]
  rw [iterate_mod_bit a 18 0 0 (by decide),iterate_mod_bit a 18 1 0 (by decide),
    iterate_mod_bit a 18 2 0 (by decide),iterate_mod_bit a 18 3 0 (by decide),
    iterate_mod_bit a 18 4 0 (by decide),iterate_mod_bit a 18 5 0 (by decide)]

/-! ## Exact 5-periodicity of 3-gap-free `Window` stretches, quantitative `free_bits_clock` bounds on 3-gap droughts, 8-step 3-gap spacing, and `Psi R` renormalization -/

/-- **`Window` implies `Spaced` (`spaced_of_window`):**
if `Window f r` holds at every `r : Nat`, then `Rule30SpacingRenormalization.Spaced f` holds. -/
theorem spaced_of_window {f : Nat → Bool} (hw : ∀ r, Window f r) :
    Rule30SpacingRenormalization.Spaced f :=
  fun r => ⟨(hw r).1, (hw r).2.1⟩

/-- **Exact Stepwise Period-5 Forcing in 3-Gap-Free `Window` Stretches (`window_step_five_of_no_gap_three`):**
if `Window f` holds on `[b, b + 5]` and neither `b + 1` nor `b + 3` starts a gap of `3`
(`(f (b + 1) && f (b + 4)) = false` and `(f (b + 3) && f (b + 6)) = false`), then `f (b + 6) = f (b + 1)`. -/
theorem window_step_five_of_no_gap_three (f : Nat → Bool) (b : Nat)
    (hw0 : Window f b) (hw1 : Window f (b + 1)) (hw2 : Window f (b + 2))
    (hw3 : Window f (b + 3)) (hw4 : Window f (b + 4)) (hw5 : Window f (b + 5))
    (hn1 : (f (b + 1) && f (b + 4)) = false)
    (hn3 : (f (b + 3) && f (b + 6)) = false) :
    f (b + 6) = f (b + 1) := by
  unfold Window at hw0 hw1 hw2 hw3 hw4 hw5
  simp only [Nat.add_assoc] at hw0 hw1 hw2 hw3 hw4 hw5 hn1 hn3
  cases h0 : f b <;> cases h1 : f (b + 1) <;> cases h2 : f (b + 2) <;>
    cases h3 : f (b + 3) <;> cases h4 : f (b + 4) <;> cases h5 : f (b + 5) <;>
    cases h6 : f (b + 6) <;> simp_all

/-- **Quantitative `free_bits_clock` Upper Bound on 3-Gap Droughts (`no_gap_three_clock_bound`):**
let `L` be a constrained start (`Rule30ZeroBoundary.InX L`) with last black cell at depth `m ≥ 1`,
and let `G s := !Rule30ZeroBoundary.zrow L (2 * s + 1) 1`. If `Window G` holds on `[s0, s0 + ℓ + 5]`
and no 3-gap `(G s && G (s + 3)) = true` occurs for `s ∈ [s0 + 1, s0 + ℓ + 3]`, then
`2 * ℓ + 2 ≤ 2 * (s0 + 1) + m + 20`. -/
theorem no_gap_three_clock_bound {L : Nat → Bool} {m : Nat}
    (hm : 1 ≤ m) (hedge : L m = true) (hfin : ∀ k, m < k → L k = false)
    (hX : Rule30ZeroBoundary.InX L) (s0 ℓ : Nat)
    (hw : ∀ s, s0 ≤ s → s ≤ s0 + ℓ + 5 → Window (fun r => !Rule30ZeroBoundary.zrow L (2 * r + 1) 1) s)
    (hno3 : ∀ s, s0 + 1 ≤ s → s ≤ s0 + ℓ + 3 →
      ((!Rule30ZeroBoundary.zrow L (2 * s + 1) 1) &&
       (!Rule30ZeroBoundary.zrow L (2 * (s + 3) + 1) 1)) = false) :
    2 * ℓ + 2 ≤ 2 * (s0 + 1) + m + 20 := by
  have hper : ∀ s, s0 + 1 ≤ s → s + 5 ≤ s0 + 1 + ℓ →
      Rule30ZeroBoundary.zrow L (2 * (s + 5) + 1) 1 = Rule30ZeroBoundary.zrow L (2 * s + 1) 1 := by
    intro s hs1 hs2
    have hstep := window_step_five_of_no_gap_three
      (fun r => !Rule30ZeroBoundary.zrow L (2 * r + 1) 1) (s - 1)
      (hw (s - 1) (by omega) (by omega))
      (hw (s - 1 + 1) (by omega) (by omega))
      (hw (s - 1 + 2) (by omega) (by omega))
      (hw (s - 1 + 3) (by omega) (by omega))
      (hw (s - 1 + 4) (by omega) (by omega))
      (hw (s - 1 + 5) (by omega) (by omega))
      (by rw [show s - 1 + 1 = s by omega, show s - 1 + 4 = s + 3 by omega]; exact hno3 s (by omega) (by omega))
      (by rw [show s - 1 + 3 = s + 2 by omega, show s - 1 + 6 = s + 2 + 3 by omega]; exact hno3 (s + 2) (by omega) (by omega))
    rw [show s - 1 + 6 = s + 5 by omega, show s - 1 + 1 = s by omega] at hstep
    revert hstep
    cases Rule30ZeroBoundary.zrow L (2 * (s + 5) + 1) 1 <;>
      cases Rule30ZeroBoundary.zrow L (2 * s + 1) 1 <;> decide
  have hclk := Rule30ZeroBoundary.free_bits_clock hm hedge hfin hX
    (s₀ := s0 + 1) (ℓ := ℓ) (p := 5) (by decide) hper
  omega

/-- **Cofinal Existence of 3-Gaps for Any Finitely Supported Constrained Start (`cofinal_gap_three_of_finSupp_InX`):**
if `FinSupp L` and `InX L` hold and `G s := !zrow L (2 * s + 1) 1` satisfies `Window G s` from `s0` on,
then for every `N : Nat` there exists `s ≥ N` such that `G s = true ∧ G (s + 3) = true`. -/
theorem cofinal_gap_three_of_finSupp_InX {L : Nat → Bool}
    (hfin : Rule30ZeroBoundary.FinSupp L) (hX : Rule30ZeroBoundary.InX L)
    {s0 : Nat} (hw : ∀ s, s0 ≤ s → Window (fun r => !Rule30ZeroBoundary.zrow L (2 * r + 1) 1) s)
    (N : Nat) :
    ∃ s, N ≤ s ∧
      !Rule30ZeroBoundary.zrow L (2 * s + 1) 1 = true ∧
      !Rule30ZeroBoundary.zrow L (2 * (s + 3) + 1) 1 = true := by
  apply Classical.byContradiction
  intro hneg
  obtain ⟨W, hW⟩ := hfin
  obtain ⟨m, hm, hedge, hz⟩ := Rule30ZeroBoundary.last_black (show L 1 = true from hX 0) W hW
  let S := max s0 N
  let ℓ := S + m + 12
  have hno3 : ∀ s, S + 1 ≤ s → s ≤ S + ℓ + 3 →
      ((!Rule30ZeroBoundary.zrow L (2 * s + 1) 1) &&
       (!Rule30ZeroBoundary.zrow L (2 * (s + 3) + 1) 1)) = false := by
    intro s hs1 _
    cases ha : !Rule30ZeroBoundary.zrow L (2 * s + 1) 1 with
    | false => rfl
    | true =>
      cases hb : !Rule30ZeroBoundary.zrow L (2 * (s + 3) + 1) 1 with
      | false => rfl
      | true =>
        exfalso
        have hgeN : N ≤ s := by omega
        exact hneg ⟨s, hgeN, ha, hb⟩
  have hbd := no_gap_three_clock_bound hm hedge hz hX S ℓ
    (fun s hs _ => hw s (by omega)) hno3
  omega

/-- **Exact 8-Step Minimum Spacing Between 3-Gaps under No-`33` (`gap_three_spacing_eight_of_no_33`):**
if `Window f r` and `Window f (r + 3)` hold and `f` does not read `[3, 3]` at `r`
(`(f r && f (r + 3) && f (r + 6)) = false`), then whenever `f r = true ∧ f (r + 3) = true`,
the next black cell after `r + 3` is at `r + 8` and no 3-gap `(f (r + i) && f (r + i + 3)) = true`
can start at any offset `1 ≤ i ≤ 7`. -/
theorem gap_three_spacing_eight_of_no_33 (f : Nat → Bool) (r : Nat)
    (hw0 : Window f r) (hw3 : Window f (r + 3))
    (hno33 : (f r && f (r + 3) && f (r + 6)) = false)
    (hr0 : f r = true) (hr3 : f (r + 3) = true) :
    f (r + 1) = false ∧ f (r + 2) = false ∧ f (r + 4) = false ∧
    f (r + 5) = false ∧ f (r + 6) = false ∧ f (r + 7) = false ∧ f (r + 8) = true ∧
    (∀ i, 1 ≤ i → i ≤ 7 → (f (r + i) && f (r + i + 3)) = false) := by
  unfold Window at hw0 hw3
  simp only [Nat.add_assoc] at hw0 hw3 hno33
  have h1245678 :
      f (r + 1) = false ∧ f (r + 2) = false ∧ f (r + 4) = false ∧
      f (r + 5) = false ∧ f (r + 6) = false ∧ f (r + 7) = false ∧ f (r + 8) = true := by
    cases h1 : f (r + 1) <;> cases h2 : f (r + 2) <;> cases h4 : f (r + 4) <;>
      cases h5 : f (r + 5) <;> cases h6 : f (r + 6) <;> cases h7 : f (r + 7) <;>
      cases h8 : f (r + 8) <;> simp_all
  rcases h1245678 with ⟨h1, h2, h4, h5, h6, h7, h8⟩
  refine ⟨h1, h2, h4, h5, h6, h7, h8, fun i hi1 hi7 => ?_⟩
  have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h1, Bool.false_and]
  · rw [h2, Bool.false_and]
  · rw [show r + 3 + 3 = r + 6 by omega, h6, Bool.and_false]
  · rw [h4, Bool.false_and]
  · rw [h5, Bool.false_and]
  · rw [h6, Bool.false_and]
  · rw [h7, Bool.false_and]

/-! ### Multi-Step `Theta` and `Psi R` Shift Conjugacy and 8-Depth Renormalization -/

/-- **`2 * k`-Step Shift Conjugacy for `Theta` (`Theta_shift_two_mul`):**
evolving `Theta f` for `2 * k` steps in the zero-boundary left half equals `Theta (fun s => f (k + s))`. -/
theorem Theta_shift_two_mul (f : Nat → Bool) :
    ∀ k : Nat, Rule30ZeroBoundary.zrow (Rule30ZeroBoundary.Theta f) (2 * k) =
      Rule30ZeroBoundary.Theta (fun s => f (k + s))
  | 0 => by
    have h0 := Rule30ZeroBoundary.zrow_zero_self (Rule30ZeroBoundary.Theta_wall f)
    simpa [Nat.zero_add] using h0
  | k + 1 => by
    funext d
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        Rule30ZeroBoundary.zrow_shift (Rule30ZeroBoundary.Theta f) (2 * k) 2 d,
        Theta_shift_two_mul f k,
        Rule30ZeroBoundary.two_step_shift]
    have hfun : (fun s => f (k + (s + 1))) = (fun s => f (k + 1 + s)) := by
      funext s; congr 1; omega
    rw [hfun]

/-- **`2 * k`-Step Shift Conjugacy for `Psi R` (`Psi_shift_two_mul`):**
evolving `Psi R` for `2 * k` steps in the zero-boundary left half equals `Theta (fun s => !u R (k + s))`. -/
theorem Psi_shift_two_mul (R : Nat → Bool) (k : Nat) :
    Rule30ZeroBoundary.zrow (Psi R) (2 * k) =
      Rule30ZeroBoundary.Theta (fun s => !u R (k + s)) :=
  Theta_shift_two_mul (fun s => !u R s) k

/-- **Direct 8-Depth Renormalization of `Psi R` under `Spaced` (`Psi_spaced_translate`):**
for any right half `R` and offset `s0 : Nat` such that `Spaced (fun r => u R (s0 + r))` holds,
`zrow (Psi R) (2 * (s0 + 1)) (m + 9) = Theta (fun s => !transform (fun r => u R (s0 + r)) (s + 1)) (m + 1)`. -/
theorem Psi_spaced_translate (R : Nat → Bool) (s0 : Nat)
    (hsp : Rule30SpacingRenormalization.Spaced (fun r => u R (s0 + r))) (m : Nat) :
    Rule30ZeroBoundary.zrow (Psi R) (2 * (s0 + 1)) (m + 9) =
      Rule30ZeroBoundary.Theta
        (fun s => !Rule30SpacingRenormalization.transform (fun r => u R (s0 + r)) (s + 1)) (m + 1) := by
  rw [Psi_shift_two_mul R (s0 + 1)]
  have hfun : (fun s => !u R (s0 + 1 + s)) = (fun s => !(fun r => u R (s0 + r)) (s + 1)) := by
    funext s; simp only [Nat.add_assoc, Nat.add_comm 1 s]
  rw [hfun]
  have hs := Rule30ZeroBoundary.recon_shift (Rule30SpacingRenormalization.boundary (fun r => u R (s0 + r))) 1 (m + 9) 0
  have hs' := Rule30ZeroBoundary.recon_shift
    (Rule30SpacingRenormalization.boundary (Rule30SpacingRenormalization.transform (fun r => u R (s0 + r)))) 1 (m + 1) 0
  rw [Nat.add_zero] at hs hs'
  have hb1 : (fun i => Rule30SpacingRenormalization.boundary (fun r => u R (s0 + r)) (i + 1)) =
      Rule30ZeroBoundary.alt (fun s => !(fun r => u R (s0 + r)) (s + 1)) := by
    funext t
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have he : t = 2 * (t / 2) := by omega
      rw [he, Rule30SpacingRenormalization.boundary_odd]
      unfold Rule30ZeroBoundary.alt; rw [ite_eq_left (by omega)]
    · have ho : t = 2 * (t / 2) + 1 := by omega
      rw [ho, show 2 * (t / 2) + 1 + 1 = 2 * (t / 2 + 1) by omega, Rule30SpacingRenormalization.boundary_even]
      unfold Rule30ZeroBoundary.alt; rw [ite_eq_right (by omega), show (2 * (t / 2) + 1) / 2 = t / 2 by omega]
  have hb2 : (fun i => Rule30SpacingRenormalization.boundary
        (Rule30SpacingRenormalization.transform (fun r => u R (s0 + r))) (i + 1)) =
      Rule30ZeroBoundary.alt
        (fun s => !Rule30SpacingRenormalization.transform (fun r => u R (s0 + r)) (s + 1)) := by
    funext t
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have he : t = 2 * (t / 2) := by omega
      rw [he, Rule30SpacingRenormalization.boundary_odd]
      unfold Rule30ZeroBoundary.alt; rw [ite_eq_left (by omega)]
    · have ho : t = 2 * (t / 2) + 1 := by omega
      rw [ho, show 2 * (t / 2) + 1 + 1 = 2 * (t / 2 + 1) by omega, Rule30SpacingRenormalization.boundary_even]
      unfold Rule30ZeroBoundary.alt; rw [ite_eq_right (by omega), show (2 * (t / 2) + 1) / 2 = t / 2 by omega]
  show Rule30ZeroBoundary.recon (Rule30ZeroBoundary.alt (fun s => !(fun r => u R (s0 + r)) (s + 1))) (m + 9) 0 =
    Rule30ZeroBoundary.recon
      (Rule30ZeroBoundary.alt (fun s => !Rule30SpacingRenormalization.transform (fun r => u R (s0 + r)) (s + 1))) (m + 1) 0
  rw [← hb1, ← hb2, ← hs, ← hs']
  exact Rule30SpacingRenormalization.reconstruction_translate (fun r => u R (s0 + r)) hsp m 1

/-- **Finite-Support Transfer from `Psi R` to the 8-Column Renormalized `Theta` (`finSupp_Theta_transform_of_finSupp_Psi`):**
if `FinSupp (Psi R)` holds and `Spaced (fun r => u R (s0 + r))` holds from `s0` on, then
`Theta (fun s => !transform (fun r => u R (s0 + r)) (s + 1))` is also finitely supported. -/
theorem finSupp_Theta_transform_of_finSupp_Psi (R : Nat → Bool) (s0 : Nat)
    (hsp : Rule30SpacingRenormalization.Spaced (fun r => u R (s0 + r)))
    (hfin : Rule30ZeroBoundary.FinSupp (Psi R)) :
    Rule30ZeroBoundary.FinSupp
      (Rule30ZeroBoundary.Theta
        (fun s => !Rule30SpacingRenormalization.transform (fun r => u R (s0 + r)) (s + 1))) := by
  obtain ⟨W, hW⟩ := hfin
  refine ⟨W + 2 * (s0 + 1) - 8, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [← Psi_spaced_translate R s0 hsp m]
  exact Rule30ZeroBoundary.zrow_fin hW (2 * (s0 + 1)) (m + 9) (by omega)

end Ruliology.CellularAutomata.Rule30DrivenPrefix
