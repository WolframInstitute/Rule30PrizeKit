module

public import Ruliology.CellularAutomata.Rule30WedgeParity

/-!
# The top coefficient of the center function

Every left-permutive elementary rule is `a ⊕ g(b, c)` with `g = γ ⊕ α b ⊕ β c ⊕ κ bc`
(`Rule30WedgeParity.Coef`). For a quadratic rule (`κ = 1`) and `n = m + 2`, `top_coefficient_rows` shows
that the number of initial rows on the window `[-n, n]` whose two leftmost cells `x(0, -n)` and
`x(0, -n + 1)` are white and whose center `x(n, 0)` is black is odd iff `1 ⊕ α ⊕ β = 1`, for every `γ`.
The coefficient of a monomial in the algebraic normal form of a Boolean function is the parity of the
number of assignments of the monomial's variables, the others set to `0`, on which the function is `1`.
So over `𝔽₂` the coefficient of `x_{-n+2} ⋯ x_n` in the center function `x(n, 0)` is `1 ⊕ α ⊕ β`: `1` for
Rule 30 (`rule30_top_coefficient`) and `0` for Rule 180 (`rule180_top_coefficient`). That this monomial
has the maximal degree `2n - 1` when `1 ⊕ α ⊕ β = 1` was observed for `n ≤ 6` and is not proved here.

The proof writes the diagram by its two boundary diagonals, the boundary word `bd` and the free word `q`
(`Rule30WedgeParity.Y`). The substitution `bd (t + 1) = Y 2 t ⊕ g (q t, bd t)` (`phi`) is triangular, so it
leaves the parity sum `psum` unchanged (`psum_tri`); it makes the array from index `1` on the array with
boundary `q` and free word `Y 2` (`Y_shift`, `Y_phi_shift`). The first bit `bd 0`, the rightmost cell,
enters the apex affinely with the multiplier product `Pq` (`phi_flip`). Summing it out leaves `Pq`
(`sum_bd`), which is `1` only for the constant free word `q = ¬β`. The remaining free bits form a
top-parity sum for that boundary (`sum_Hq`, from `Rule30WedgeParity.top_parity_quadratic`) in which the
extra white cell removes the newest bit, and the sum over `q` is `sum_q`: this is
`top_coefficient_quadratic`. The rows correspond to the seed words through the interleaved word
`z (2t) = bd t`, `z (2t + 1) = q t`: the cell `x(0, n - j) = Y j 0` is `z j` plus a function of the bits
before `j` (`Y_zdep`), so the map from the interleaved seed word to the row cells is again a triangular
substitution, and the reconstructed row has the seeds as its diagonals (`evolve_rowOfG`,
`psum_interleave`, `top_coefficient_rows`).

This is a statement about initial rows of width `2n + 1`, not about the single seed; Problems 1 to 3
stay open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30TopCoefficient

open Rule30WedgeParity

/-! ## Two general facts about the parity sum `psum` -/

/-- Prepend a bit: `cons b w 0 = b`, `cons b w (i + 1) = w i`. -/
def cons (b : Bool) (w : Nat → Bool) : Nat → Bool
  | 0 => b
  | i + 1 => w i

/-- Summing out the first bit. -/
theorem psum_first : ∀ (n : Nat) (F : (Nat → Bool) → Bool),
    psum 0 (n + 1) F
      = xor (psum 0 n (fun w => F (cons false w))) (psum 0 n (fun w => F (cons true w)))
  | 0, F => by
    have e : ∀ b, upd (fun _ => false) 0 b = cons b (fun _ => false) := by
      intro b; funext i; cases i <;> simp [upd, cons]
    show xor (F (upd (fun _ => false) (0 + 0) false)) (F (upd (fun _ => false) (0 + 0) true))
      = xor (F (cons false (fun _ => false))) (F (cons true (fun _ => false)))
    rw [Nat.add_zero, e, e]
  | n + 1, F => by
    have e : ∀ (c : Bool) (w : Nat → Bool) (b : Bool), upd (cons c w) (n + 1) b = cons c (upd w n b) := by
      intro c w b; funext i; cases i <;> simp [upd, cons]
    show xor (psum 0 (n + 1) (fun w => F (upd w (0 + (n + 1)) false)))
        (psum 0 (n + 1) (fun w => F (upd w (0 + (n + 1)) true)))
      = xor (psum 0 (n + 1) (fun w => F (cons false w))) (psum 0 (n + 1) (fun w => F (cons true w)))
    rw [psum_first n (fun w => F (upd w (0 + (n + 1)) false)),
      psum_first n (fun w => F (upd w (0 + (n + 1)) true))]
    show _ = xor (xor (psum 0 n (fun w => F (cons false (upd w (0 + n) false))))
          (psum 0 n (fun w => F (cons false (upd w (0 + n) true)))))
        (xor (psum 0 n (fun w => F (cons true (upd w (0 + n) false))))
          (psum 0 n (fun w => F (cons true (upd w (0 + n) true)))))
    simp only [Nat.zero_add, e]
    generalize psum 0 n (fun w => F (cons false (upd w n false))) = a
    generalize psum 0 n (fun w => F (cons false (upd w n true))) = b
    generalize psum 0 n (fun w => F (cons true (upd w n false))) = c
    generalize psum 0 n (fun w => F (cons true (upd w n true))) = d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- A triangular substitution of the summation variables does not change the parity sum:
`T w i = w i ⊕ h i w` with `h i` depending only on the bits before `i`. -/
theorem psum_tri (h : Nat → (Nat → Bool) → Bool)
    (hdep : ∀ i w w', (∀ j, j < i → w j = w' j) → h i w = h i w') :
    ∀ (n : Nat) (F : (Nat → Bool) → Bool),
      psum 0 n (fun w => F (fun i => if i < n then xor (w i) (h i w) else w i)) = psum 0 n F
  | 0, F => by
    show F (fun i => if i < 0 then _ else (fun _ => false) i) = F (fun _ => false)
    congr 1
  | n + 1, F => by
    have key : ∀ (w : Nat → Bool) (b : Bool),
        (fun i => if i < n + 1 then xor (upd w n b i) (h i (upd w n b)) else upd w n b i)
          = upd (fun i => if i < n then xor (w i) (h i w) else w i) n (xor b (h n w)) := by
      intro w b
      funext i
      by_cases h1 : i < n
      · have hi : i ≠ n := by omega
        have hh : h i (upd w n b) = h i w :=
          hdep i _ _ (fun j hj => upd_other w (by omega) b)
        simp [upd, hi, h1, hh, show i < n + 1 from by omega]
      · by_cases h2 : i = n
        · subst h2
          have hh : h i (upd w i b) = h i w :=
            hdep i _ _ (fun j hj => upd_other w (by omega) b)
          simp [upd, hh]
        · simp [upd, h2, h1, show ¬ i < n + 1 from by omega]
    show xor (psum 0 n (fun w => F (fun i => if i < n + 1 then xor (upd w (0 + n) false i) (h i (upd w (0 + n) false)) else upd w (0 + n) false i)))
        (psum 0 n (fun w => F (fun i => if i < n + 1 then xor (upd w (0 + n) true i) (h i (upd w (0 + n) true)) else upd w (0 + n) true i)))
      = psum 0 (n + 1) F
    simp only [Nat.zero_add, key]
    have pw : ∀ w : Nat → Bool,
        xor (F (upd (fun i => if i < n then xor (w i) (h i w) else w i) n (xor false (h n w))))
            (F (upd (fun i => if i < n then xor (w i) (h i w) else w i) n (xor true (h n w))))
          = (fun v => xor (F (upd v n false)) (F (upd v n true)))
              (fun i => if i < n then xor (w i) (h i w) else w i) := by
      intro w
      generalize h n w = x
      generalize (fun i => if i < n then xor (w i) (h i w) else w i) = v
      cases x <;> simp [Bool.xor_comm]
    rw [← psum_xor, show (fun w => xor (F (upd (fun i => if i < n then xor (w i) (h i w) else w i) n (xor false (h n w))))
            (F (upd (fun i => if i < n then xor (w i) (h i w) else w i) n (xor true (h n w)))))
        = fun w => (fun v => xor (F (upd v n false)) (F (upd v n true)))
              (fun i => if i < n then xor (w i) (h i w) else w i) from funext pw]
    rw [psum_tri h hdep n (fun v => xor (F (upd v n false)) (F (upd v n true))), psum_xor]
    simp only [psum, Nat.zero_add]

/-! ## Dropping the boundary diagonal -/

/-- Shifting the diagonals: the array with seeds `(bd, q)` at index `j + 1` is the array with seeds
`(q, Y 2)` at index `j`. -/
theorem Y_shift (p : Coef) (bd q : Nat → Bool) :
    ∀ j t, Y p bd q (j + 1) t = Y p q (fun t => Y p bd q 2 t) j t
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, t => by
    show xor (Y p bd q (j + 1) (t + 1)) (p.g (Y p bd q (j + 2) t) (Y p bd q (j + 1) t))
      = xor (Y p q (fun t => Y p bd q 2 t) j (t + 1))
          (p.g (Y p q (fun t => Y p bd q 2 t) (j + 1) t) (Y p q (fun t => Y p bd q 2 t) j t))
    rw [Y_shift p bd q j (t + 1), Y_shift p bd q (j + 1) t, Y_shift p bd q j t]

/-- `g` is affine in its second argument. -/
theorem g_affine (p : Coef) (b c d : Bool) :
    p.g b (xor c d) = xor (p.g b c) (d && xor p.β (p.κ && b)) := by
  cases p with
  | mk γ α β κ =>
    cases γ <;> cases α <;> cases β <;> cases κ <;> cases b <;> cases c <;> cases d <;> rfl

/-- The substitution `bd = phi q u`: `bd 0 = u 0` and `bd (i + 1) = u (i + 1) ⊕ g (q i, bd i)`, so that
`Y 2 t = u (t + 1)`. -/
def phi (p : Coef) (q u : Nat → Bool) : Nat → Bool
  | 0 => u 0
  | i + 1 => xor (u (i + 1)) (p.g (q i) (phi p q u i))

theorem phi_dep (p : Coef) (q : Nat → Bool) (u u' : Nat → Bool) :
    ∀ i, (∀ j, j ≤ i → u j = u' j) → phi p q u i = phi p q u' i
  | 0, h => h 0 (Nat.le_refl _)
  | i + 1, h => by
    show xor (u (i + 1)) (p.g (q i) (phi p q u i)) = xor (u' (i + 1)) (p.g (q i) (phi p q u' i))
    rw [h (i + 1) (Nat.le_refl _), phi_dep p q u u' i (fun j hj => h j (by omega))]

theorem Y_phi_two (p : Coef) (q u : Nat → Bool) (t : Nat) :
    Y p (phi p q u) q 2 t = u (t + 1) := by
  show xor (phi p q u (t + 1)) (p.g (q t) (phi p q u t)) = u (t + 1)
  show xor (xor (u (t + 1)) (p.g (q t) (phi p q u t))) (p.g (q t) (phi p q u t)) = u (t + 1)
  generalize p.g (q t) (phi p q u t) = c
  generalize u (t + 1) = a
  cases a <;> cases c <;> rfl

/-- The array with boundary `phi q u` at index `j + 1` is the array with seeds `(q, u ∘ succ)`. -/
theorem Y_phi_shift (p : Coef) (q u : Nat → Bool) (j t : Nat) :
    Y p (phi p q u) q (j + 1) t = Y p q (fun t => u (t + 1)) j t := by
  rw [Y_shift]
  have : (fun t => Y p (phi p q u) q 2 t) = fun t => u (t + 1) := funext (Y_phi_two p q u)
  rw [this]

/-- The product of the multipliers `β ⊕ κ q k`, `k < i`. -/
def Pq (p : Coef) (q : Nat → Bool) : Nat → Bool
  | 0 => true
  | i + 1 => Pq p q i && xor p.β (p.κ && q i)

theorem Pq_congr (p : Coef) (q q' : Nat → Bool) :
    ∀ i, (∀ k, k < i → q k = q' k) → Pq p q i = Pq p q' i
  | 0, _ => rfl
  | i + 1, h => by
    show (Pq p q i && xor p.β (p.κ && q i)) = (Pq p q' i && xor p.β (p.κ && q' i))
    rw [Pq_congr p q q' i (fun k hk => h k (by omega)), h i (by omega)]

/-- **The first bit enters affinely.** Flipping `u 0` changes `phi q u i` by `Pq q i`. -/
theorem phi_flip (p : Coef) (q u : Nat → Bool) :
    ∀ i, phi p q (upd u 0 true) i = xor (phi p q (upd u 0 false) i) (Pq p q i)
  | 0 => by simp [phi, Pq, upd]
  | i + 1 => by
    have ih := phi_flip p q u i
    show xor (upd u 0 true (i + 1)) (p.g (q i) (phi p q (upd u 0 true) i))
      = xor (xor (upd u 0 false (i + 1)) (p.g (q i) (phi p q (upd u 0 false) i)))
          (Pq p q i && xor p.β (p.κ && q i))
    rw [ih, g_affine]
    simp only [upd, show i + 1 ≠ 0 from by omega, ↓reduceIte]
    generalize u (i + 1) = a
    generalize p.g (q i) (phi p q (upd u 0 false) i) = c
    generalize (Pq p q i && xor p.β (p.κ && q i)) = d
    cases a <;> cases c <;> cases d <;> rfl

/-! ## The seed count with two white window cells -/

/-- The seed indicator for `n = m + 2`: apex `bd n = 1`, and the two leftmost window cells
`x(0, -n + 1) = Y (2n - 1) 0` and `x(0, -n) = Y (2n) 0` white. -/
def Fq (p : Coef) (m : Nat) (q bd : Nat → Bool) : Bool :=
  bd (m + 2) && (Y p bd q (2 * m + 3) 0 == false) && (Y p bd q (2 * m + 4) 0 == false)

theorem Fq_congr (p : Coef) (m : Nat) (q bd bd' : Nat → Bool) (h : ∀ i, i ≤ m + 2 → bd i = bd' i) :
    Fq p m q bd = Fq p m q bd' := by
  unfold Fq
  rw [h (m + 2) (Nat.le_refl _),
    Y_bd_congr p q bd bd' (2 * m + 3) 0 (fun i hi => h i (by omega)),
    Y_bd_congr p q bd bd' (2 * m + 4) 0 (fun i hi => h i (by omega))]

/-- The triangular term of the substitution. -/
def hfun (p : Coef) (q : Nat → Bool) : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | k + 1, w => p.g (q k) (phi p q w k)

theorem hfun_dep (p : Coef) (q : Nat → Bool) :
    ∀ i w w', (∀ j, j < i → w j = w' j) → hfun p q i w = hfun p q i w'
  | 0, _, _, _ => rfl
  | k + 1, w, w', h => by
    show p.g (q k) (phi p q w k) = p.g (q k) (phi p q w' k)
    rw [phi_dep p q w w' k (fun j hj => h j (by omega))]

theorem phi_eq_tri (p : Coef) (q w : Nat → Bool) : ∀ i, phi p q w i = xor (w i) (hfun p q i w)
  | 0 => by simp [phi, hfun]
  | k + 1 => rfl

theorem cons_upd (w : Nat → Bool) (b : Bool) : upd (cons false w) 0 b = cons b w := by
  funext i; cases i <;> simp [upd, cons]

/-- The part of the indicator that does not depend on the first substituted bit. -/
def Hq (p : Coef) (m : Nat) (q w : Nat → Bool) : Bool :=
  (Y p q w (2 * m + 2) 0 == false) && (Y p q w (2 * m + 3) 0 == false)

theorem Fq_phi (p : Coef) (m : Nat) (q w : Nat → Bool) (c : Bool) :
    Fq p m q (phi p q (cons c w)) = (phi p q (cons c w) (m + 2) && Hq p m q w) := by
  have h3 : Y p (phi p q (cons c w)) q (2 * m + 3) 0 = Y p q w (2 * m + 2) 0 :=
    Y_phi_shift p q (cons c w) (2 * m + 2) 0
  have h4 : Y p (phi p q (cons c w)) q (2 * m + 4) 0 = Y p q w (2 * m + 3) 0 :=
    Y_phi_shift p q (cons c w) (2 * m + 3) 0
  unfold Fq Hq
  rw [h3, h4, Bool.and_assoc]

/-- Summing out the substituted boundary leaves the multiplier product `Pq`. -/
theorem sum_bd (p : Coef) (m : Nat) (q : Nat → Bool) :
    psum 0 (m + 3) (fun bd => Fq p m q bd)
      = (Pq p q (m + 2) && psum 0 (m + 2) (Hq p m q)) := by
  have A := psum_tri (hfun p q) (hfun_dep p q) (m + 3) (fun bd => Fq p m q bd)
  have A' : psum 0 (m + 3) (fun bd => Fq p m q bd) = psum 0 (m + 3) (fun u => Fq p m q (phi p q u)) := by
    rw [← A]
    congr 1
    funext w
    apply Fq_congr
    intro i hi
    simp only [show i < m + 3 from by omega, ↓reduceIte, phi_eq_tri]
  rw [A', psum_first, ← psum_xor]
  have pw : ∀ w : Nat → Bool,
      xor (Fq p m q (phi p q (cons false w))) (Fq p m q (phi p q (cons true w)))
        = (Pq p q (m + 2) && Hq p m q w) := by
    intro w
    rw [Fq_phi, Fq_phi]
    have hf : phi p q (cons true w) (m + 2) = xor (phi p q (cons false w) (m + 2)) (Pq p q (m + 2)) := by
      have := phi_flip p q (cons false w) (m + 2)
      rwa [cons_upd, cons_upd] at this
    rw [hf]
    generalize phi p q (cons false w) (m + 2) = a
    generalize Pq p q (m + 2) = b
    generalize Hq p m q w = c
    cases a <;> cases b <;> cases c <;> rfl
  rw [show (fun w => xor (Fq p m q (phi p q (cons false w))) (Fq p m q (phi p q (cons true w))))
      = fun w => (Pq p q (m + 2) && Hq p m q w) from funext pw]
  exact psum_and_left 0 _ (m + 2) (Hq p m q)

/-- The remaining free word is a top-parity sum for the boundary `q`: the extra white cell
`x(0, -n)` is permutive in the newest free bit and removes it. -/
theorem sum_Hq (p : Coef) (hκ : p.κ = true) (m : Nat) (q : Nat → Bool) :
    psum 0 (m + 2) (Hq p m q) = xor p.α (q 0) := by
  have hD := Y_dep p q (m + 1) 0
  simp only [Nat.zero_add] at hD
  show xor (psum 0 (m + 1) (fun w => Hq p m q (upd w (0 + (m + 1)) false)))
      (psum 0 (m + 1) (fun w => Hq p m q (upd w (0 + (m + 1)) true))) = _
  rw [← psum_xor]
  have pw : ∀ w : Nat → Bool,
      xor (Hq p m q (upd w (0 + (m + 1)) false)) (Hq p m q (upd w (0 + (m + 1)) true))
        = (Y p q w (2 * m + 2) 0 == false) := by
    intro w
    simp only [Nat.zero_add]
    have e1 : ∀ b, Y p q (upd w (m + 1) b) (2 * m + 2) 0 = Y p q w (2 * m + 2) 0 :=
      fun b => hD.1 _ _ (fun i _ h2 => upd_other w (by omega) b)
    have e2 : ∀ b, xor (Y p q (upd w (m + 1) b) (2 * m + 3) 0) b
        = xor (Y p q w (2 * m + 3) 0) (w (m + 1)) := by
      intro b
      have := hD.2.2 (upd w (m + 1) b) w (fun i _ h2 => upd_other w (by omega) b)
      simp only [upd_same] at this
      exact this
    unfold Hq
    rw [e1, e1]
    have e2f := e2 false
    have e2t := e2 true
    generalize Y p q (upd w (m + 1) false) (2 * m + 3) 0 = f at *
    generalize Y p q (upd w (m + 1) true) (2 * m + 3) 0 = t at *
    generalize xor (Y p q w (2 * m + 3) 0) (w (m + 1)) = k at *
    generalize Y p q w (2 * m + 2) 0 = y
    revert e2f e2t
    cases y <;> cases f <;> cases t <;> cases k <;> decide
  rw [show (fun w => xor (Hq p m q (upd w (0 + (m + 1)) false)) (Hq p m q (upd w (0 + (m + 1)) true)))
      = fun w => (Y p q w (2 * m + 2) 0 == false) from funext pw]
  have e : (fun w : Nat → Bool => (Y p q w (2 * m + 2) 0 == false))
      = fun w => xor (Y p q w (2 * (m + 1)) 0) true := by
    funext w
    show (Y p q w (2 * m + 2) 0 == false) = _
    generalize Y p q w (2 * m + 2) 0 = y
    cases y <;> rfl
  rw [e, psum_xor, psum_const 0 m true, top_parity_quadratic p hκ q 0 (m + 1) (by omega)]
  exact Bool.xor_false _

/-! ## The sum over the free word -/

/-- The sum over the free word of the multiplier product weighted by `α ⊕ q 0`. -/
theorem sum_q (p : Coef) (hκ : p.κ = true) :
    ∀ n, 1 ≤ n → psum 0 n (fun q => Pq p q n && xor p.α (q 0)) = xor (xor true p.α) p.β
  | 0, h => absurd h (by omega)
  | 1, _ => by
    show xor (Pq p (upd (fun _ => false) (0 + 0) false) 1 && xor p.α (upd (fun _ => false) (0 + 0) false 0))
        (Pq p (upd (fun _ => false) (0 + 0) true) 1 && xor p.α (upd (fun _ => false) (0 + 0) true 0))
      = _
    simp only [Pq, hκ, upd, Nat.add_zero, ↓reduceIte, Bool.true_and]
    cases p.α <;> cases p.β <;> rfl
  | n + 2, _ => by
    show xor (psum 0 (n + 1) (fun q => Pq p (upd q (0 + (n + 1)) false) (n + 2) && xor p.α (upd q (0 + (n + 1)) false 0)))
        (psum 0 (n + 1) (fun q => Pq p (upd q (0 + (n + 1)) true) (n + 2) && xor p.α (upd q (0 + (n + 1)) true 0))) = _
    have pw : ∀ q : Nat → Bool,
        xor (Pq p (upd q (0 + (n + 1)) false) (n + 2) && xor p.α (upd q (0 + (n + 1)) false 0))
          (Pq p (upd q (0 + (n + 1)) true) (n + 2) && xor p.α (upd q (0 + (n + 1)) true 0))
          = (Pq p q (n + 1) && xor p.α (q 0)) := by
      intro q
      simp only [Nat.zero_add]
      have h0 : ∀ b, upd q (n + 1) b 0 = q 0 := fun b => upd_other q (by omega) b
      have hP : ∀ b, Pq p (upd q (n + 1) b) (n + 1) = Pq p q (n + 1) :=
        fun b => Pq_congr p _ _ (n + 1) (fun k hk => upd_other q (by omega) b)
      have hn : ∀ b, upd q (n + 1) b (n + 1) = b := fun b => upd_same q (n + 1) b
      show xor ((Pq p (upd q (n + 1) false) (n + 1) && xor p.β (p.κ && upd q (n + 1) false (n + 1)))
            && xor p.α (upd q (n + 1) false 0))
          ((Pq p (upd q (n + 1) true) (n + 1) && xor p.β (p.κ && upd q (n + 1) true (n + 1)))
            && xor p.α (upd q (n + 1) true 0)) = _
      rw [h0, h0, hP, hP, hn, hn, hκ]
      generalize Pq p q (n + 1) = a
      generalize xor p.α (q 0) = c
      cases p.β <;> cases a <;> cases c <;> rfl
    rw [← psum_xor, show (fun q => xor (Pq p (upd q (0 + (n + 1)) false) (n + 2) && xor p.α (upd q (0 + (n + 1)) false 0))
          (Pq p (upd q (0 + (n + 1)) true) (n + 2) && xor p.α (upd q (0 + (n + 1)) true 0)))
        = fun q => (Pq p q (n + 1) && xor p.α (q 0)) from funext pw]
    exact sum_q p hκ (n + 1) (by omega)

/-- **The top coefficient.** For a quadratic left-permutive rule (`κ = 1`), the number of pairs
`(q, bd)` of a free word `q` of length `n = m + 2` and a boundary word `bd` of length `n + 1` with
apex `bd n = 1` and the two leftmost window cells `x(0, -n + 1)` and `x(0, -n)` white is odd iff
`1 ⊕ α ⊕ β = 1`, for every `γ`. -/
theorem top_coefficient_quadratic (p : Coef) (hκ : p.κ = true) (m : Nat) :
    psum 0 (m + 2) (fun q => psum 0 (m + 3) (fun bd => Fq p m q bd)) = xor (xor true p.α) p.β := by
  rw [show (fun q => psum 0 (m + 3) (fun bd => Fq p m q bd))
      = fun q => (Pq p q (m + 2) && xor p.α (q 0)) from
    funext fun q => by rw [sum_bd, sum_Hq p hκ]]
  exact sum_q p hκ (m + 2) (by omega)

/-! ## From seeds to rows

The seeds are interleaved in one word `z`: `bd t = z (2t)` (`bdz`) and `q t = z (2t + 1)` (`qz`). The cell
`x(0, n - j) = Y j 0` is `z j` plus a function of the bits before `j` (`Y_zdep`), so the map from the
interleaved seed word to the row cells is a triangular substitution (`psum_tri`). -/

def bdz (z : Nat → Bool) : Nat → Bool := fun s => z (2 * s)
def qz (z : Nat → Bool) : Nat → Bool := fun s => z (2 * s + 1)

/-- `Y j t` depends on `z (0), …, z (2t + j)`, and `Y j t ⊕ z (2t + j)` only on the bits before. -/
theorem Y_zdep (p : Coef) :
    ∀ j t,
      (∀ z z' : Nat → Bool, (∀ i, i ≤ 2 * t + j → z i = z' i) →
        Y p (bdz z) (qz z) j t = Y p (bdz z') (qz z') j t) ∧
      (∀ z z' : Nat → Bool, (∀ i, i < 2 * t + j → z i = z' i) →
        xor (Y p (bdz z) (qz z) j t) (z (2 * t + j))
          = xor (Y p (bdz z') (qz z') j t) (z' (2 * t + j)))
  | 0, t => by
    refine ⟨fun z z' h => ?_, fun z z' _ => ?_⟩
    · exact h (2 * t) (by omega)
    · show xor (z (2 * t)) (z (2 * t + 0)) = xor (z' (2 * t)) (z' (2 * t + 0))
      rw [Nat.add_zero, Bool.xor_self, Bool.xor_self]
  | 1, t => by
    refine ⟨fun z z' h => ?_, fun z z' _ => ?_⟩
    · exact h (2 * t + 1) (by omega)
    · show xor (z (2 * t + 1)) (z (2 * t + 1)) = xor (z' (2 * t + 1)) (z' (2 * t + 1))
      rw [Bool.xor_self, Bool.xor_self]
  | j + 2, t => by
    have a1 := Y_zdep p j (t + 1)
    have a2 := Y_zdep p (j + 1) t
    have a3 := Y_zdep p j t
    refine ⟨fun z z' h => ?_, fun z z' h => ?_⟩
    · show xor (Y p (bdz z) (qz z) j (t + 1))
          (p.g (Y p (bdz z) (qz z) (j + 1) t) (Y p (bdz z) (qz z) j t))
        = xor (Y p (bdz z') (qz z') j (t + 1))
          (p.g (Y p (bdz z') (qz z') (j + 1) t) (Y p (bdz z') (qz z') j t))
      rw [a1.1 z z' (fun i hi => h i (by omega)), a2.1 z z' (fun i hi => h i (by omega)),
        a3.1 z z' (fun i hi => h i (by omega))]
    · have e : 2 * (t + 1) + j = 2 * t + (j + 2) := by omega
      have b1 := a1.2 z z' (fun i hi => h i (by omega))
      rw [e] at b1
      have b2 := a2.1 z z' (fun i hi => h i (by omega))
      have b3 := a3.1 z z' (fun i hi => h i (by omega))
      show xor (xor (Y p (bdz z) (qz z) j (t + 1))
            (p.g (Y p (bdz z) (qz z) (j + 1) t) (Y p (bdz z) (qz z) j t))) (z (2 * t + (j + 2)))
        = xor (xor (Y p (bdz z') (qz z') j (t + 1))
            (p.g (Y p (bdz z') (qz z') (j + 1) t) (Y p (bdz z') (qz z') j t))) (z' (2 * t + (j + 2)))
      rw [b2, b3]
      generalize Y p (bdz z) (qz z) j (t + 1) = a at *
      generalize Y p (bdz z') (qz z') j (t + 1) = a' at *
      generalize z (2 * t + (j + 2)) = b at *
      generalize z' (2 * t + (j + 2)) = b' at *
      generalize p.g (Y p (bdz z') (qz z') (j + 1) t) (Y p (bdz z') (qz z') j t) = c
      revert b1
      cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> decide

/-- Cell `j` of the window `[-n, n]`, counted from the right, as a function of a word. -/
def rowW (n : Nat) (c : Nat → Bool) : Int → Bool := fun i =>
  if -(n : Int) ≤ i ∧ i ≤ n then c ((n : Int) - i).toNat else false

/-- The row reconstructed from seeds `(bd, q)`. -/
def rowOfG (p : Coef) (n : Nat) (bd q : Nat → Bool) : Int → Bool :=
  rowW n (fun j => Y p bd q j 0)

/-- The reconstructed row evolves along the diagonals of `Y`, inside the window cone. -/
theorem evolve_rowOfG (p : Coef) (n : Nat) (bd q : Nat → Bool) :
    ∀ t j, j + 2 * t ≤ 2 * n →
      evolveC p t (rowOfG p n bd q) ((n : Int) - j - t) = Y p bd q j t
  | 0, j, h => by
    show rowOfG p n bd q ((n : Int) - j - ((0 : Nat) : Int)) = _
    unfold rowOfG rowW
    have c1 : -(n : Int) ≤ (n : Int) - j - ((0 : Nat) : Int) := by omega
    have c2 : (n : Int) - j - ((0 : Nat) : Int) ≤ n := by omega
    simp only [c1, c2, and_self, ↓reduceIte]
    have e : ((n : Int) - ((n : Int) - j - ((0 : Nat) : Int))).toNat = j := by omega
    rw [e]
  | t + 1, j, h => by
    have ih2 := evolve_rowOfG p n bd q t (j + 2) (by omega)
    have ih1 := evolve_rowOfG p n bd q t (j + 1) (by omega)
    have ih0 := evolve_rowOfG p n bd q t j (by omega)
    show xor (evolveC p t (rowOfG p n bd q) (((n : Int) - j - ((t + 1 : Nat) : Int)) - 1))
        (p.g (evolveC p t (rowOfG p n bd q) ((n : Int) - j - ((t + 1 : Nat) : Int)))
          (evolveC p t (rowOfG p n bd q) (((n : Int) - j - ((t + 1 : Nat) : Int)) + 1))) = _
    have a1 : ((n : Int) - j - ((t + 1 : Nat) : Int)) - 1 = (n : Int) - ((j + 2 : Nat) : Int) - t := by omega
    have a2 : ((n : Int) - j - ((t + 1 : Nat) : Int)) = (n : Int) - ((j + 1 : Nat) : Int) - t := by omega
    have a3 : ((n : Int) - j - ((t + 1 : Nat) : Int)) + 1 = (n : Int) - j - t := by omega
    rw [a1, a3, a2, ih2, ih1, ih0]
    have hY : Y p bd q (j + 2) t = xor (Y p bd q j (t + 1)) (p.g (Y p bd q (j + 1) t) (Y p bd q j t)) := rfl
    rw [hY]
    generalize Y p bd q j (t + 1) = a
    generalize p.g (Y p bd q (j + 1) t) (Y p bd q j t) = c
    cases a <;> cases c <;> rfl

/-! ## The interleaved word and the nested sum -/

theorem psum_succ (s n : Nat) (F : (Nat → Bool) → Bool) :
    psum s (n + 1) F
      = xor (psum s n (fun q => F (upd q (s + n) false))) (psum s n (fun q => F (upd q (s + n) true))) := rfl

theorem psum_two (N : Nat) (F : (Nat → Bool) → Bool) :
    psum 0 (N + 2) F
      = xor (xor (psum 0 N (fun w => F (upd (upd w N false) (N + 1) false)))
                 (psum 0 N (fun w => F (upd (upd w N true) (N + 1) false))))
            (xor (psum 0 N (fun w => F (upd (upd w N false) (N + 1) true)))
                 (psum 0 N (fun w => F (upd (upd w N true) (N + 1) true)))) := by
  rw [show N + 2 = (N + 1) + 1 from rfl, psum_succ, psum_succ, psum_succ]
  simp only [Nat.zero_add]

theorem bdz_upd_even (z : Nat → Bool) (k : Nat) (b : Bool) : bdz (upd z (2 * k) b) = upd (bdz z) k b := by
  funext s; by_cases h : s = k <;> simp [bdz, upd, h] <;> omega

theorem bdz_upd_odd (z : Nat → Bool) (k : Nat) (b : Bool) : bdz (upd z (2 * k + 1) b) = bdz z := by
  funext s; simp [bdz, upd] <;> omega

theorem qz_upd_odd (z : Nat → Bool) (k : Nat) (b : Bool) : qz (upd z (2 * k + 1) b) = upd (qz z) k b := by
  funext s; by_cases h : s = k <;> simp [qz, upd, h] <;> omega

theorem qz_upd_even (z : Nat → Bool) (k : Nat) (b : Bool) : qz (upd z (2 * k) b) = qz z := by
  funext s; simp [qz, upd] <;> omega

/-- A sum over the interleaved word is the nested sum over the free word and the boundary word. -/
theorem psum_interleave (G : (Nat → Bool) → (Nat → Bool) → Bool) :
    ∀ n, psum 0 (2 * n + 1) (fun z => G (bdz z) (qz z))
      = psum 0 n (fun q => psum 0 (n + 1) (fun bd => G bd q))
  | 0 => by
    have e1 : ∀ b, bdz (upd (fun _ => false) 0 b) = upd (fun _ => false) 0 b := by
      intro b; funext s; by_cases h : s = 0 <;> simp [bdz, upd, h] <;> omega
    have e2 : ∀ b, qz (upd (fun _ => false) 0 b) = (fun _ => false) := by
      intro b; funext s; simp [qz, upd] <;> omega
    show xor (G (bdz (upd (fun _ => false) (0 + 0) false)) (qz (upd (fun _ => false) (0 + 0) false)))
        (G (bdz (upd (fun _ => false) (0 + 0) true)) (qz (upd (fun _ => false) (0 + 0) true)))
      = xor (G (upd (fun _ => false) (0 + 0) false) (fun _ => false))
          (G (upd (fun _ => false) (0 + 0) true) (fun _ => false))
    simp only [Nat.add_zero, e1, e2]
  | n + 1 => by
    have key : ∀ b b' : Bool,
        psum 0 (2 * n + 1) (fun w => G (bdz (upd (upd w (2 * n + 1) b') (2 * n + 1 + 1) b))
            (qz (upd (upd w (2 * n + 1) b') (2 * n + 1 + 1) b)))
          = psum 0 n (fun q => psum 0 (n + 1) (fun bd => G (upd bd (n + 1) b) (upd q n b'))) := by
      intro b b'
      rw [← psum_interleave (fun bd q => G (upd bd (n + 1) b) (upd q n b')) n]
      congr 1
      funext w
      have h2 : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      rw [h2, bdz_upd_even, qz_upd_even, bdz_upd_odd, qz_upd_odd]
    have inner : ∀ q' : Nat → Bool, psum 0 (n + 1 + 1) (fun bd => G bd q')
        = xor (psum 0 (n + 1) (fun bd => G (upd bd (n + 1) false) q'))
              (psum 0 (n + 1) (fun bd => G (upd bd (n + 1) true) q')) := by
      intro q'; rw [psum_succ]; simp only [Nat.zero_add]
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by omega, psum_two, key, key, key, key, psum_succ]
    simp only [Nat.zero_add, inner]
    simp only [psum_xor]
    generalize psum 0 n (fun q => psum 0 (n + 1) (fun bd => G (upd bd (n + 1) false) (upd q n false))) = a
    generalize psum 0 n (fun q => psum 0 (n + 1) (fun bd => G (upd bd (n + 1) false) (upd q n true))) = b
    generalize psum 0 n (fun q => psum 0 (n + 1) (fun bd => G (upd bd (n + 1) true) (upd q n false))) = c
    generalize psum 0 n (fun q => psum 0 (n + 1) (fun bd => G (upd bd (n + 1) true) (upd q n true))) = d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-! ## The top coefficient of the center function -/

/-- **The top ANF coefficient of the center function.** Let `p = a ⊕ g(b, c)` with
`g = γ ⊕ α b ⊕ β c ⊕ bc` (`κ = 1`), `n = m + 2`, and let a row on the window `[-n, n]` be given by its
cells `c j = x(0, n - j)`, `j = 0, …, 2n`. The number of such rows with the two leftmost cells
`x(0, -n)` and `x(0, -n + 1)` white and center `x(n, 0)` black is odd iff `1 ⊕ α ⊕ β = 1`, for
every `γ`. Equivalently, over `𝔽₂` the coefficient of the monomial `x_{-n+2} ⋯ x_n` in the algebraic
normal form of the center function `x(n, 0)` of the row `x_{-n}, …, x_n` is `1 ⊕ α ⊕ β` (the
coefficient of a monomial is the parity of the number of its support's assignments with value `1`). -/
theorem top_coefficient_rows (p : Coef) (hκ : p.κ = true) (m : Nat) :
    psum 0 (2 * m + 5) (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
        && evolveC p (m + 2) (rowW (m + 2) c) 0) = xor (xor true p.α) p.β := by
  let h : Nat → (Nat → Bool) → Bool := fun i z => xor (Y p (bdz z) (qz z) i 0) (z i)
  have hdep : ∀ i z z', (∀ j, j < i → z j = z' j) → h i z = h i z' := by
    intro i z z' hz
    have e : 2 * 0 + i = i := by omega
    have := (Y_zdep p i 0).2 z z' (fun j hj => hz j (by omega))
    rw [e] at this
    exact this
  have A := psum_tri h hdep (2 * m + 5)
    (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
        && evolveC p (m + 2) (rowW (m + 2) c) 0)
  rw [← A]
  have Tval : ∀ (z : Nat → Bool) (i : Nat), i < 2 * m + 5 →
      (if i < 2 * m + 5 then xor (z i) (h i z) else z i) = Y p (bdz z) (qz z) i 0 := by
    intro z i hi
    simp only [hi, ↓reduceIte, h]
    generalize z i = a
    generalize Y p (bdz z) (qz z) i 0 = b
    cases a <;> cases b <;> rfl
  have pw : ∀ z : Nat → Bool,
      ((fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
          && evolveC p (m + 2) (rowW (m + 2) c) 0)
        (fun i => if i < 2 * m + 5 then xor (z i) (h i z) else z i))
        = Fq p m (qz z) (bdz z) := by
    intro z
    have row : rowW (m + 2) (fun i => if i < 2 * m + 5 then xor (z i) (h i z) else z i)
        = rowOfG p (m + 2) (bdz z) (qz z) := by
      funext i
      unfold rowW rowOfG
      by_cases hw : -((m + 2 : Nat) : Int) ≤ i ∧ i ≤ ((m + 2 : Nat) : Int)
      · simp only [hw, and_self, ↓reduceIte]
        rw [Tval z _ (by omega)]
        unfold rowW
        simp only [hw, and_self, ↓reduceIte]
      · simp only [hw, ↓reduceIte]
        unfold rowW
        simp only [hw, ↓reduceIte]
    have top : evolveC p (m + 2) (rowOfG p (m + 2) (bdz z) (qz z)) 0 = z (m + 2 + (m + 2)) := by
      have := evolve_rowOfG p (m + 2) (bdz z) (qz z) (m + 2) 0 (by omega)
      have e : ((m + 2 : Nat) : Int) - ((0 : Nat) : Int) - ((m + 2 : Nat) : Int) = 0 := by omega
      rw [e] at this
      rw [this]
      show z (2 * (m + 2)) = _
      congr 1
      omega
    dsimp only
    rw [Tval z (2 * m + 4) (by omega), Tval z (2 * m + 3) (by omega), row, top]
    unfold Fq
    have e : z (m + 2 + (m + 2)) = bdz z (m + 2) := by
      show z (m + 2 + (m + 2)) = z (2 * (m + 2))
      congr 1
      omega
    rw [e]
    generalize bdz z (m + 2) = a
    generalize Y p (bdz z) (qz z) (2 * m + 3) 0 = b
    generalize Y p (bdz z) (qz z) (2 * m + 4) 0 = c
    cases a <;> cases b <;> cases c <;> rfl
  rw [show (fun z => (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
          && evolveC p (m + 2) (rowW (m + 2) c) 0)
        (fun i => if i < 2 * m + 5 then xor (z i) (h i z) else z i))
      = fun z => Fq p m (qz z) (bdz z) from funext pw]
  rw [show 2 * m + 5 = 2 * (m + 2) + 1 from by omega,
    psum_interleave (fun bd q => Fq p m q bd) (m + 2)]
  exact top_coefficient_quadratic p hκ m

/-- Rule 30 (`α = β = 1`): the top coefficient is `1`. -/
theorem rule30_top_coefficient (m : Nat) :
    psum 0 (2 * m + 5) (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
        && evolveC rule30Coef (m + 2) (rowW (m + 2) c) 0) = true :=
  (top_coefficient_rows rule30Coef rfl m).trans rfl

/-- Rule 180 (`α = 1`, `β = 0`): the top coefficient is `0`. -/
theorem rule180_top_coefficient (m : Nat) :
    psum 0 (2 * m + 5) (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
        && evolveC rule180Coef (m + 2) (rowW (m + 2) c) 0) = false :=
  (top_coefficient_rows rule180Coef rfl m).trans rfl

/-! ## Constant-term `γ`-invariance of the top ANF coefficient and Rule 30 vs. Rule 180 separation -/

/-- **Constant-Term `γ`-Invariance of the Top ANF Coefficient and Rule 30 vs. Rule 180 Separation (`top_coefficient_gamma_invariance_and_rule30_vs_rule180`).** -/
theorem top_coefficient_gamma_invariance_and_rule30_vs_rule180
    (p : Coef) (hκ : p.κ = true) (γ' : Bool) (m : Nat) :
    psum 0 (2 * m + 5) (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
          && evolveC { p with γ := γ' } (m + 2) (rowW (m + 2) c) 0) =
      psum 0 (2 * m + 5) (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
          && evolveC p (m + 2) (rowW (m + 2) c) 0) ∧
    psum 0 (2 * m + 5) (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
          && evolveC rule30Coef (m + 2) (rowW (m + 2) c) 0) ≠
      psum 0 (2 * m + 5) (fun c => (c (2 * m + 4) == false) && (c (2 * m + 3) == false)
          && evolveC rule180Coef (m + 2) (rowW (m + 2) c) 0) := by
  refine ⟨?_, ?_⟩
  · rw [top_coefficient_rows { p with γ := γ' } hκ m, top_coefficient_rows p hκ m]
  · rw [rule30_top_coefficient m, rule180_top_coefficient m]
    decide

end Rule30TopCoefficient
end Ruliology.CellularAutomata
