module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Parity of the zero-wedge count for every left-permutive elementary rule

Every left-permutive elementary rule is `a ⊕ g(b, c)` with `g = γ ⊕ α b ⊕ β c ⊕ κ bc` (`Coef`). For
`n ≥ 1`, a boundary value `r` and a far-left value `ℓ`, an *admissible row* has window cell
`x(0, -n) = ℓ`, boundary diagonal `x(t, n - t) = r` for `t < n`, and output `x(n, 0) = 1` (`Adm`). For
Rule 30 with `r = ℓ = 0` the number of admissible rows is the sequence A400898.

Left-permutivity reconstructs a row from two adjacent diagonals. Writing `Y j t = x(t, n - j - t)`, the
local rule solved for its left input gives `Y (j + 2) t = Y j (t + 1) ⊕ g (Y (j + 1) t, Y j t)` (`Y`,
`diag_rec`), so the boundary diagonal `Y 0` and the free word `q t = Y 1 t` determine every diagonal
(`diag_eq_Y`) and the window cell is `Y (2n) 0` (`row_left_eq_Y`). The free word is a bijection from
admissible rows onto the words with `Y (2n) 0 = ℓ` for the boundary `bnd n r`: it is well defined
(`adm_eq_Y`), injective on the window (`adm_injective`), and every such word is the free word of an
admissible row (`rowOf_adm`, `qOf_rowOf`).

The parity of the number of such words is computed by summing out the newest free bit (`psum`,
`psum_step`): `Y (2k) t` depends only on `q t, …, q (t + k - 1)` and `Y (2k + 1) t ⊕ q (t + k)` only on the
bits before `q (t + k)` (`Y_dep`), which gives `S (k + 1) = κ S k` for the top parity `S`. Hence
`top_parity_quadratic`, `wedge_parity_quadratic`: for `κ = 1` the count is odd iff `α ⊕ r = 1`, for every
`n ≥ 1`; and `wedge_parity_affine_one`, `wedge_parity_affine`: for `κ = 0` it has parity `α` at `n = 1`
and is even from `n = 2`. `rule30_wedge_odd`: A400898 is odd.

The parity is a property of the coefficient `α` of the center input and of the boundary value, not of
the OR: Rules 30, 75, 180 and 225 all have odd counts for `r = 0` (`rule180_wedge_odd`), and the
lone-seed center of Rule 180 is `1, 1, 0, 0, …` (observed, not formalized here). Nothing here bounds the center
column of Rule 30, and the counts are over all initial rows, not over the single seed; Problems 1 to 3
stay open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30WedgeParity

/-- Coefficients of a left-permutive rule `a ⊕ g(b, c)` with `g = γ ⊕ α b ⊕ β c ⊕ κ bc`. -/
structure Coef where
  γ : Bool
  α : Bool
  β : Bool
  κ : Bool

def Coef.g (p : Coef) (b c : Bool) : Bool :=
  xor p.γ (xor (p.α && b) (xor (p.β && c) (p.κ && (b && c))))

/-- Diagonal array of the reconstruction: boundary diagonal `bd`, free diagonal `q`, and
`Y (j + 2) t = Y j (t + 1) ⊕ g (Y (j + 1) t, Y j t)`. -/
def Y (p : Coef) (bd : Nat → Bool) (q : Nat → Bool) : Nat → Nat → Bool
  | 0, t => bd t
  | 1, t => q t
  | j + 2, t => xor (Y p bd q j (t + 1)) (p.g (Y p bd q (j + 1) t) (Y p bd q j t))

/-- `F` depends only on the free bits `q s, …, q (e - 1)`. -/
def Dep (s e : Nat) (F : (Nat → Bool) → Bool) : Prop :=
  ∀ q q' : Nat → Bool, (∀ i, s ≤ i → i < e → q i = q' i) → F q = F q'

theorem dep_const (s e : Nat) (c : Bool) : Dep s e (fun _ => c) := fun _ _ _ => rfl

theorem dep_mono {s e s' e' : Nat} {F : (Nat → Bool) → Bool} (h : Dep s e F)
    (hs : s' ≤ s) (he : e ≤ e') : Dep s' e' F :=
  fun q q' hq => h q q' (fun i h1 h2 => hq i (by omega) (by omega))

theorem dep_xor {s e : Nat} {F G : (Nat → Bool) → Bool} (hF : Dep s e F) (hG : Dep s e G) :
    Dep s e (fun q => xor (F q) (G q)) :=
  fun q q' hq => by
    show xor (F q) (G q) = xor (F q') (G q')
    rw [hF q q' hq, hG q q' hq]

theorem dep_g (p : Coef) {s e : Nat} {F G : (Nat → Bool) → Bool} (hF : Dep s e F) (hG : Dep s e G) :
    Dep s e (fun q => p.g (F q) (G q)) :=
  fun q q' hq => by
    show p.g (F q) (G q) = p.g (F q') (G q')
    rw [hF q q' hq, hG q q' hq]

theorem dep_coord (s e i : Nat) (h1 : s ≤ i) (h2 : i < e) : Dep s e (fun q => q i) :=
  fun _ _ hq => hq i h1 h2

/-- Dependence of the even and odd diagonals on the free word, all at once. -/
theorem Y_dep (p : Coef) (bd : Nat → Bool) :
    ∀ k t, Dep t (t + k) (fun q => Y p bd q (2 * k) t) ∧
      Dep t (t + k + 1) (fun q => Y p bd q (2 * k + 1) t) ∧
      Dep t (t + k) (fun q => xor (Y p bd q (2 * k + 1) t) (q (t + k))) := by
  intro k
  induction k with
  | zero =>
    intro t
    refine ⟨fun _ _ _ => rfl, ?_, ?_⟩
    · exact fun q q' hq => hq t (Nat.le_refl _) (by omega)
    · exact fun _ _ _ => by simp [Y]
  | succ k ih =>
    intro t
    have ihT := ih t
    have ihT1 := ih (t + 1)
    have hE : Dep t (t + (k + 1)) (fun q => Y p bd q (2 * (k + 1)) t) := by
      have e1 : Dep t (t + (k + 1)) (fun q => Y p bd q (2 * k) (t + 1)) :=
        dep_mono ihT1.1 (by omega) (by omega)
      have e2 : Dep t (t + (k + 1)) (fun q => Y p bd q (2 * k + 1) t) :=
        dep_mono ihT.2.1 (Nat.le_refl _) (by omega)
      have e3 : Dep t (t + (k + 1)) (fun q => Y p bd q (2 * k) t) :=
        dep_mono ihT.1 (Nat.le_refl _) (by omega)
      exact dep_xor e1 (dep_g p e2 e3)
    refine ⟨hE, ?_, ?_⟩
    · have o1 : Dep t (t + (k + 1) + 1) (fun q => Y p bd q (2 * k + 1) (t + 1)) :=
        dep_mono ihT1.2.1 (by omega) (by omega)
      have o2 : Dep t (t + (k + 1) + 1) (fun q => Y p bd q (2 * (k + 1)) t) :=
        dep_mono hE (Nat.le_refl _) (by omega)
      have o3 : Dep t (t + (k + 1) + 1) (fun q => Y p bd q (2 * k + 1) t) :=
        dep_mono ihT.2.1 (Nat.le_refl _) (by omega)
      exact dep_xor o1 (dep_g p o2 o3)
    · -- `O (k+1) t ⊕ q (t + k + 1)` depends only on `q t, …, q (t + k)`.
      have l1 : Dep t (t + (k + 1)) (fun q => xor (Y p bd q (2 * k + 1) (t + 1)) (q (t + 1 + k))) :=
        dep_mono ihT1.2.2 (by omega) (by omega)
      have l2 : Dep t (t + (k + 1)) (fun q => Y p bd q (2 * (k + 1)) t) := hE
      have l3 : Dep t (t + (k + 1)) (fun q => Y p bd q (2 * k + 1) t) :=
        dep_mono ihT.2.1 (Nat.le_refl _) (by omega)
      intro q q' hq
      have h1 := l1 q q' hq
      have h2 := dep_g p l2 l3 q q' hq
      show xor (xor (Y p bd q (2 * k + 1) (t + 1)) (p.g (Y p bd q (2 * (k + 1)) t) (Y p bd q (2 * k + 1) t))) (q (t + (k + 1)))
        = xor (xor (Y p bd q' (2 * k + 1) (t + 1)) (p.g (Y p bd q' (2 * (k + 1)) t) (Y p bd q' (2 * k + 1) t))) (q' (t + (k + 1)))
      have e : t + 1 + k = t + (k + 1) := by omega
      rw [e] at h1
      simp only [] at h1 h2
      generalize Y p bd q (2 * k + 1) (t + 1) = a at *
      generalize Y p bd q' (2 * k + 1) (t + 1) = a' at *
      generalize q (t + (k + 1)) = b at *
      generalize q' (t + (k + 1)) = b' at *
      generalize p.g (Y p bd q (2 * (k + 1)) t) (Y p bd q (2 * k + 1) t) = c at *
      generalize p.g (Y p bd q' (2 * (k + 1)) t) (Y p bd q' (2 * k + 1) t) = c' at *
      revert h1 h2
      cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp

/-! ## Parity sums over the first `n` free bits from `s` -/

def upd (q : Nat → Bool) (i : Nat) (b : Bool) : Nat → Bool := fun j => if j = i then b else q j

theorem upd_same (q : Nat → Bool) (i : Nat) (b : Bool) : upd q i b i = b := by simp [upd]

theorem upd_other (q : Nat → Bool) {i j : Nat} (h : j ≠ i) (b : Bool) : upd q i b j = q j := by
  simp [upd, h]

theorem upd_comm (q : Nat → Bool) {i j : Nat} (h : i ≠ j) (b c : Bool) :
    upd (upd q i b) j c = upd (upd q j c) i b := by
  funext x
  by_cases hx : x = j <;> by_cases hy : x = i <;> simp [upd, hx, hy] <;> omega

/-- The parity of the number of assignments of `q s, …, q (s + n - 1)` (all other bits false) with
`F q = true`. -/
def psum (s : Nat) : Nat → ((Nat → Bool) → Bool) → Bool
  | 0, F => F (fun _ => false)
  | n + 1, F =>
    xor (psum s n (fun q => F (upd q (s + n) false))) (psum s n (fun q => F (upd q (s + n) true)))

theorem psum_xor (s : Nat) : ∀ (n : Nat) (F G : (Nat → Bool) → Bool),
    psum s n (fun q => xor (F q) (G q)) = xor (psum s n F) (psum s n G)
  | 0, _, _ => rfl
  | n + 1, F, G => by
    simp only [psum]
    rw [psum_xor s n (fun q => F (upd q (s + n) false)) (fun q => G (upd q (s + n) false)),
      psum_xor s n (fun q => F (upd q (s + n) true)) (fun q => G (upd q (s + n) true))]
    generalize psum s n (fun q => F (upd q (s + n) false)) = a
    generalize psum s n (fun q => G (upd q (s + n) false)) = b
    generalize psum s n (fun q => F (upd q (s + n) true)) = c
    generalize psum s n (fun q => G (upd q (s + n) true)) = d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- `F` does not depend on the bit `u`. -/
def Indep (u : Nat) (F : (Nat → Bool) → Bool) : Prop := ∀ q b, F (upd q u b) = F q

theorem psum_indep (s : Nat) : ∀ (n u : Nat) (F : (Nat → Bool) → Bool), s ≤ u → u < s + n →
    Indep u F → psum s n F = false
  | 0, u, F, h1, h2, _ => by omega
  | n + 1, u, F, h1, h2, hI => by
    by_cases hu : u = s + n
    · subst hu
      simp only [psum]
      rw [show (fun q => F (upd q (s + n) false)) = F from funext fun q => hI q false,
        show (fun q => F (upd q (s + n) true)) = F from funext fun q => hI q true]
      exact Bool.xor_self _
    · have hI' : ∀ b, Indep u (fun q => F (upd q (s + n) b)) := fun b q b' => by
        show F (upd (upd q u b') (s + n) b) = F (upd q (s + n) b)
        rw [upd_comm q hu b' b]
        exact hI _ b'
      simp only [psum]
      rw [psum_indep s n u _ h1 (by omega) (hI' false), psum_indep s n u _ h1 (by omega) (hI' true)]
      rfl

theorem psum_const (s n : Nat) (c : Bool) : psum s (n + 1) (fun _ => c) = false :=
  psum_indep s (n + 1) s _ (Nat.le_refl _) (by omega) (fun _ _ => rfl)

theorem psum_and_left (s : Nat) (c : Bool) : ∀ (n : Nat) (F : (Nat → Bool) → Bool),
    psum s n (fun q => c && F q) = (c && psum s n F)
  | 0, _ => rfl
  | n + 1, F => by
    cases c
    · cases n <;> simp [psum_const]
    · simp only [Bool.true_and]

/-! ## The recursion for the top parity -/

theorem g_diff (p : Coef) (b c : Bool) : xor (p.g b c) (p.g (!b) c) = xor p.α (p.κ && c) := by
  cases p with
  | mk γ α β κ =>
    cases γ <;> cases α <;> cases β <;> cases κ <;> cases b <;> cases c <;> simp [Coef.g]

/-- The part of `Y (2 * (k + 1)) t` that contains the new free bit `q (t + k)` only through `b`. -/
def Afun (p : Coef) (bd : Nat → Bool) (t k : Nat) (b : Bool) (q : Nat → Bool) : Bool :=
  Y p bd (upd q (t + k) b) (2 * k) (t + 1)

def Bfun (p : Coef) (bd : Nat → Bool) (t k : Nat) (b : Bool) (q : Nat → Bool) : Bool :=
  p.g (xor (xor (Y p bd q (2 * k + 1) t) (q (t + k))) b) (Y p bd q (2 * k) t)

theorem Y_upd (p : Coef) (bd : Nat → Bool) (t k : Nat) (b : Bool) :
    (fun q => Y p bd (upd q (t + k) b) (2 * (k + 1)) t)
      = fun q => xor (Afun p bd t k b q) (Bfun p bd t k b q) := by
  have hdep := Y_dep p bd k t
  funext q
  show xor (Y p bd (upd q (t + k) b) (2 * k) (t + 1))
      (p.g (Y p bd (upd q (t + k) b) (2 * k + 1) t) (Y p bd (upd q (t + k) b) (2 * k) t)) = _
  have h1 : Y p bd (upd q (t + k) b) (2 * k) t = Y p bd q (2 * k) t :=
    hdep.1 _ _ (fun i _ h2 => upd_other q (by omega) b)
  have h2 : xor (Y p bd (upd q (t + k) b) (2 * k + 1) t) b
      = xor (Y p bd q (2 * k + 1) t) (q (t + k)) := by
    have := hdep.2.2 (upd q (t + k) b) q (fun i _ h2 => upd_other q (by omega) b)
    simpa [upd_same] using this
  have h3 : Y p bd (upd q (t + k) b) (2 * k + 1) t
      = xor (xor (Y p bd q (2 * k + 1) t) (q (t + k))) b := by
    rw [← h2]
    generalize Y p bd (upd q (t + k) b) (2 * k + 1) t = x
    cases x <;> cases b <;> rfl
  rw [h1, h3]
  rfl

theorem psum_A_eq (p : Coef) (bd : Nat → Bool) (t k : Nat) (hk : 1 ≤ k) :
    xor (psum t k (Afun p bd t k false)) (psum t k (Afun p bd t k true)) = false := by
  have hdep1 := Y_dep p bd k (t + 1)
  have hI : Indep t (fun q => xor (Afun p bd t k false q) (Afun p bd t k true q)) := by
    intro q b
    have hne : t + k ≠ t := by omega
    have hc : ∀ c, Afun p bd t k c (upd q t b) = Afun p bd t k c q := by
      intro c
      unfold Afun
      apply hdep1.1
      intro i h1 h2
      have hit : i ≠ t := by omega
      by_cases hik : i = t + k
      · subst hik; simp [upd_same]
      · rw [upd_other _ hik, upd_other _ hik, upd_other _ hit]
    show xor (Afun p bd t k false (upd q t b)) (Afun p bd t k true (upd q t b)) = _
    rw [hc, hc]
  have := psum_indep t k t _ (Nat.le_refl _) (by omega) hI
  rwa [psum_xor] at this

theorem psum_B_eq (p : Coef) (bd : Nat → Bool) (t k : Nat) (hk : 1 ≤ k) :
    xor (psum t k (Bfun p bd t k false)) (psum t k (Bfun p bd t k true))
      = (p.κ && psum t k (fun q => Y p bd q (2 * k) t)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e : (fun q => xor (Bfun p bd t (k' + 1) false q) (Bfun p bd t (k' + 1) true q))
      = fun q => xor p.α (p.κ && Y p bd q (2 * (k' + 1)) t) := by
    funext q
    unfold Bfun
    simp only [Bool.xor_false, Bool.xor_true]
    exact g_diff p _ _
  rw [← psum_xor, e, psum_xor, psum_const, psum_and_left]
  exact Bool.false_xor _

theorem psum_step (p : Coef) (bd : Nat → Bool) (t k : Nat) (hk : 1 ≤ k) :
    psum t (k + 1) (fun q => Y p bd q (2 * (k + 1)) t)
      = (p.κ && psum t k (fun q => Y p bd q (2 * k) t)) := by
  have hsum : psum t (k + 1) (fun q => Y p bd q (2 * (k + 1)) t)
      = xor (psum t k (fun q => Y p bd (upd q (t + k) false) (2 * (k + 1)) t))
          (psum t k (fun q => Y p bd (upd q (t + k) true) (2 * (k + 1)) t)) := rfl
  rw [hsum, Y_upd, Y_upd, psum_xor, psum_xor]
  have hA := psum_A_eq p bd t k hk
  have hB := psum_B_eq p bd t k hk
  rw [← hB]
  generalize psum t k (Afun p bd t k false) = a at *
  generalize psum t k (Afun p bd t k true) = c at *
  generalize psum t k (Bfun p bd t k false) = b at *
  generalize psum t k (Bfun p bd t k true) = d at *
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem psum_base (p : Coef) (bd : Nat → Bool) (t : Nat) :
    psum t 1 (fun q => Y p bd q 2 t) = xor p.α (p.κ && bd t) := by
  show xor (Y p bd (upd (fun _ => false) (t + 0) false) 2 t)
      (Y p bd (upd (fun _ => false) (t + 0) true) 2 t) = _
  have e : ∀ b, Y p bd (upd (fun _ => false) (t + 0) b) 2 t = xor (bd (t + 1)) (p.g b (bd t)) := by
    intro b
    show xor (bd (t + 1)) (p.g (upd (fun _ => false) (t + 0) b t) (bd t)) = _
    rw [show t + 0 = t from rfl, upd_same]
  rw [e, e]
  generalize bd (t + 1) = u
  generalize bd t = v
  cases p with
  | mk γ α β κ =>
    cases γ <;> cases α <;> cases β <;> cases κ <;> cases u <;> cases v <;> simp [Coef.g]

/-- **Top parity, quadratic rules.** For `κ = 1` the parity of the number of free words `q` of
length `n` with `Y (2n) t = 1` is `α ⊕ bd t`, for every `n ≥ 1`. -/
theorem top_parity_quadratic (p : Coef) (hκ : p.κ = true) (bd : Nat → Bool) (t : Nat) :
    ∀ n, 1 ≤ n → psum t n (fun q => Y p bd q (2 * n) t) = xor p.α (bd t)
  | 0, h => absurd h (by omega)
  | 1, _ => by
    have := psum_base p bd t
    simpa [hκ] using this
  | n + 2, _ => by
    refine (psum_step p bd t (n + 1) (by omega)).trans ?_
    rw [top_parity_quadratic p hκ bd t (n + 1) (by omega), hκ]
    cases p.α <;> cases bd t <;> rfl

/-- **Top parity, affine rules.** For `κ = 0` the parity is `α` at `n = 1` and `0` from `n = 2`. -/
theorem top_parity_affine (p : Coef) (hκ : p.κ = false) (bd : Nat → Bool) (t : Nat) :
    psum t 1 (fun q => Y p bd q 2 t) = p.α ∧
      ∀ n, 2 ≤ n → psum t n (fun q => Y p bd q (2 * n) t) = false := by
  refine ⟨by simpa [hκ] using psum_base p bd t, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 := psum_step p bd t (m + 1) (by omega)
  rw [hκ] at h1
  exact h1.trans rfl

/-! ## The actual diagram -/

/-- One step of the left-permutive rule `a ⊕ g(b, c)` on a two-sided row. -/
def stepC (p : Coef) (x : Int → Bool) : Int → Bool := fun i => xor (x (i - 1)) (p.g (x i) (x (i + 1)))

def evolveC (p : Coef) : Nat → (Int → Bool) → (Int → Bool)
  | 0, x => x
  | t + 1, x => stepC p (evolveC p t x)

/-- The diagonal array of the diagram of `x`: `diag j t` is the cell at time `t`, position
`n - j - t`. -/
def diag (p : Coef) (n : Nat) (x : Int → Bool) (j t : Nat) : Bool :=
  evolveC p t x ((n : Int) - j - t)

theorem diag_rec (p : Coef) (n : Nat) (x : Int → Bool) (j t : Nat) :
    diag p n x (j + 2) t
      = xor (diag p n x j (t + 1)) (p.g (diag p n x (j + 1) t) (diag p n x j t)) := by
  unfold diag
  have h1 : evolveC p (t + 1) x ((n : Int) - j - ((t + 1 : Nat) : Int))
      = xor (evolveC p t x ((n : Int) - ((j + 2 : Nat) : Int) - t))
          (p.g (evolveC p t x ((n : Int) - ((j + 1 : Nat) : Int) - t))
            (evolveC p t x ((n : Int) - j - t))) := by
    show xor (evolveC p t x (((n : Int) - j - ((t + 1 : Nat) : Int)) - 1))
        (p.g (evolveC p t x ((n : Int) - j - ((t + 1 : Nat) : Int)))
          (evolveC p t x (((n : Int) - j - ((t + 1 : Nat) : Int)) + 1))) = _
    have a1 : ((n : Int) - j - ((t + 1 : Nat) : Int)) - 1 = (n : Int) - ((j + 2 : Nat) : Int) - t := by omega
    have a2 : ((n : Int) - j - ((t + 1 : Nat) : Int)) = (n : Int) - ((j + 1 : Nat) : Int) - t := by omega
    have a3 : ((n : Int) - j - ((t + 1 : Nat) : Int)) + 1 = (n : Int) - j - t := by omega
    rw [a1, a3, a2]
  rw [h1]
  generalize evolveC p t x ((n : Int) - ((j + 2 : Nat) : Int) - t) = a
  generalize p.g (evolveC p t x ((n : Int) - ((j + 1 : Nat) : Int) - t)) (evolveC p t x ((n : Int) - j - t)) = c
  cases a <;> cases c <;> rfl

/-- Every diagonal of the diagram is the reconstruction from its boundary and first diagonals. -/
theorem diag_eq_Y (p : Coef) (n : Nat) (x : Int → Bool) :
    ∀ j t, diag p n x j t = Y p (fun t => diag p n x 0 t) (fun t => diag p n x 1 t) j t
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, t => by
    rw [diag_rec]
    show _ = xor (Y p (fun t => diag p n x 0 t) (fun t => diag p n x 1 t) j (t + 1))
      (p.g (Y p (fun t => diag p n x 0 t) (fun t => diag p n x 1 t) (j + 1) t)
        (Y p (fun t => diag p n x 0 t) (fun t => diag p n x 1 t) j t))
    rw [diag_eq_Y p n x j (t + 1), diag_eq_Y p n x (j + 1) t, diag_eq_Y p n x j t]

/-- `Y` depends on the boundary only through `bd 0, …, bd (t + (j + 1) / 2)`. -/
theorem Y_bd_congr (p : Coef) (q : Nat → Bool) (bd bd' : Nat → Bool) :
    ∀ j t, (∀ i, i ≤ t + (j + 1) / 2 → bd i = bd' i) → Y p bd q j t = Y p bd' q j t
  | 0, t, h => h t (by omega)
  | 1, _, _ => rfl
  | j + 2, t, h => by
    show xor (Y p bd q j (t + 1)) (p.g (Y p bd q (j + 1) t) (Y p bd q j t))
      = xor (Y p bd' q j (t + 1)) (p.g (Y p bd' q (j + 1) t) (Y p bd' q j t))
    rw [Y_bd_congr p q bd bd' j (t + 1) (fun i hi => h i (by omega)),
      Y_bd_congr p q bd bd' (j + 1) t (fun i hi => h i (by omega)),
      Y_bd_congr p q bd bd' j t (fun i hi => h i (by omega))]

/-- The leftmost cell of the window is the top diagonal: `x(0, -n) = Y (2n) 0`. -/
theorem row_left_eq_Y (p : Coef) (n : Nat) (x : Int → Bool) :
    x (-(n : Int)) = Y p (fun t => diag p n x 0 t) (fun t => diag p n x 1 t) (2 * n) 0 := by
  rw [← diag_eq_Y]
  unfold diag
  show x (-(n : Int)) = x ((n : Int) - ((2 * n : Nat) : Int) - ((0 : Nat) : Int))
  have : (n : Int) - ((2 * n : Nat) : Int) - ((0 : Nat) : Int) = -(n : Int) := by omega
  rw [this]

/-! ## Admissible rows and free words -/

/-- The boundary diagonal: `r` for `t < n`, and the output value `1` at time `n`. -/
def bnd (n : Nat) (r : Bool) : Nat → Bool := fun t => if t < n then r else true

/-- An admissible initial row: window cell `x(0, -n) = ℓ`, boundary diagonal `x(t, n - t) = r` for
`t < n`, and output `x(n, 0) = 1`. -/
structure Adm (p : Coef) (n : Nat) (r ℓ : Bool) (x : Int → Bool) : Prop where
  left : x (-(n : Int)) = ℓ
  bdry : ∀ t, t < n → evolveC p t x ((n : Int) - t) = r
  out : evolveC p n x 0 = true

/-- The free word of a row: the diagonal next to the boundary. -/
def qOf (p : Coef) (n : Nat) (x : Int → Bool) (t : Nat) : Bool := diag p n x 1 t

theorem diag0_eq_bnd (p : Coef) (n : Nat) (r ℓ : Bool) (x : Int → Bool) (h : Adm p n r ℓ x) :
    ∀ i, i ≤ n → diag p n x 0 i = bnd n r i := by
  intro i hi
  unfold bnd
  by_cases hlt : i < n
  · simp only [hlt, ↓reduceIte]
    have := h.bdry i hlt
    unfold diag
    have e : (n : Int) - ((0 : Nat) : Int) - (i : Int) = (n : Int) - (i : Int) := by omega
    rw [e]; exact this
  · have hin : i = n := by omega
    subst hin
    simp only [hlt, ↓reduceIte]
    unfold diag
    have e : (i : Int) - ((0 : Nat) : Int) - (i : Int) = 0 := by omega
    rw [e]; exact h.out

/-- The free word of an admissible row reconstructs its window cell. -/
theorem adm_eq_Y (p : Coef) (n : Nat) (r ℓ : Bool) (x : Int → Bool) (h : Adm p n r ℓ x) :
    Y p (bnd n r) (qOf p n x) (2 * n) 0 = ℓ := by
  have h1 := row_left_eq_Y p n x
  rw [h.left] at h1
  rw [h1]
  exact Y_bd_congr p _ _ _ (2 * n) 0 (fun i hi => (diag0_eq_bnd p n r ℓ x h i (by omega)).symm)

/-- `Y j 0` for `j ≤ 2n` depends only on `q 0, …, q (n - 1)`. -/
theorem Y_q_congr (p : Coef) (bd : Nat → Bool) (n : Nat) (q q' : Nat → Bool)
    (hq : ∀ t, t < n → q t = q' t) (j : Nat) (hj : j ≤ 2 * n) : Y p bd q j 0 = Y p bd q' j 0 := by
  obtain ⟨k, hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  rcases hk with rfl | rfl
  · exact (Y_dep p bd k 0).1 q q' (fun i _ h2 => hq i (by omega))
  · exact (Y_dep p bd k 0).2.1 q q' (fun i _ h2 => hq i (by omega))

/-- **Injectivity.** Two admissible rows with the same free word agree on the window. -/
theorem adm_injective (p : Coef) (n : Nat) (r ℓ : Bool) (x x' : Int → Bool)
    (h : Adm p n r ℓ x) (h' : Adm p n r ℓ x')
    (hq : ∀ t, t < n → qOf p n x t = qOf p n x' t) :
    ∀ i : Int, -(n : Int) ≤ i → i ≤ n → x i = x' i := by
  intro i h1 h2
  have key : ∀ (y : Int → Bool), Adm p n r ℓ y →
      y i = Y p (bnd n r) (qOf p n y) (n - i).toNat 0 := by
    intro y hy
    have e : y i = diag p n y (n - i).toNat 0 := by
      unfold diag
      show y i = y ((n : Int) - (((n : Int) - i).toNat : Nat) - ((0 : Nat) : Int))
      have : (n : Int) - (((n : Int) - i).toNat : Nat) - ((0 : Nat) : Int) = i := by omega
      rw [this]
    rw [e, diag_eq_Y]
    exact Y_bd_congr p _ _ _ _ 0 (fun k hk => diag0_eq_bnd p n r ℓ y hy k (by omega))
  rw [key x h, key x' h']
  exact Y_q_congr p _ n _ _ hq _ (by omega)

/-- The window row reconstructed from a free word. -/
def rowOf (p : Coef) (n : Nat) (r : Bool) (q : Nat → Bool) : Int → Bool := fun i =>
  if -(n : Int) ≤ i ∧ i ≤ n then Y p (bnd n r) q ((n : Int) - i).toNat 0 else false

/-- The reconstructed row evolves along the diagonals of `Y`, inside the window cone. -/
theorem evolve_rowOf (p : Coef) (n : Nat) (r : Bool) (q : Nat → Bool) :
    ∀ t j, j + 2 * t ≤ 2 * n →
      evolveC p t (rowOf p n r q) ((n : Int) - j - t) = Y p (bnd n r) q j t
  | 0, j, h => by
    show rowOf p n r q ((n : Int) - j - ((0 : Nat) : Int)) = _
    unfold rowOf
    have c1 : -(n : Int) ≤ (n : Int) - j - ((0 : Nat) : Int) := by omega
    have c2 : (n : Int) - j - ((0 : Nat) : Int) ≤ n := by omega
    simp only [c1, c2, and_self, ↓reduceIte]
    have e : ((n : Int) - ((n : Int) - j - ((0 : Nat) : Int))).toNat = j := by omega
    rw [e]
  | t + 1, j, h => by
    have ih2 := evolve_rowOf p n r q t (j + 2) (by omega)
    have ih1 := evolve_rowOf p n r q t (j + 1) (by omega)
    have ih0 := evolve_rowOf p n r q t j (by omega)
    show xor (evolveC p t (rowOf p n r q) (((n : Int) - j - ((t + 1 : Nat) : Int)) - 1))
        (p.g (evolveC p t (rowOf p n r q) ((n : Int) - j - ((t + 1 : Nat) : Int)))
          (evolveC p t (rowOf p n r q) (((n : Int) - j - ((t + 1 : Nat) : Int)) + 1))) = _
    have a1 : ((n : Int) - j - ((t + 1 : Nat) : Int)) - 1 = (n : Int) - ((j + 2 : Nat) : Int) - t := by omega
    have a2 : ((n : Int) - j - ((t + 1 : Nat) : Int)) = (n : Int) - ((j + 1 : Nat) : Int) - t := by omega
    have a3 : ((n : Int) - j - ((t + 1 : Nat) : Int)) + 1 = (n : Int) - j - t := by omega
    rw [a1, a3, a2, ih2, ih1, ih0]
    have hY : Y p (bnd n r) q (j + 2) t
        = xor (Y p (bnd n r) q j (t + 1)) (p.g (Y p (bnd n r) q (j + 1) t) (Y p (bnd n r) q j t)) := rfl
    rw [hY]
    generalize Y p (bnd n r) q j (t + 1) = a
    generalize p.g (Y p (bnd n r) q (j + 1) t) (Y p (bnd n r) q j t) = c
    cases a <;> cases c <;> rfl

/-- **Surjectivity.** A free word with the right top diagonal reconstructs an admissible row. -/
theorem rowOf_adm (p : Coef) (n : Nat) (r ℓ : Bool) (q : Nat → Bool)
    (hq : Y p (bnd n r) q (2 * n) 0 = ℓ) : Adm p n r ℓ (rowOf p n r q) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold rowOf
    have c1 : -(n : Int) ≤ -(n : Int) := Int.le_refl _
    have c2 : -(n : Int) ≤ n := by omega
    simp only [c1, c2, and_self, ↓reduceIte]
    have e : ((n : Int) - -(n : Int)).toNat = 2 * n := by omega
    rw [e]; exact hq
  · intro t ht
    have := evolve_rowOf p n r q t 0 (by omega)
    have e : (n : Int) - ((0 : Nat) : Int) - (t : Int) = (n : Int) - (t : Int) := by omega
    rw [e] at this
    rw [this]
    simp only [Y, bnd, ht, ↓reduceIte]
  · have := evolve_rowOf p n r q n 0 (by omega)
    have e : (n : Int) - ((0 : Nat) : Int) - (n : Int) = 0 := by omega
    rw [e] at this
    rw [this]
    simp [Y, bnd]

theorem qOf_rowOf (p : Coef) (n : Nat) (r : Bool) (q : Nat → Bool) (t : Nat) (ht : t < n) :
    qOf p n (rowOf p n r q) t = q t := by
  have := evolve_rowOf p n r q t 1 (by omega)
  unfold qOf diag
  exact this

/-! ## The wedge count -/

/-- The number of free words `q` of length `n` whose reconstructed window cell is `ℓ`, counted modulo
two, for the boundary diagonal `r` and output `1`. By `adm_eq_Y`, `adm_injective` and `rowOf_adm` it is
the number of admissible rows, modulo two. -/
theorem wedge_parity_quadratic (p : Coef) (hκ : p.κ = true) (n : Nat) (hn : 1 ≤ n) (r ℓ : Bool) :
    psum 0 n (fun q => Y p (bnd n r) q (2 * n) 0 == ℓ) = xor p.α r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : (fun q : Nat → Bool => Y p (bnd (m + 1) r) q (2 * (m + 1)) 0 == ℓ)
      = fun q => xor (xor (Y p (bnd (m + 1) r) q (2 * (m + 1)) 0) ℓ) true := by
    funext q
    generalize Y p (bnd (m + 1) r) q (2 * (m + 1)) 0 = y
    cases y <;> cases ℓ <;> rfl
  rw [e, psum_xor 0 (m + 1) (fun q => xor (Y p (bnd (m + 1) r) q (2 * (m + 1)) 0) ℓ) (fun _ => true),
    psum_xor 0 (m + 1) (fun q => Y p (bnd (m + 1) r) q (2 * (m + 1)) 0) (fun _ => ℓ),
    psum_const 0 m ℓ, psum_const 0 m true,
    top_parity_quadratic p hκ (bnd (m + 1) r) 0 (m + 1) (by omega)]
  simp only [bnd, show 0 < m + 1 from by omega, ↓reduceIte, Bool.xor_false]

theorem wedge_parity_affine_one (p : Coef) (hκ : p.κ = false) (r ℓ : Bool) :
    psum 0 1 (fun q => Y p (bnd 1 r) q 2 0 == ℓ) = p.α := by
  have e : (fun q : Nat → Bool => Y p (bnd 1 r) q 2 0 == ℓ)
      = fun q => xor (xor (Y p (bnd 1 r) q 2 0) ℓ) true := by
    funext q
    generalize Y p (bnd 1 r) q 2 0 = y
    cases y <;> cases ℓ <;> rfl
  rw [e, psum_xor 0 1 (fun q => xor (Y p (bnd 1 r) q 2 0) ℓ) (fun _ => true),
    psum_xor 0 1 (fun q => Y p (bnd 1 r) q 2 0) (fun _ => ℓ),
    psum_const 0 0 ℓ, psum_const 0 0 true, (top_parity_affine p hκ (bnd 1 r) 0).1]
  simp

theorem wedge_parity_affine (p : Coef) (hκ : p.κ = false) (n : Nat) (hn : 2 ≤ n) (r ℓ : Bool) :
    psum 0 n (fun q => Y p (bnd n r) q (2 * n) 0 == ℓ) = false := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : (fun q : Nat → Bool => Y p (bnd (m + 1) r) q (2 * (m + 1)) 0 == ℓ)
      = fun q => xor (xor (Y p (bnd (m + 1) r) q (2 * (m + 1)) 0) ℓ) true := by
    funext q
    generalize Y p (bnd (m + 1) r) q (2 * (m + 1)) 0 = y
    cases y <;> cases ℓ <;> rfl
  rw [e, psum_xor 0 (m + 1) (fun q => xor (Y p (bnd (m + 1) r) q (2 * (m + 1)) 0) ℓ) (fun _ => true),
    psum_xor 0 (m + 1) (fun q => Y p (bnd (m + 1) r) q (2 * (m + 1)) 0) (fun _ => ℓ),
    psum_const 0 m ℓ, psum_const 0 m true,
    (top_parity_affine p hκ (bnd (m + 1) r) 0).2 (m + 1) hn]
  rfl

/-! ## Rule 30 -/

/-- Rule 30: `a ⊕ (b ∨ c) = a ⊕ b ⊕ c ⊕ bc`. -/
def rule30Coef : Coef := ⟨false, true, true, true⟩

theorem rule30_g (b c : Bool) : rule30Coef.g b c = (b || c) := by
  cases b <;> cases c <;> rfl

theorem evolveC_rule30 (t : Nat) :
    ∀ i : Int, evolveC rule30Coef t (fun j => decide (j = 0)) i = Rule30Jen.cell t i := by
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    show xor (evolveC rule30Coef t (fun j => decide (j = 0)) (i - 1))
        (rule30Coef.g (evolveC rule30Coef t (fun j => decide (j = 0)) i)
          (evolveC rule30Coef t (fun j => decide (j = 0)) (i + 1)))
      = Rule30Jen.rule (Rule30Jen.cell t (i - 1)) (Rule30Jen.cell t i) (Rule30Jen.cell t (i + 1))
    rw [rule30_g, ih, ih, ih]
    rfl

/-- **Rule 30.** The number of free words `q` of length `n ≥ 1` with reconstructed window cell `0`
under the zero boundary diagonal is odd: this is the parity of A400898. -/
theorem rule30_wedge_odd (n : Nat) (hn : 1 ≤ n) :
    psum 0 n (fun q => Y rule30Coef (bnd n false) q (2 * n) 0 == false) = true :=
  (wedge_parity_quadratic rule30Coef rfl n hn false false).trans rfl

/-! ## Rule 180 -/

/-- Rule 180: `a ⊕ b ⊕ bc`. -/
def rule180Coef : Coef := ⟨false, true, false, true⟩

/-- Rule 180 has the same odd wedge counts as Rule 30. -/
theorem rule180_wedge_odd (n : Nat) (hn : 1 ≤ n) :
    psum 0 n (fun q => Y rule180Coef (bnd n false) q (2 * n) 0 == false) = true :=
  (wedge_parity_quadratic rule180Coef rfl n hn false false).trans rfl

/-! ## Far-left target `ℓ`-invariance and boundary-flip complementarity of quadratic wedge parity -/

/-- **Target `ℓ`-Invariance and Boundary-Flip Complementarity of Quadratic Wedge Parity (`wedge_parity_quadratic_invariance_and_flip`).** -/
theorem wedge_parity_quadratic_invariance_and_flip
    (p : Coef) (hκ : p.κ = true) (n : Nat) (hn : 1 ≤ n) (r ℓ1 ℓ2 : Bool) :
    psum 0 n (fun q => Y p (bnd n r) q (2 * n) 0 == ℓ1) =
      psum 0 n (fun q => Y p (bnd n r) q (2 * n) 0 == ℓ2) ∧
    psum 0 n (fun q => Y p (bnd n (!r)) q (2 * n) 0 == ℓ1) =
      !psum 0 n (fun q => Y p (bnd n r) q (2 * n) 0 == ℓ1) ∧
    psum 0 n (fun q => Y rule30Coef (bnd n true) q (2 * n) 0 == ℓ1) = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [wedge_parity_quadratic p hκ n hn r ℓ1, wedge_parity_quadratic p hκ n hn r ℓ2]
  · rw [wedge_parity_quadratic p hκ n hn (!r) ℓ1, wedge_parity_quadratic p hκ n hn r ℓ1]
    cases p.α <;> cases r <;> rfl
  · rw [wedge_parity_quadratic rule30Coef rfl n hn true ℓ1]
    rfl

end Rule30WedgeParity
end Ruliology.CellularAutomata
