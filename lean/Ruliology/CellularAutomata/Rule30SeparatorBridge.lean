module

public import Ruliology.CellularAutomata.Rule30WedgeBridge

/-!
# `RW` implies a separator for hard-core streams

A stream `e` is hard-core when all its symbols are binary and no two adjacent symbols are both `1`.
With `inverse` and the wedge operations of `Rule30WedgeBridge`, this module proves, from the open
hypothesis `RW` alone and with no finite census:

* `rw_forces_eventual_twos`, `inverse_eventual_twos`: a hard-core stream whose inverse diagonal is
  eventually constant `c ∈ {2, 3}` has an eventually-`2` structure that contradicts `RW`;
* `rw_implies_constant_tail_separator`: no hard-core `e` has `inverse e` eventually constant `c`
  (`ConstantTailSeparator`);
* `rw_implies_orbit_separator`: no hard-core `e` has `inverse e = liftWord u (const c)` for a word `u`
  over `{0, 1, 2}` (`OrbitSeparator`), where `lift` and `unphi` invert the pair step on one symbol.

For how `RW` and the separators relate to `Rule30PeriodTwo.Q01` and to mortality of the auxiliary frontier
(`Rule30AlternatingTraceBridge.Mortality`), which is equivalent to `Q01`, see `Rule30SEPToPeriodTwo` and
`Rule30SeparatorQ01`: `Q01` implies the separators (`Rule30SeparatorQ01.Q01_sep`); whether `RW` or the
separators imply `Q01`, and whether `Q01` implies `RW`, is open.

Control `no_pull_without_hard_core_control`: the hard-core condition is needed. Nothing here proves `RW`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30SeparatorBridge

open Rule30WedgeBridge


def shiftN (e : Stream) (n : Nat) : Stream := fun t => e (t+n)

theorem shiftN_succ (e : Stream) (n : Nat) :
    shiftN e (n+1) = shift (shiftN e n) := by
  funext t
  simp only [shiftN, shift]
  congr 1 <;> omega

theorem rotated_iterate (e : Stream) (n t : Nat) :
    wedge n (shiftN e n) t = inverse e (t+2*n) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [shiftN_succ, wedge_shift, ih]
    congr 1 <;> omega

def HardCore (e : Stream) : Prop :=
  (∀ i, binary (e i)) ∧ ∀ i, ¬(e i=1 ∧ e (i+1)=1)

def EventuallyConstant (x : Stream) (c : Sym) : Prop :=
  ∃ N, ∀ t, N ≤ t → x t = c

def ConstantTailSeparator : Prop :=
  ∀ c, constantTail c → ∀ e, HardCore e → ¬EventuallyConstant (inverse e) c

theorem hc_shift (e : Stream) (n : Nat) (h : HardCore e) :
    HardCore (shiftN e n) := by
  constructor
  · intro i
    exact h.1 (i+n)
  · intro i hh
    apply h.2 (i+n)
    simpa only [shiftN, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- Explicit placement of every late pull; the last binary symbol is kept. -/
theorem late_pull_witness (e : Stream) (c : Sym) (N m : Nat)
    (hh : HardCore e) (hc : ∀ t, N ≤ t → inverse e t=c)
    (hm : 3*(N+1) ≤ m) (hp : e (m-1)=1 ∧ e m=2) :
    RWWitness (m/3) (m%3) c (shiftN e (m/3)) := by
  let n := m/3
  let r := m%3
  have heq : 3*n+r=m := by
    have h := Nat.mod_add_div m 3
    dsimp [n, r]
    omega
  have hr : r<3 := Nat.mod_lt m (by decide)
  have hn : 1≤n := by omega
  have hN : N≤2*n := by omega
  change RWWitness n r c (shiftN e n)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i _
    exact hh.1 (i+n)
  · intro i hi _ hp'
    apply hh.2 ((i-1)+n)
    constructor
    · exact hp'.1
    · have hindex : (i-1)+n+1=i+n := by omega
      rw [hindex]
      exact hp'.2
  · intro t _
    rw [rotated_iterate]
    exact hc (t+2*n) (by omega)
  · change e ((2*n+r-1)+n)=1
    have hindex : (2*n+r-1)+n=m-1 := by omega
    rw [hindex]
    exact hp.1
  · change e ((2*n+r)+n)=2
    have hindex : (2*n+r)+n=m := by omega
    rw [hindex]
    exact hp.2

theorem rw_forces_eventual_twos (hrw : RW) (e : Stream) (c : Sym)
    (ht : constantTail c) (hh : HardCore e)
    (N : Nat) (hc : ∀ t, N ≤ t → inverse e t=c) :
    ∀ i, 3*(N+1) ≤ i → e i=2 := by
  intro i hi
  rcases hh.1 i with h1 | h2
  · have hnext : e (i+1)=2 := by
      rcases hh.1 (i+1) with hbad | hok
      · exact False.elim (hh.2 i ⟨h1,hbad⟩)
      · exact hok
    have hm : 3*(N+1)≤i+1 := by omega
    have hdiv : 1≤(i+1)/3 := by omega
    have hmod : (i+1)%3≤2 := by omega
    have witness := late_pull_witness e c N (i+1) hh hc hm
      (by simpa only [Nat.add_sub_cancel] using And.intro h1 hnext)
    exact False.elim (hrw ((i+1)/3) hdiv ((i+1)%3) hmod c ht
      (shiftN e ((i+1)/3)) witness)
  · exact h2

def alternatingCut (t : Nat) : Sym := if t%2=0 then 1 else 2

theorem alternating_rule (t : Nat) :
    phi (alternatingCut t) (alternatingCut (t+1)) = alternatingCut (t+2) := by
  have hlt := Nat.mod_lt t (by decide : 0<2)
  by_cases h : t%2=0
  · have h1 : (t+1)%2=1 := by omega
    have h2 : (t+2)%2=0 := by omega
    simp [alternatingCut, h, h1, h2, phi]
  · have h1 : (t+1)%2=0 := by omega
    have h2 : (t+2)%2=1 := by omega
    simp [alternatingCut, h, h1, h2, phi]

theorem alternating_two (t : Nat) : alternatingCut (t+2)=alternatingCut t := by
  unfold alternatingCut
  have h : (t+2)%2=t%2 := by omega
  rw [h]

theorem inverse_twos : inverse (fun _ => 2) = alternatingCut := by
  have hc (t : Nat) : ∀ j, cone (fun _ => 2) t j=alternatingCut t := by
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro j
      match t with
      | 0 => rfl
      | 1 => rfl
      | t+2 =>
        simp only [cone]
        rw [ih t (by omega), ih (t+1) (by omega), alternating_rule]
  funext t
  exact hc t 0

theorem peel_alternating : peel alternatingCut=alternatingCut := by
  funext t
  exact (alternating_rule t).trans (alternating_two t)

theorem peelPow_alternating (n : Nat) : peelPow n alternatingCut=alternatingCut := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [peelPow, ih, peel_alternating]

theorem inverse_eventual_twos (e : Stream) (K : Nat)
    (h : ∀ i, K≤i → e i=2) :
    ∀ t, inverse e (t+2*K)=alternatingCut t := by
  have hs : shiftN e K=(fun _ => 2) := by
    funext i
    exact h (i+K) (by omega)
  intro t
  rw [← rotated_iterate, hs]
  unfold wedge
  rw [inverse_twos, peelPow_alternating]

/-- All lengths, both tails, all hard-core endpoints: no census premise. -/
theorem rw_implies_constant_tail_separator (hrw : RW) : ConstantTailSeparator := by
  intro c ht e hh ⟨N,hc⟩
  have he := rw_forces_eventual_twos hrw e c ht hh N hc
  have hi := inverse_eventual_twos e (3*(N+1)) he (2*N)
  have ha : alternatingCut (2*N)=1 := by simp [alternatingCut]
  rw [ha, hc (2*N+2*(3*(N+1))) (by omega)] at hi
  rcases ht with h2 | h3 <;> subst c <;> contradiction

/-! The orbit separator uses the entire finite label word, not a bounded
summary. It is proved even for labels 0,1,2,3; the normalized alphabet
0,1,2 of the ladder is a restriction. -/

def unphi (l a : Sym) : Sym :=
  match l.val, a.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 3 | 0, _ => 2
  | 2, 0 => 2 | 2, 1 => 3 | 2, 2 => 1 | 2, _ => 0
  | _, 0 => 3 | _, 1 => 2 | _, 2 => 1 | _, _ => 0

theorem phi_unphi : ∀ l a : Sym, phi l (unphi l a)=a := by decide
theorem unphi_phi : ∀ l r : Sym, unphi l (phi l r)=r := by decide

def lift (a : Sym) (v : Stream) : Stream
  | 0 => a
  | j+1 => unphi (lift a v j) (v (j+1))

theorem peel_lift (a : Sym) (v : Stream) : peel (lift a v)=shift v := by
  funext j
  exact phi_unphi (lift a v j) (v (j+1))

def liftWord : List Sym → Stream → Stream
  | [], v => v
  | a::u, v => liftWord u (lift a v)

theorem peelPow_liftWord (u : List Sym) (v : Stream) :
    peelPow u.length (liftWord u v)=shiftN v u.length := by
  induction u generalizing v with
  | nil => rfl
  | cons a u ih =>
    simp only [List.length_cons, liftWord, peelPow, ih]
    funext t
    change phi (lift a v (t+u.length)) (lift a v ((t+1)+u.length)) =
      v (t+(u.length+1))
    have hindex : (t+1)+u.length=(t+u.length)+1 := by omega
    rw [hindex, lift, phi_unphi]
    congr 1 <;> omega

def prependTwos (e : Stream) (d : Nat) : Stream :=
  fun i => if i<d then 2 else e (i-d)

theorem shift_prepend (e : Stream) (d : Nat) : shiftN (prependTwos e d) d=e := by
  funext t
  have hn : ¬t+d<d := by omega
  simp [shiftN, prependTwos, hn]

theorem hc_prepend (e : Stream) (d : Nat) (hh : HardCore e) :
    HardCore (prependTwos e d) := by
  constructor
  · intro i
    by_cases hi : i<d
    · simp [prependTwos, hi, binary]
    · simpa [prependTwos, hi] using hh.1 (i-d)
  · intro i h
    by_cases hi : i<d
    · have : (2 : Sym)=1 := by simpa [prependTwos,hi] using h.1
      contradiction
    · have hn : ¬i+1<d := by omega
      have hindex : i+1-d=(i-d)+1 := by omega
      apply hh.2 (i-d)
      simpa only [prependTwos, hi, hn, hindex, ↓reduceIte] using h

def OrbitSeparator : Prop :=
  ∀ c, constantTail c → ∀ u : List Sym,
    (∀ a∈u, a.val≤2) → ∀ e, HardCore e → liftWord u (fun _=>c) ≠ inverse e

theorem constant_separator_implies_full_orbit_separator
    (hs : ConstantTailSeparator) (c : Sym) (hc : constantTail c)
    (u : List Sym) (e : Stream) (hh : HardCore e) :
    liftWord u (fun _=>c) ≠ inverse e := by
  intro heq
  have hp : peelPow u.length (inverse e)=(fun _=>c) := by
    rw [← heq, peelPow_liftWord]
    rfl
  apply hs c hc (prependTwos e u.length) (hc_prepend e u.length hh)
  refine ⟨2*u.length, ?_⟩
  intro t ht
  have hi := rotated_iterate (prependTwos e u.length) u.length (t-2*u.length)
  rw [shift_prepend] at hi
  have hindex : t-2*u.length+2*u.length=t := by omega
  rw [hindex] at hi
  change peelPow u.length (inverse e) (t-2*u.length)=_ at hi
  rw [hp] at hi
  exact hi.symm

/-- This is the normalized O_c ∩ I(HC) separator from the ladder. -/
theorem rw_implies_orbit_separator (hrw : RW) : OrbitSeparator := by
  intro c hc u _ e hh
  exact constant_separator_implies_full_orbit_separator
    (rw_implies_constant_tail_separator hrw) c hc u e hh

/-- The no-pull-to-twos step fails if the no-11 guard is removed. -/
theorem no_pull_without_hard_core_control :
    (∀ i, binary ((fun _ : Nat => (1 : Sym)) i)) ∧
    (∀ _i : Nat, ¬((1 : Sym)=1 ∧ (1 : Sym)=2)) ∧
    ¬EventuallyConstant (fun _=>1) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Or.inl rfl
  · intro i h
    exact (by decide : (1 : Sym)≠2) h.2
  · intro ⟨N,h⟩
    exact (by decide : (1 : Sym)≠2) (h N (by omega))


/-! ### Semigroup laws for `shiftN`, `liftWord`, and `prependTwos`, and constant-inverse exclusion -/

/-- **Semigroup Laws for `shiftN`, `liftWord`, and `prependTwos`, and Constant-Inverse Exclusion (`shiftN_liftWord_append_and_separator_iff`).** -/
theorem shiftN_liftWord_append_and_separator_iff
    (e : Stream) (m n : Nat) (u w : List Sym) (v : Stream) :
    shiftN (shiftN e m) n = shiftN e (m + n) ∧
    liftWord (u ++ w) v = liftWord w (liftWord u v) ∧
    prependTwos (prependTwos e m) n = prependTwos e (n + m) ∧
    (OrbitSeparator → ∀ c, constantTail c → ∀ d, HardCore d → (fun _ => c) ≠ inverse d) := by
  have hshift : shiftN (shiftN e m) n = shiftN e (m + n) := by
    funext t; simp [shiftN, Nat.add_assoc, Nat.add_comm m n]
  have hlift : ∀ (l1 l2 : List Sym) (st : Stream),
      liftWord (l1 ++ l2) st = liftWord l2 (liftWord l1 st) := by
    intro l1
    induction l1 with
    | nil => intro l2 st; rfl
    | cons a l1 ih => intro l2 st; exact ih l2 (lift a st)
  have hprep : prependTwos (prependTwos e m) n = prependTwos e (n + m) := by
    funext i
    unfold prependTwos
    by_cases h1 : i < n
    · simp [h1, show i < n + m by omega]
    · by_cases h2 : i - n < m
      · simp [h1, h2, show i < n + m by omega]
      · simp [h1, h2, show ¬ i < n + m by omega, show i - n - m = i - (n + m) by omega]
  refine ⟨hshift, hlift u w v, hprep, fun horb c hc d hh => ?_⟩
  exact horb c hc [] (by simp) d hh

end Rule30SeparatorBridge
end Ruliology.CellularAutomata
