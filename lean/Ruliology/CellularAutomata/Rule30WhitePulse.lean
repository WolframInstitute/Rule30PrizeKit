module

public import Ruliology.CellularAutomata.Rule30FiniteBlackRuns
public import Ruliology.CellularAutomata.Rule30LightCone
public import Ruliology.CellularAutomata.Rule30FiniteStrips

@[expose] public section

/-!
# A shield survives every short pulse

A black run in the first right column creates a striped block. An interior black
cell of that block survives an arbitrary boundary pulse of length m by locality.
These lemmas quantify the absorbing, synchronized regime without enumerating tails.
They do not prove every periodic history enters that regime.
-/
namespace Ruliology.CellularAutomata.Rule30WhitePulse
open Rule30Jen Rule30Realization Rule30FiniteBlackRuns Rule30ZeroBoundaryBarriers

/-- A spatially stationary stripe, black at odd offsets from column i. -/
def stripe (i p : Int) : Bool := decide ((p - i) % 2 = 1)

theorem stripe_step (i p : Int) :
    rule (stripe i (p - 1)) (stripe i p) (stripe i (p + 1)) = stripe i p := by
  have hp : (p - i) % 2 = 0 ∨ (p - i) % 2 = 1 := by omega
  rcases hp with hp | hp
  · have hl : (p - 1 - i) % 2 = 1 := by omega
    have hr : (p + 1 - i) % 2 = 1 := by omega
    simp [stripe, rule, hp, hl, hr]
  · have hl : (p - 1 - i) % 2 = 0 := by omega
    have hr : (p + 1 - i) % 2 = 0 := by omega
    simp [stripe, rule, hp, hl, hr]

theorem evol_stripe (i : Int) : ∀ t p, evol (stripe i) t p = stripe i p
  | 0, p => rfl
  | t+1, p => by
    change rule (evol (stripe i) t (p-1)) (evol (stripe i) t p)
      (evol (stripe i) t (p+1)) = stripe i p
    rw [evol_stripe i t (p-1), evol_stripe i t p, evol_stripe i t (p+1), stripe_step]

/-- The nine-black shield is a whole stripe on its forced interval. -/
theorem shield_stripe (x : Int → Bool) (i : Int) (a j : Nat)
    (hblack : ∀ s, s < 9*j → evol x (a+s) (i+1) = true)
    (p : Int) (hlo : i+2 ≤ p) (hhi : p ≤ i+2*j+1) :
    evol x (a+9*j) p = stripe i p := by
  have hs := black_shield x (i+1) j a hblack
  let k : Nat := ((p-i)/2).toNat
  have hk : (k : Int) = (p-i)/2 := by
    dsimp [k]
    exact Int.toNat_of_nonneg (by omega)
  have hklo : 1 ≤ k := by omega
  have hkhi : k ≤ j := by omega
  have hp : (p-i)%2 = 0 ∨ (p-i)%2 = 1 := by omega
  rcases hp with hp | hp
  · have he : p = (i+1)+2*(k:Int)-1 := by omega
    rw [he, (hs k hklo hkhi).1]
    simp [stripe, show ((i+1)+2*(k:Int)-1-i)%2 = 0 by omega]
  · have he : p = (i+1)+2*(k:Int) := by omega
    rw [he, (hs k hklo hkhi).2]
    simp [stripe, show ((i+1)+2*(k:Int)-i)%2 = 1 by omega]

/-- **An arbitrary m-step pulse cannot erase the entire shield.** After 9(m+1) black steps
of column i+1, a black cell survives any following m steps at an explicitly bounded distance.
There is no hypothesis on the boundary column during those m steps. -/
theorem black_survives_pulse (x : Int → Bool) (i : Int) (a m : Nat)
    (hblack : ∀ s, s < 9*(m+1) → evol x (a+s) (i+1) = true) :
    evol x (a+9*(m+1)+m) (i+(2*(m/2)+3 : Nat)) = true := by
  let q : Nat := 2*(m/2)+3
  have hqlo : m+2 ≤ q := by dsimp [q]; omega
  have hqhi : q ≤ m+3 := by dsimp [q]; omega
  have hloc := Rule30LightCone.evol_window (x := stripe i)
    (x' := fun p => evol x (a+9*(m+1)) p) (t := m) (p := i+q)
    (fun p hp1 hp2 => shield_stripe x i a (m+1) hblack p (by omega) (by omega))
  rw [evol_restart, evol_stripe] at hloc
  rw [hloc]
  simp only [stripe, decide_eq_true_eq]
  dsimp [q]
  omega

/-- During n white boundary steps, any black cell initially n+1 places to the right forces
column i+1 to be black by the end. No assumption is needed on the intervening cells. -/
theorem black_reaches_boundary (x : Int → Bool) : ∀ (n : Nat) (i : Int) (a : Nat),
    (∀ s, s < n → evol x (a+s) i = false) →
    evol x a (i+(n+1 : Nat)) = true → evol x (a+n) (i+1) = true
  | 0, i, a, _, hb => by simpa using hb
  | n+1, i, a, hw, hb => by
    cases hf : evol x (a+(n+1)) (i+1)
    · have h1 : ∀ s, s ≤ n+1 → evol x (a+s) (i+1) = false := by
        intro s hs
        cases hb1 : evol x (a+s) (i+1)
        · rfl
        · have hm := Rule30FiniteBlackRuns.black_stays x i (a+s) (n+1-s)
            (fun k hk => by
              have hh := hw (s+k) (by omega)
              rwa [show a+(s+k) = (a+s)+k by omega] at hh)
            hb1 (n+1-s) (Nat.le_refl _)
          rw [show a+s+(n+1-s) = a+(n+1) by omega, hf] at hm
          exact absurd hm (by decide)
      have hb' : evol x a ((i+1)+(n+1 : Nat)) = true := by
        rw [show (i+1)+((n+1 : Nat) : Int) = i+((n+1+1 : Nat) : Int) by omega]
        exact hb
      have ih := black_reaches_boundary x n (i+1) a (fun s hs => h1 s (by omega)) hb'
      have hstep : evol x (a+(n+1)) (i+1) =
          rule (evol x (a+n) i) (evol x (a+n) (i+1)) (evol x (a+n) (i+2)) := by
        rw [show a+(n+1) = (a+n)+1 by omega]
        change rule (evol x (a+n) (i+1-1)) (evol x (a+n) (i+1))
          (evol x (a+n) (i+1+1)) = _
        congr 2 <;> omega
      rw [hw n (by omega), h1 n (by omega),
        show i+2 = (i+1)+1 by omega, ih, hf] at hstep
      exact absurd hstep (by decide)
    · rfl

/-- **One absorbing step.** Once a white interval has a sufficiently early black neighbour,
any following m-step pulse leaves a black cell close enough that the next white interval
has a black neighbour after at most m+2 steps. The pulse is entirely arbitrary. -/
theorem white_pulse_return (x : Int → Bool) (i : Int) (a r m s : Nat)
    (hw : ∀ k, k < r → evol x (a+k) i = false)
    (hearly : evol x (a+s) (i+1) = true) (hs : s+9*(m+1) ≤ r)
    (hnext : ∀ k, k < r → evol x (a+r+m+k) i = false) :
    ∀ k, m+2 ≤ k → k ≤ r → evol x (a+r+m+k) (i+1) = true := by
  have hhold := Rule30FiniteBlackRuns.black_stays x i (a+s) (r-s)
    (fun k hk => by
      have hh := hw (s+k) (by omega)
      rwa [show a+(s+k) = (a+s)+k by omega] at hh) hearly
  have hlast : ∀ k, k < 9*(m+1) → evol x (a+r-9*(m+1)+k) (i+1) = true := by
    intro k hk
    have hh := hhold (r-9*(m+1)-s+k) (by omega)
    rwa [show a+s+(r-9*(m+1)-s+k) = a+r-9*(m+1)+k by omega] at hh
  have hsurv := black_survives_pulse x i (a+r-9*(m+1)) m hlast
  rw [show a+r-9*(m+1)+9*(m+1)+m = a+r+m by omega] at hsurv
  let q : Nat := 2*(m/2)+3
  have hqlo : 1 ≤ q := by dsimp [q]; omega
  have hqhi : q-1 ≤ m+2 := by dsimp [q]; omega
  have hqr : q-1 ≤ r := by omega
  have harr := black_reaches_boundary x (q-1) i (a+r+m)
    (fun k hk => hnext k (by omega)) (by simpa only [show q-1+1 = q by omega] using hsurv)
  have hstay := Rule30FiniteBlackRuns.black_stays x i ((a+r+m)+(q-1)) (r-(q-1))
    (fun k hk => by
      have hh := hnext (q-1+k) (by omega)
      rwa [show a+r+m+(q-1+k) = ((a+r+m)+(q-1))+k by omega] at hh) harr
  intro k hk hkr
  have hh := hstay (k-(q-1)) (by omega)
  rwa [show (a+r+m)+(q-1)+(k-(q-1)) = a+r+m+k by omega] at hh

/-- **The absorbing regime persists for arbitrary pulses.** If every cycle starts with r white
steps, r≥10m+11, one early black neighbour forces all later white intervals to have a black
neighbour from phase m+2 on. No periodicity or restriction on the m pulse bits is assumed. -/
theorem absorbing_white_cycles (x : Int → Bool) (i : Int) (a r m s : Nat)
    (hr : 10*m+11 ≤ r)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false)
    (hearly : evol x (a+s) (i+1) = true) (hs : s+9*(m+1) ≤ r) :
    ∀ n, 1 ≤ n → ∀ k, m+2 ≤ k → k ≤ r →
      evol x (a+n*(r+m)+k) (i+1) = true := by
  have hcycle : ∀ n, ∀ k, m+2 ≤ k → k ≤ r →
      evol x (a+(n+1)*(r+m)+k) (i+1) = true := by
    intro n
    induction n with
    | zero =>
      simpa only [Nat.zero_add, Nat.one_mul, Nat.add_assoc] using
        white_pulse_return x i a r m s (by simpa using hw 0) hearly hs
          (by simpa [Nat.one_mul, Nat.add_assoc] using hw 1)
    | succ n ih =>
      have h := white_pulse_return x i (a+(n+1)*(r+m)) r m (m+2)
        (hw (n+1)) (ih (m+2) (Nat.le_refl _) (by omega)) (by omega)
        (fun k hk => by
          have hh := hw (n+2) k hk
          rwa [show a+(n+2)*(r+m)+k = a+(n+1)*(r+m)+r+m+k by
            rw [show n+2 = (n+1)+1 by omega, Nat.succ_mul]; omega] at hh)
      intro k hk hkr
      have hh := h k hk hkr
      rwa [show a+(n+1)*(r+m)+r+m+k = a+(n+1+1)*(r+m)+k by
        rw [Nat.succ_mul (n+1) (r+m)]; omega] at hh
  intro n hn k hk hkr
  have hh := hcycle (n-1) k hk hkr
  rwa [show n-1+1 = n by omega] at hh

/-- **Synchronization of the neighbour.** For a periodic boundary with r white phases and m
arbitrary pulse phases, r≥10m+11, entering the early-black regime forces the entire neighbour
column to be eventually periodic. This statement is independent of the initial configuration. -/
theorem periodic_neighbour_of_early_black (x : Int → Bool) (i : Int) (a r m s : Nat)
    (hr : 10*m+11 ≤ r)
    (hper : ∀ t, a ≤ t → evol x (t+(r+m)) i = evol x t i)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false)
    (hearly : evol x (a+s) (i+1) = true) (hs : s+9*(m+1) ≤ r) :
    EventuallyPeriodic (fun t => evol x t (i+1)) := by
  let b : Nat → Nat := fun n => a+(n+1)*(r+m)+r
  have hb (n : Nat) : b (n+1) = b n+(r+m) := by
    dsimp [b]
    rw [Nat.succ_mul (n+1) (r+m)]
    omega
  have hbounds (n : Nat) : a ≤ b n ∧ r ≤ b n := by dsimp [b]; omega
  have habs := absorbing_white_cycles x i a r m s hr hw hearly hs
  have hend (n : Nat) : evol x (b n) (i+1) = true := by
    exact habs (n+1) (by omega) r (by omega) (Nat.le_refl _)
  have hlast (n : Nat) : ∀ k, k < 9*(m+1) →
      evol x (b n-9*(m+1)+k) (i+1) = true := by
    intro k hk
    have hh := habs (n+1) (by omega) (r-9*(m+1)+k) (by omega) (by omega)
    rwa [show a+(n+1)*(r+m)+(r-9*(m+1)+k) = b n-9*(m+1)+k by
      dsimp [b]; omega] at hh
  have hstripe (n : Nat) (p : Int) (hlo : i+2 ≤ p) (hhi : p ≤ i+2*(m+1)+1) :
      evol x (b n) p = stripe i p := by
    have hh := shield_stripe x i (b n-9*(m+1)) (m+1) (hlast n) p hlo hhi
    rwa [show b n-9*(m+1)+9*(m+1) = b n by have := (hbounds n).2; omega] at hh
  have hrow (n : Nat) (p : Int) (hlo : i+1 ≤ p) (hhi : p ≤ i+(2*m+3 : Nat)) :
      evol x (b n) p = evol x (b (n+1)) p := by
    by_cases hp : p = i+1
    · rw [hp, hend n, hend (n+1)]
    · rw [hstripe n p (by omega) (by omega), hstripe (n+1) p (by omega) (by omega)]
  have hdriver (n : Nat) : ∀ k, evol x (b n+k) i = evol x (b (n+1)+k) i := by
    intro k
    have hh := hper (b n+k) (by have := (hbounds n).1; omega)
    rw [hb]
    rw [show b n+k+(r+m) = b n+(r+m)+k by omega] at hh
    exact hh.symm
  have hlate (n k : Nat) (hk : m ≤ k) :
      b n+k = a+((n+1)+1)*(r+m)+(k-m) := by
    dsimp [b]
    rw [Nat.succ_mul (n+1) (r+m)]
    omega
  have hblock (n k : Nat) (hk : k < r+m) :
      evol x (b n+k) (i+1) = evol x (b (n+1)+k) (i+1) := by
    by_cases he : k ≤ 2*m+2
    · exact Rule30FiniteBlackRuns.cone_agree x i (b n) (b (n+1)) (2*m+3)
        (hdriver n) (hrow n) k (i+1) (by omega) (by omega)
    · rw [hlate n k (by omega), hlate (n+1) k (by omega),
        habs ((n+1)+1) (by omega) (k-m) (by omega) (by omega),
        habs (((n+1)+1)+1) (by omega) (k-m) (by omega) (by omega)]
  refine ⟨b 0, r+m, by omega, fun t ht => ?_⟩
  let n := (t-b 0)/(r+m)
  let k := (t-b 0)%(r+m)
  have hk : k < r+m := Nat.mod_lt _ (by omega)
  have hb0 : b n = b 0+n*(r+m) := by
    dsimp [b]
    rw [Nat.succ_mul n (r+m)]
    omega
  have heq : t = b n+k := by
    have hd := Nat.div_add_mod (t-b 0) (r+m)
    rw [Nat.mul_comm] at hd
    dsimp [n, k] at hb0 ⊢
    omega
  have hh := hblock n k hk
  rw [← heq, hb, show b n+(r+m)+k = (b n+k)+(r+m) by omega, ← heq] at hh
  exact hh.symm

/-- **General early-arrival exclusion.** A periodic boundary column in a left-finite nonzero
configuration cannot enter the synchronized early-black regime. Any hypothetical periodic
word 0^r u with r≥10|u|+11 must therefore keep its right neighbour white through the early
part of every white run. This reduces the unbounded-tail question to the late-arrival regime. -/
theorem no_periodic_boundary_early_black {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (a r m s : Nat) (hr : 10*m+11 ≤ r)
    (hper : ∀ t, a ≤ t → evol x (t+(r+m)) i = evol x t i)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false)
    (hearly : evol x (a+s) (i+1) = true) (hs : s+9*(m+1) ≤ r) : False :=
  Rule30FiniteConfigs.not_adjacent hlo hzero i ⟨a, r+m, by omega, hper⟩
    (periodic_neighbour_of_early_black x i a r m s hr hper hw hearly hs)

/-- **Necessary early-white condition, in every cycle.** A periodic boundary with a sufficiently
long white block forces its right neighbour to remain white until the final 9(m+1) white steps. -/
theorem periodic_white_cycles_force_early_white {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (a r m : Nat) (hr : 10*m+11 ≤ r)
    (hper : ∀ t, a ≤ t → evol x (t+(r+m)) i = evol x t i)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false) :
    ∀ n s, s+9*(m+1) ≤ r → evol x (a+n*(r+m)+s) (i+1) = false := by
  intro n s hs
  cases hb : evol x (a+n*(r+m)+s) (i+1)
  · rfl
  · exact False.elim (no_periodic_boundary_early_black hlo hzero i (a+n*(r+m)) r m s hr
      (fun t ht => hper t (by omega))
      (fun q k hk => by
        have hh := hw (n+q) k hk
        simpa only [Nat.add_mul, Nat.add_assoc] using hh) hb hs)

/-- **A wide spatial white prefix is necessary at every period start.** Any closer black cell
would reach the right neighbour in a forbidden early phase. -/
theorem periodic_white_cycles_force_empty_prefix {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (a r m : Nat) (hr : 10*m+11 ≤ r)
    (hper : ∀ t, a ≤ t → evol x (t+(r+m)) i = evol x t i)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false) :
    ∀ n q, 1 ≤ q → q-1+9*(m+1) ≤ r → evol x (a+n*(r+m)) (i+q) = false := by
  intro n q hq hqr
  cases hb : evol x (a+n*(r+m)) (i+q)
  · rfl
  · have harr := black_reaches_boundary x (q-1) i (a+n*(r+m))
      (fun k hk => hw n k (by omega)) (by simpa only [show q-1+1 = q by omega] using hb)
    have hz := periodic_white_cycles_force_early_white hlo hzero i a r m hr hper hw n (q-1) hqr
    rw [hz] at harr
    exact absurd harr (by decide)

/-- **Arbitrary-tail reduction.** For every finite tail u, an eventual word 0^r u with
r≥10|u|+11 forces column i+1 white throughout every early phase of its white block.
No bound is placed on |u|, and no certificate or finite case split is used here. -/
theorem white_padding_forces_early_white {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (r : Nat) (hr : 10*u.length+11 ≤ r)
    (hword : Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u)) :
    ∃ T, (∀ t, T ≤ t → evol x t i =
      (List.replicate r false ++ u).getD ((t-T)%(r+u.length)) false) ∧
      ∀ n s, s+9*(u.length+1) ≤ r →
        evol x (T+n*(r+u.length)+s) (i+1) = false := by
  obtain ⟨T, hT⟩ := hword
  have hlen : (List.replicate r false ++ u).length = r+u.length := by simp
  have hT' : ∀ t, T ≤ t → evol x t i =
      (List.replicate r false ++ u).getD ((t-T)%(r+u.length)) false := by
    simpa only [hlen] using hT
  refine ⟨T, hT', periodic_white_cycles_force_early_white hlo hzero i T r u.length hr ?_ ?_⟩
  · intro t ht
    rw [hT' t ht, hT' (t+(r+u.length)) (by omega),
      show t+(r+u.length)-T = (t-T)+(r+u.length) by omega, Nat.add_mod_right]
  · intro n k hk
    rw [hT' _ (by omega), show T+n*(r+u.length)+k-T = k+n*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (l₁ := List.replicate r false) (l₂ := u) (by simpa using hk),
      List.getElem?_replicate_of_lt hk]
    rfl

/-! ## Spatial period-2 and shift-complement symmetries of `stripe`, and finite-configuration pulse laws -/

/-- **Spatial Period-2 and Shift-Complement Symmetries of `stripe` (`stripe_symmetries`).** -/
theorem stripe_symmetries (i p k : Int) :
    stripe i (p + 2 * k) = stripe i p ∧
    stripe (i + 2 * k) p = stripe i p ∧
    stripe i (p + 1) = !stripe i p ∧
    stripe (i + 1) p = !stripe i p := by
  unfold stripe
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · cases h : decide ((p - i) % 2 = 1)
    · have h0 : (p - i) % 2 ≠ 1 := of_decide_eq_false h
      exact decide_eq_true (by omega)
    · have h1 : (p - i) % 2 = 1 := of_decide_eq_true h
      exact decide_eq_false (by omega)
  · cases h : decide ((p - i) % 2 = 1)
    · have h0 : (p - i) % 2 ≠ 1 := of_decide_eq_false h
      exact decide_eq_true (by omega)
    · have h1 : (p - i) % 2 = 1 := of_decide_eq_true h
      exact decide_eq_false (by omega)

/-- **Finite-Configuration Early-Black Exclusion and Early-White Reduction (`white_pulse_finite_config_laws`).** -/
theorem white_pulse_finite_config_laws {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true) (i : Int) :
    (∀ (a r m s : Nat), 10 * m + 11 ≤ r →
      (∀ t, a ≤ t → evol x (t + (r + m)) i = evol x t i) →
      (∀ n k, k < r → evol x (a + n * (r + m) + k) i = false) →
      evol x (a + s) (i + 1) = true → s + 9 * (m + 1) ≤ r → False) ∧
    (∀ (u : List Bool) (r : Nat), 10 * u.length + 11 ≤ r →
      Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) →
      ∃ T, (∀ t, T ≤ t → evol x t i =
          (List.replicate r false ++ u).getD ((t - T) % (r + u.length)) false) ∧
        ∀ n s, s + 9 * (u.length + 1) ≤ r →
          evol x (T + n * (r + u.length) + s) (i + 1) = false) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact ⟨fun a r m s hr hper hw hearly hs =>
           no_periodic_boundary_early_black hlo hzero i a r m s hr hper hw hearly hs,
         fun u r hr hword =>
           white_padding_forces_early_white hlo hzero i u r hr hword⟩

end Ruliology.CellularAutomata.Rule30WhitePulse
