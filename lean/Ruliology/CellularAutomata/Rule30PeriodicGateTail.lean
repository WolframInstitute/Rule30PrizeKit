module
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! Arbitrary inverse-head histories on the periodic gap-five spatial tail.
This concerns one concrete periodic tail, not arbitrary legal futures. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30PeriodicGateTail
open Rule30ZeroBoundary
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def words : List Nat := [513, 255, 128, 191, 736, 911, 40, 955, 102, 972, 520, 712, 940, 570, 675, 490, 798, 625, 71, 84, 125, 579, 350, 1008, 518, 757, 397, 315, 802, 682, 767, 384, 831, 32, 815, 184, 995, 10, 1006, 537, 243, 130, 178, 235, 654, 936, 634, 711, 412, 785, 21, 287, 912, 599, 252, 641, 445, 355, 846, 712, 682, 959, 96, 975, 8, 971, 46, 1016, 514, 763, 390, 828, 544, 556, 826, 675, 234, 670, 945, 103, 452, 261, 839, 228, 917, 63, 416, 367, 856, 723, 178, 682, 1007, 24, 1011, 2, 1010, 523, 254, 640, 958, 609, 207, 136, 139, 718, 936, 570, 679, 492, 793, 113, 321, 977, 57, 485, 783, 104, 859, 214, 948, 556, 682, 1019, 6, 1020, 512, 764, 898, 575, 160, 751, 408, 819, 34, 802, 691, 234, 654, 937, 123, 454, 284, 336, 500, 270, 377, 963, 26, 982, 565, 237, 139, 682, 1022]

def profileRow (p k : Nat) : Bool := Nat.testBit (words[k % 155]?.getD 0) (p % 10)

theorem phase_mod (p : Nat) : profileRow (p%10) = profileRow p := by
  funext k
  simp only [profileRow, Nat.mod_mod]

theorem phase_add_mod (p q : Nat) : profileRow (p%10+q) = profileRow (p+q) := by
  funext k
  unfold profileRow
  have h : (p%10+q)%10 = (p+q)%10 := by omega
  rw [h]

theorem phase_ten (p : Nat) : profileRow (p+10) = profileRow p := by
  funext k
  unfold profileRow
  have h : (p+10)%10 = p%10 := by omega
  rw [h]

def scan (y : Nat → Bool) : Nat → (Bool × Bool) → (Bool × Bool)
  | 0, s => s
  | n+1, s =>
      let q := scan y n s
      (q.2, xor (y n) (q.2 || q.1))

private theorem reference_certificate : ∀ p : Fin 10, ∀ k : Fin 155,
    profileRow p.val (k.val+2) = xor (profileRow (p.val+1) (k.val+1))
      (profileRow p.val (k.val+1) || profileRow p.val k.val) := by decide

private theorem sync_certificate : ∀ p : Fin 10, ∀ a b : Bool,
    scan (profileRow p.val) 155 (a,b) =
      (profileRow (p.val+9) 154, profileRow (p.val+9) 155) := by decide

theorem profile_step (p k : Nat) :
    profileRow p (k+2) = xor (profileRow (p+1) (k+1))
      (profileRow p (k+1) || profileRow p k) := by
  have h := reference_certificate ⟨p % 10, by omega⟩ ⟨k % 155, by omega⟩
  simpa [profileRow, Nat.add_mod] using h

theorem reference_rec (p k : Nat) :
    profileRow (p+9) (k+2) = xor (profileRow p (k+1))
      (profileRow (p+9) (k+1) || profileRow (p+9) k) := by
  have h := profile_step (p+9) k
  rw [show p+9+1 = p+10 by omega, phase_ten] at h
  exact h

theorem scan_sync (p : Nat) (a b : Bool) :
    scan (profileRow p) 155 (a,b) =
      (profileRow (p+9) 154, profileRow (p+9) 155) := by
  have h := sync_certificate ⟨p % 10, by omega⟩ a b
  rw [phase_mod p, phase_add_mod p 9] at h
  exact h

theorem scan_congr (x y : Nat → Bool) (n : Nat) (s : Bool × Bool)
    (h : ∀ i, i < n → x i = y i) : scan x n s = scan y n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [scan, scan, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem scan_back (b : Bool) (y : Nat → Bool) (m n : Nat) :
    scan (fun i => y (m+i+1)) n (back b y m, back b y (m+1)) =
      (back b y (m+n), back b y (m+n+1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [scan, ih]
      change (back b y (m+n+1), xor (y (m+n+1))
        (back b y (m+n+1) || back b y (m+n))) =
        (back b y (m+n+1), back b y (m+n+2))
      rfl

def Tail (offset p : Nat) (y : Nat → Bool) : Prop :=
  ∃ N, ∀ k, N ≤ k → y k = profileRow p (k+offset)

def EventuallyEq (x y : Nat → Bool) : Prop := ∃ N, ∀ k, N ≤ k → x k = y k

/-- Every inverse head reaches the preceding phase of the same carrier.
The input can have an arbitrary finite prefix. -/
theorem back_tail_bound (offset p : Nat) (y : Nat → Bool) (b : Bool) (N : Nat)
    (hy : ∀ k, N ≤ k → y k = profileRow p (k+offset)) :
    ∀ k, N+310 ≤ k → back b y k = profileRow (p+9) (k+offset) := by
  let Q := (N+offset+1)/155
  let m := N+155-((N+offset+1)%155)
  have ms : m+offset = 155*Q+154 := by dsimp [m,Q]; omega
  have hm : N ≤ m+1 := by dsimp [m]; omega
  have driver : ∀ i, i < 155 → y (m+i+1) = profileRow p i := by
    intro i hi
    rw [hy _ (by omega)]
    have index : m+i+1+offset = 155*(Q+1)+i := by omega
    rw [index]
    simp [profileRow, Nat.add_mod]
  have eq := scan_congr (fun i => y (m+i+1)) (profileRow p) 155
    (back b y m, back b y (m+1)) driver
  rw [scan_back] at eq
  have synced := eq.trans (scan_sync p (back b y m) (back b y (m+1)))
  let M := m+155
  have ref0 : profileRow (p+9) (M+offset) = profileRow (p+9) 154 := by
    have index : M+offset = 155*(Q+1)+154 := by dsimp [M]; omega
    rw [index]
    simp [profileRow, Nat.add_mod]
  have ref1 : profileRow (p+9) (M+1+offset) = profileRow (p+9) 155 := by
    have index : M+1+offset = 155*(Q+2) := by dsimp [M]; omega
    rw [index]
    simp [profileRow, Nat.add_mod]
  have pair : back b y M = profileRow (p+9) (M+offset) ∧
      back b y (M+1) = profileRow (p+9) (M+1+offset) := by
    exact ⟨(congrArg Prod.fst synced).trans ref0.symm,
      (congrArg Prod.snd synced).trans ref1.symm⟩
  have prop : ∀ r, back b y (M+r) = profileRow (p+9) (M+r+offset) ∧
      back b y (M+r+1) = profileRow (p+9) (M+r+1+offset) := by
    intro r
    induction r with
    | zero => simpa using pair
    | succ r ih =>
        refine ⟨ih.2, ?_⟩
        change xor (y (M+r+1)) (back b y (M+r+1) || back b y (M+r)) =
          profileRow (p+9) (M+r+2+offset)
        rw [hy _ (by dsimp [M]; omega), ih.1, ih.2]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (reference_rec p (M+r+offset)).symm
  intro k hk
  have hkm : M ≤ k := by dsimp [M,m]; omega
  simpa only [Nat.add_sub_of_le hkm] using (prop (k-M)).1

theorem back_tail (offset p : Nat) (y : Nat → Bool) (b : Bool)
    (ht : Tail offset p y) : Tail offset (p+9) (back b y) := by
  obtain ⟨N,hy⟩ := ht
  exact ⟨N+310, back_tail_bound offset p y b N hy⟩

def history (h : Nat → Bool) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, y => y
  | n+1, y => back (h n) (history h n y)

theorem history_tail (offset p : Nat) (y : Nat → Bool) (ht : Tail offset p y)
    (h : Nat → Bool) (n : Nat) : Tail offset (p+9*n) (history h n y) := by
  induction n with
  | zero => simpa [history] using ht
  | succ n ih =>
      have next := back_tail offset (p+9*n) (history h n y) (h n) ih
      simpa [history, Nat.mul_succ, Nat.add_assoc] using next

theorem history_tail_bound (offset p : Nat) (y : Nat → Bool) (N : Nat)
    (hy : ∀ k, N ≤ k → y k = profileRow p (k+offset))
    (h : Nat → Bool) (n : Nat) :
    ∀ k, N+310*n ≤ k → history h n y k = profileRow (p+9*n) (k+offset) := by
  induction n with
  | zero => simpa [history] using hy
  | succ n ih =>
      have next := back_tail_bound offset (p+9*n) (history h n y) (h n) (N+310*n) ih
      simpa [history, Nat.mul_succ, Nat.add_assoc] using next

theorem tails_agree (offset p : Nat) (x y : Nat → Bool)
    (hx : Tail offset p x) (hy : Tail offset p y) : EventuallyEq x y := by
  obtain ⟨A,hA⟩ := hx
  obtain ⟨B,hB⟩ := hy
  refine ⟨max A B, ?_⟩
  intro k hk
  exact (hA k (by omega)).trans (hB k (by omega)).symm

/-- No restriction on the number of inverse steps or the chosen heads. -/
theorem all_histories_agree (offset p : Nat) (y : Nat → Bool) (ht : Tail offset p y)
    (h g : Nat → Bool) (n : Nat) : EventuallyEq (history h n y) (history g n y) :=
  tails_agree offset (p+9*n) _ _ (history_tail offset p y ht h n) (history_tail offset p y ht g n)

def boundary (t : Nat) : Bool := Nat.testBit 1022 (t % 10)

private theorem boundary_certificate : ∀ t : Fin 10,
    profileRow t.val 154 = boundary t.val ∧
      profileRow t.val 155 = xor (boundary (t.val+1)) (boundary t.val || false) := by decide

theorem profile_boundary (t : Nat) : profileRow t 154 = boundary t := by
  have h := (boundary_certificate ⟨t % 10, by omega⟩).1
  simpa [profileRow, boundary] using h

theorem wall_step (t : Nat) :
    profileRow t 155 = xor (boundary (t+1)) (boundary t || false) := by
  have h := (boundary_certificate ⟨t % 10, by omega⟩).2
  simpa [profileRow, boundary, Nat.add_mod] using h

def periodicProfile (k t : Nat) : Bool :=
  if k = 0 then false else profileRow t (k+153)

theorem periodic_profile_step (k t : Nat) :
    periodicProfile (k+2) t = xor (periodicProfile (k+1) (t+1))
      (periodicProfile (k+1) t || periodicProfile k t) := by
  cases k with
  | zero =>
      change profileRow t 155 = xor (profileRow (t+1) 154) (profileRow t 154 || false)
      rw [profile_boundary, profile_boundary]
      exact wall_step t
  | succ k =>
      change profileRow t (k+156) = xor (profileRow (t+1) (k+155))
        (profileRow t (k+155) || profileRow t (k+154))
      exact profile_step t (k+154)

theorem recon_periodic_profile (k t : Nat) : recon boundary k t = periodicProfile k t := by
  have key : ∀ n, ∀ s, recon boundary n s = periodicProfile n s ∧
      recon boundary (n+1) s = periodicProfile (n+1) s := by
    intro n
    induction n with
    | zero =>
        intro s
        constructor
        · rfl
        · change boundary s = profileRow s 154
          exact (profile_boundary s).symm
    | succ n ih =>
        intro s
        constructor
        · exact (ih s).2
        · rw [recon, (ih (s+1)).2, (ih s).1, (ih s).2]
          exact (periodic_profile_step n s).symm
  exact (key k t).1

theorem lam_gap_five_tail : Tail 153 0 (lam boundary) := by
  refine ⟨1, ?_⟩
  intro k hk
  change recon boundary k 0 = profileRow 0 (k+153)
  rw [recon_periodic_profile]
  simp [periodicProfile, show k ≠ 0 by omega]

/-- Arbitrarily many inverse choices for this actual reconstructed
periodic boundary have the same far spatial tail. -/
theorem gap_five_histories_agree (h g : Nat → Bool) (n : Nat) :
    EventuallyEq (history h n (lam boundary)) (history g n (lam boundary)) :=
  all_histories_agree 153 0 _ lam_gap_five_tail h g n

def tracePrepend (b : Bool) (a : Nat → Bool) : Nat → Bool
  | 0 => b
  | t+1 => a t

theorem back_lam (b : Bool) (a : Nat → Bool) :
    back b (lam a) = lam (tracePrepend b a) := by
  have ht : ∀ t, zrow (back b (lam a)) t 1 = tracePrepend b a t := by
    intro t
    cases t with
    | zero => rfl
    | succ t =>
        calc
          zrow (back b (lam a)) (t+1) 1 =
              zrow (zrow (back b (lam a)) 1) t 1 := by
                simpa only [Nat.add_comm] using zrow_shift (back b (lam a)) 1 t 1
          _ = zrow (lam a) t 1 := zrow_congr (zrow_back b (lam a)) t 1
          _ = a t := (realization a).1 t
  have hh := (realization (tracePrepend b a)).2 (back b (lam a)) ht
  rw [zrow_back_zero] at hh
  exact hh

def gateHistory (h : Nat → Bool) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, y => y
  | n+1, y => back (!(h n)) (back true (gateHistory h n y))

def gateTracePast (h : Nat → Bool) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, a => a
  | n+1, a => tracePrepend (!(h n)) (tracePrepend true (gateTracePast h n a))

theorem gate_history_lam (h : Nat → Bool) (n : Nat) (a : Nat → Bool) :
    gateHistory h n (lam a) = lam (gateTracePast h n a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gateHistory, gateTracePast, ih, back_lam]

theorem gate_history_tail (offset p : Nat) (y : Nat → Bool) (ht : Tail offset p y)
    (h : Nat → Bool) (n : Nat) : Tail offset (p+18*n) (gateHistory h n y) := by
  induction n with
  | zero => simpa [gateHistory] using ht
  | succ n ih =>
      have first := back_tail offset (p+18*n) (gateHistory h n y) true ih
      have second := back_tail offset (p+18*n+9) _ (!(h n)) first
      simpa [gateHistory, Nat.mul_succ, Nat.add_assoc] using second

theorem gate_history_tail_bound (offset p : Nat) (y : Nat → Bool) (N : Nat)
    (hy : ∀ k, N ≤ k → y k = profileRow p (k+offset))
    (h : Nat → Bool) (n : Nat) :
    ∀ k, N+620*n ≤ k → gateHistory h n y k = profileRow (p+18*n) (k+offset) := by
  induction n with
  | zero => simpa [gateHistory] using hy
  | succ n ih =>
      have first := back_tail_bound offset (p+18*n) (gateHistory h n y) true (N+620*n) ih
      have second := back_tail_bound offset (p+18*n+9) _ (!(h n)) (N+620*n+310) first
      simpa [gateHistory, Nat.mul_succ, Nat.add_assoc] using second

def oddTrace (G : Nat → Bool) (t : Nat) : Bool :=
  if t % 2 = 0 then !(G (t/2)) else true

def gateCons (b : Bool) (G : Nat → Bool) : Nat → Bool
  | 0 => b
  | r+1 => G r

def gatePrepend (h : Nat → Bool) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, G => G
  | n+1, G => gateCons (h n) (gatePrepend h n G)

theorem odd_trace_cons (b : Bool) (G : Nat → Bool) :
    oddTrace (gateCons b G) = tracePrepend (!b) (tracePrepend true (oddTrace G)) := by
  funext t
  cases t with
  | zero => rfl
  | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
          have hp : (t+2)%2 = t%2 := by omega
          have hd : (t+2)/2 = t/2+1 := by omega
          simp [oddTrace, tracePrepend, gateCons, hp, hd]

theorem odd_trace_past (h : Nat → Bool) (n : Nat) (G : Nat → Bool) :
    oddTrace (gatePrepend h n G) = gateTracePast h n (oddTrace G) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gatePrepend, gateTracePast, odd_trace_cons, ih]

def gapFiveGate (r : Nat) : Bool := decide (r % 5 = 0)

theorem boundary_odd_trace : boundary = oddTrace gapFiveGate := by
  funext t
  have cert : ∀ r : Fin 10, boundary r.val = oddTrace gapFiveGate r.val := by decide
  have hp : (t%10)%2 = t%2 := by omega
  have hd : (t%10)/2 = (t/2)%5 := by omega
  have h := cert ⟨t%10, by omega⟩
  simpa [boundary, oddTrace, gapFiveGate, hp, hd] using h

/-- Any two same-length gate pasts of the all-gap-five future reconstruct
to the same far tail. All lengths and all past bits are quantified;
admissibility of those past bits is unnecessary for this subclass. -/
theorem arbitrary_gate_pasts_agree (h g : Nat → Bool) (n : Nat) :
    EventuallyEq (lam (oddTrace (gatePrepend h n gapFiveGate)))
      (lam (oddTrace (gatePrepend g n gapFiveGate))) := by
  rw [odd_trace_past, odd_trace_past, ← boundary_odd_trace,
    ← gate_history_lam, ← gate_history_lam]
  exact tails_agree 153 (0+18*n) _ _
    (gate_history_tail 153 0 _ lam_gap_five_tail h n)
    (gate_history_tail 153 0 _ lam_gap_five_tail g n)

/-- A uniform linear spatial bound, independent of the chosen past bits. -/
theorem arbitrary_gate_pasts_agree_from (h g : Nat → Bool) (n k : Nat)
    (hk : 1+620*n ≤ k) :
    lam (oddTrace (gatePrepend h n gapFiveGate)) k =
      lam (oddTrace (gatePrepend g n gapFiveGate)) k := by
  rw [odd_trace_past, odd_trace_past, ← boundary_odd_trace,
    ← gate_history_lam, ← gate_history_lam]
  have base : ∀ j, 1 ≤ j → lam boundary j = profileRow 0 (j+153) := by
    intro j hj
    change recon boundary j 0 = profileRow 0 (j+153)
    rw [recon_periodic_profile]
    simp [periodicProfile, show j ≠ 0 by omega]
  exact (gate_history_tail_bound 153 0 _ 1 base h n k hk).trans
    (gate_history_tail_bound 153 0 _ 1 base g n k hk).symm

end Ruliology.CellularAutomata.Rule30PeriodicGateTail
