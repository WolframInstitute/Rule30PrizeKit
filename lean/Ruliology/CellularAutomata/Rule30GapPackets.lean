module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Four-observation sums for a clipped white gap

A gap born at tick `v` on `[a, b]` has white-pair sites on
`[a + t - v, b - (t - v) - 1]` at tick `t`. The observation indexed by `n`
samples the site `t + 1 - n` from tick `(n + d) / 2` through tick `n - 1`.
`deposit` sums the signed gates of this intersection and its center-pair correction.

On any consecutive groups of four observations, the sum of absolute group charges
is at most 14 per gap, uniformly over the cut, horizon and alignment. Three
interval-restricted waves of period four and one exceptional ray give the bound.
This estimates one contribution to the center-frequency problem.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30GapPackets

def eps (i : Int) : Int := if i % 2 = 0 then 1 else -1

private theorem phase_succ (i : Int) : eps (i+1) = -eps i := by
  unfold eps
  repeat' split <;> omega

private theorem phase_bound (i : Int) : -1 ≤ eps i ∧ eps i ≤ 1 := by
  unfold eps
  split <;> decide

/-- Alternating sum over `len` consecutive ticks, starting with phase `eps i`. -/
def alternating (i : Int) : Nat → Int
  | 0 => 0
  | k+1 => alternating i k + eps (i+k)

private theorem alternating_endpoints (i : Int) (k : Nat) :
    2 * alternating i k = eps i - eps (i+k) := by
  induction k with
  | zero => simp [alternating]
  | succ k ih =>
    have h : i + (↑(k+1) : Int) = (i+k) + 1 := by omega
    rw [alternating, h, phase_succ]
    omega

def lower (d v n : Int) := max v ((n+d)/2)
def upper (v b n : Int) := min n ((n+v+b)/2)

abbrev hit (d v a b n t : Int) : Prop :=
  v ≤ t ∧ (n+d)/2 ≤ t ∧ t < n ∧ a+(t-v) ≤ t+1-n ∧ t+2-n ≤ b-(t-v)

theorem ray_interval (d v a b n t : Int) :
    hit d v a b n t ↔ n ≤ v+1-a ∧ lower d v n ≤ t ∧ t < upper v b n := by
  dsimp [hit, lower, upper]
  omega


open Rule30Jen

def spin (t : Nat) (p : Int) : Int := if cell t p then 1 else -1

/-- The left neighbor's spin when the two sites of a gate are white. -/
def gate (t : Nat) (i : Int) : Int :=
  if cell t i || cell t (i+1) then 0 else spin t (i-1)

theorem gate_step (t : Nat) (i : Int) :
    spin (t+1) i = -spin t (i-1) + 2 * gate t i := by
  have step (x y z : Bool) :
      (if rule x y z then (1 : Int) else -1) =
        -(if x then 1 else -1) + 2 * (if y || z then 0 else (if x then 1 else -1)) := by
    cases x <;> cases y <;> cases z <;> decide
  exact step _ _ _

/-- On an eroded gap slice, the signed gate is positive exactly at the slice’s left edge. -/
theorem gate_on_gap (t : Nat) (d v a b n : Int)
    (black : cell t (a+(t-v)-1) = true)
    (white : ∀ x, a+(t-v) ≤ x → x ≤ b-(t-v) → cell t x = false)
    (h : hit d v a b n t) :
    gate t (t+1-n) = if n = v+1-a then 1 else -1 := by
  obtain ⟨_, _, _, hleft, hright⟩ := h
  have h₁ := white (t+1-n) (by omega) (by omega)
  have h₂ := white (t+1-n+1) (by omega) (by omega)
  simp only [gate, h₁, h₂, Bool.false_or, Bool.false_eq_true, ite_false, spin]
  split
  next hblack =>
    have left : n = v+1-a := by
      apply Classical.byContradiction
      intro hne
      have := white (t+1-n-1) (by omega) (by omega)
      simp_all
    simp [left]
  next hblack =>
    have off : n ≠ v+1-a := by
      intro heq
      have hx : (t : Int)+1-n-1 = a+(t-v)-1 := by omega
      exact hblack (hx ▸ black)
    simp [off]

def firstRay (d v b : Int) := max (d+1) (max (v+1) (v-b))
def pastRay (T v a : Int) := min (T+1) (v+2-a)

abbrev active (d T v a b n : Int) : Prop :=
  d ≤ v+b ∧ firstRay d v b ≤ n ∧ n < pastRay T v a

def deposit (d T v a b n : Int) : Int :=
  if d ≤ n ∧ n ≤ T ∧ n ≤ v+1-a then
    (if n = v+1-a then 1 else -1) *
      (2 * alternating (lower d v n+1-n) (upper v b n - lower d v n).toNat) +
      (if hit d v a b n (n-1) then 1 else 0)
  else 0

private theorem endpoints (l u n : Int) (h : l ≤ u) :
    2 * alternating (l+1-n) (u-l).toNat = eps (l+1-n) - eps (u+1-n) := by
  rw [alternating_endpoints, show l+1-n + ↑(u-l).toNat = u+1-n by omega]

private theorem deposit_endpoints (d T v a b n : Int) :
    deposit d T v a b n =
      if active d T v a b n then
        (if n = v+1-a then 1 else -1) * (eps (lower d v n+1-n) - eps (upper v b n+1-n)) +
          (if n ≤ v+b then 1 else 0)
      else 0 := by
  unfold deposit
  by_cases ha : active d T v a b n
  · have hb := ha
    dsimp [active, firstRay, pastRay] at hb
    have hr : d ≤ n ∧ n ≤ T ∧ n ≤ v+1-a := by omega
    have hu : lower d v n ≤ upper v b n := by dsimp [lower, upper]; omega
    have hj : hit d v a b n (n-1) ↔ n ≤ v+b := by dsimp [hit]; omega
    simp only [ite_eq_left ha, ite_eq_left hr, endpoints _ _ _ hu, hj]
  · rw [ite_eq_right ha]
    split
    next hr =>
      dsimp [active, firstRay, pastRay] at ha
      have hz : (upper v b n - lower d v n).toNat = 0 := by dsimp [upper, lower]; omega
      have hj : ¬hit d v a b n (n-1) := by dsimp [hit]; omega
      simp [hz, hj, alternating]
    next => rfl

def halfWave (c n : Int) := eps ((n+c)/2+1-n)
def altWave (v n : Int) := eps (v+1-n)
def band (lo hi : Int) (f : Int → Int) (n : Int) := if lo ≤ n ∧ n < hi then f n else 0
def spike (p value n : Int) := if n = p then value else 0

def flank (d T v a b : Int) : Int :=
  let p := v+1-a
  if active d T v a b p then 2 * (eps (lower d v p+1-p) - eps (upper v b p+1-p)) else 0


private theorem flank_bound (d T v a b : Int) :
    max (flank d T v a b) (-(flank d T v a b)) ≤ 4 := by
  unfold flank
  dsimp only
  split
  next =>
    have h := phase_bound (lower d v (v+1-a)+1-(v+1-a))
    have j := phase_bound (upper v b (v+1-a)+1-(v+1-a))
    omega
  next => decide

theorem three_waves (d T v a b n : Int) :
    let lo := firstRay d v b
    let hi := pastRay T v a
    let w := v+b
    let k := 2*v-d
    deposit d T v a b n = if d ≤ w then
      band (max lo (w+1)) hi (halfWave w) n -
      band lo (min hi k) (altWave v) n -
      band (max lo k) hi (halfWave d) n + spike (v+1-a) (flank d T v a b) n
    else 0 := by
  dsimp only
  rw [deposit_endpoints]
  by_cases hw : d ≤ v+b
  · rw [ite_eq_left hw]
    by_cases ha : active d T v a b n
    · rw [ite_eq_left ha]
      obtain ⟨_, hlo, hhi⟩ := ha
      have hu : eps (upper v b n+1-n) + (if n ≤ v+b then 1 else 0) =
          band (max (firstRay d v b) (v+b+1)) (pastRay T v a) (halfWave (v+b)) n := by
        by_cases h : n ≤ v+b
        · rw [ite_eq_left h, upper, Int.min_eq_left (by omega),
              show n+1-n = 1 by omega, show eps 1 = -1 by decide]
          rw [band, ite_eq_right (by omega)]
          decide
        · rw [ite_eq_right h, upper, Int.min_eq_right (by omega), band, ite_eq_left (by omega)]
          simp only [halfWave, Int.add_assoc n v b, Int.add_zero]
      have hl : eps (lower d v n+1-n) =
          band (firstRay d v b) (min (pastRay T v a) (2*v-d)) (altWave v) n +
          band (max (firstRay d v b) (2*v-d)) (pastRay T v a) (halfWave d) n := by
        by_cases h : n < 2*v-d
        · rw [lower, Int.max_eq_left (by omega), band, ite_eq_left (by omega), band, ite_eq_right (by omega)]
          simp [altWave]
        · rw [lower, Int.max_eq_right (by omega), band, ite_eq_right (by omega), band, ite_eq_left (by omega)]
          simp [halfWave]
      by_cases hp : n = v+1-a
      · subst n
        have ha' : active d T v a b (v+1-a) := ⟨hw, hlo, hhi⟩
        simp only [spike, flank, ite_eq_left ha', ite_true, Int.one_mul]
        omega
      · simp only [ite_eq_right hp, spike, Int.neg_one_mul]
        omega
    · rw [ite_eq_right ha]
      have h := ha
      dsimp [active] at h
      have h₁ : ¬(max (firstRay d v b) (v+b+1) ≤ n ∧ n < pastRay T v a) := by omega
      have h₂ : ¬(firstRay d v b ≤ n ∧ n < min (pastRay T v a) (2*v-d)) := by omega
      have h₃ : ¬(max (firstRay d v b) (2*v-d) ≤ n ∧ n < pastRay T v a) := by omega
      simp only [band, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]
      by_cases hp : n = v+1-a
      · subst n
        simp [spike, flank, ha]
      · simp [spike, hp]
  · have ha : ¬active d T v a b n := fun h => hw h.1
    simp [ha, hw]

def packet (f : Int → Int) (n : Int) : Int := f n + f (n+1) + f (n+2) + f (n+3)

def sumN (k : Nat) (f : Nat → Int) : Int :=
  match k with
  | 0 => 0
  | j+1 => sumN j f + f j

private theorem sum_le {f g : Nat → Int} (h : ∀ i, f i ≤ g i) (k : Nat) :
    sumN k f ≤ sumN k g := by
  induction k with
  | zero => exact Int.le_refl _
  | succ k ih => simp only [sumN]; have := h k; omega

private theorem sum_add (k : Nat) (f g : Nat → Int) :
    sumN k (fun j => f j + g j) = sumN k f + sumN k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sumN, ih]; omega

private theorem sum_mul (k : Nat) (c : Int) (f : Nat → Int) :
    sumN k (fun j => c * f j) = c * sumN k f := by
  induction k with
  | zero => simp [sumN]
  | succ k ih => simp only [sumN, ih, Int.mul_add]

private theorem sum_zero (k : Nat) : sumN k (fun _ => 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sumN, ih]

abbrev magnitude (x : Int) := max x (-x)

/-- Sum of absolute charges, with four consecutive observations per group. -/
def mass (s : Int) (k : Nat) (f : Int → Int) :=
  sumN k (fun j => magnitude (packet f (s+4*j)))

private def slot (n x : Int) : Int := if n ≤ x ∧ x < n+4 then 1 else 0

private theorem slot_sum (s x : Int) (k : Nat) :
    sumN k (fun j => slot (s+4*j) x) = if s ≤ x ∧ x < s+4*k then 1 else 0 := by
  induction k with
  | zero => simp [sumN]
  | succ k ih =>
    rw [sumN, ih]
    unfold slot
    repeat' split <;> omega

private def Wave (f : Int → Int) (C : Int) : Prop := ∀ n,
  magnitude (f n) ≤ C ∧ magnitude (f n + f (n+1)) ≤ C ∧
  magnitude (f n + f (n+1) + f (n+2)) ≤ C ∧ packet f n = 0

private theorem alt_wave (v : Int) : Wave (altWave v) 1 := by
  have step (n : Int) : altWave v (n+1) = -altWave v n := by
    unfold altWave eps
    repeat' split <;> omega
  intro n
  have h := phase_bound (v+1-n)
  change -1 ≤ altWave v n ∧ altWave v n ≤ 1 at h
  rw [packet, show n+2 = (n+1)+1 by omega, show n+3 = (n+1+1)+1 by omega,
    step (n+1+1), step (n+1), step n]
  dsimp only [magnitude]
  omega

private theorem half_wave (c : Int) : Wave (halfWave c) 2 := by
  have step (n : Int) : halfWave c (n+2) = -halfWave c n := by
    unfold halfWave eps
    repeat' split <;> omega
  intro n
  have h := phase_bound ((n+c)/2+1-n)
  have j := phase_bound ((n+1+c)/2+1-(n+1))
  change -1 ≤ halfWave c n ∧ halfWave c n ≤ 1 at h
  change -1 ≤ halfWave c (n+1) ∧ halfWave c (n+1) ≤ 1 at j
  rw [packet, show n+3 = (n+1)+2 by omega, step (n+1), step n]
  dsimp only [magnitude]
  omega

private theorem prefix_packet {f : Int → Int} {C : Int} (hf : Wave f C) (hc : 0 ≤ C) (n x : Int) :
    magnitude (packet (fun j => if j < x then f j else 0) n) ≤ C * slot n x := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hf n
  dsimp only [packet, magnitude] at *
  unfold slot
  (repeat' split) <;> simp_all <;> omega

private theorem band_mass {f : Int → Int} {C : Int} (hf : Wave f C) (hc : 0 ≤ C)
    (s lo hi : Int) (k : Nat) : mass s k (band lo hi f) ≤ 2*C := by
  by_cases order : lo ≤ hi
  · have diff (n : Int) : band lo hi f n =
        (if n < hi then f n else 0) - (if n < lo then f n else 0) := by
      unfold band
      repeat' split <;> omega
    have per (n : Int) : magnitude (packet (band lo hi f) n) ≤ C * slot n hi + C * slot n lo := by
      have h : packet (band lo hi f) n = packet (fun j => if j < hi then f j else 0) n -
          packet (fun j => if j < lo then f j else 0) n := by simp only [packet, diff]; omega
      rw [h]
      have h₁ := prefix_packet hf hc n hi
      have h₂ := prefix_packet hf hc n lo
      dsimp only [magnitude] at *
      omega
    unfold mass
    apply Int.le_trans (sum_le (fun j => per (s+4*j)) k)
    rw [sum_add, sum_mul, sum_mul, slot_sum, slot_sum]
    (repeat' split) <;> simp_all <;> omega
  · have h (n : Int) : band lo hi f n = 0 := ite_eq_right (by omega)
    simpa [mass, packet, h, magnitude, sum_zero] using (show (0 : Int) ≤ 2*C by omega)

private theorem spike_mass (s p z : Int) (k : Nat) : mass s k (spike p z) ≤ magnitude z := by
  have eq (n : Int) : magnitude (packet (spike p z) n) = magnitude z * slot n p := by
    unfold packet spike slot magnitude
    (repeat' split) <;> simp_all <;> omega
  simp only [mass, eq, sum_mul, slot_sum]
  split <;> simp [magnitude] <;> omega

/-- Every clipped birth contributes at most 14 to the sum of absolute group charges. -/
theorem birth_packet_budget (d T v a b start : Int) (k : Nat) :
    mass start k (deposit d T v a b) ≤ 14 := by
  by_cases hw : d ≤ v+b
  · let f := band (max (firstRay d v b) (v+b+1)) (pastRay T v a) (halfWave (v+b))
    let g := band (firstRay d v b) (min (pastRay T v a) (2*v-d)) (altWave v)
    let h := band (max (firstRay d v b) (2*v-d)) (pastRay T v a) (halfWave d)
    let z := spike (v+1-a) (flank d T v a b)
    have form (n : Int) : deposit d T v a b n = f n - g n - h n + z n := by
      simp only [three_waves, ite_eq_left hw, f, g, h, z]
    have per (n : Int) : magnitude (packet (deposit d T v a b) n) ≤
        magnitude (packet f n) + magnitude (packet g n) + magnitude (packet h n) + magnitude (packet z n) := by
      have eq : packet (deposit d T v a b) n = packet f n - packet g n - packet h n + packet z n := by
        simp only [packet, form]
        omega
      rw [eq]
      dsimp only [magnitude]
      omega
    have hm : mass start k (deposit d T v a b) ≤ mass start k f + mass start k g +
        mass start k h + mass start k z := by
      unfold mass
      apply Int.le_trans (sum_le (fun j => per (start+4*j)) k)
      simp only [sum_add, Int.le_refl]
    have hf : mass start k f ≤ 4 := band_mass (half_wave _) (by decide) _ _ _ _
    have hg : mass start k g ≤ 2 := band_mass (alt_wave _) (by decide) _ _ _ _
    have hh : mass start k h ≤ 4 := band_mass (half_wave _) (by decide) _ _ _ _
    have hz : mass start k z ≤ 4 :=
      Int.le_trans (spike_mass start (v+1-a) (flank d T v a b) k) (flank_bound d T v a b)
    omega
  · have h (n : Int) : deposit d T v a b n = 0 := by simp only [three_waves, ite_eq_right hw]
    simp [mass, packet, magnitude, h, sum_zero]

/-- Combined charge of a finite list of births. -/
def familyDeposit {ι : Type} (v a b : ι → Int) (d T : Int) : List ι → Int → Int
  | [], _ => 0
  | i :: rest, n => deposit d T (v i) (a i) (b i) n + familyDeposit v a b d T rest n

/-- Summing the charges before taking packet magnitudes costs at most 14 per omitted birth. -/
theorem family_packet_budget {ι : Type} (births : List ι) (v a b : ι → Int)
    (d T start : Int) (k : Nat) :
    mass start k (familyDeposit v a b d T births) ≤ 14 * (births.length : Int) := by
  induction births with
  | nil => simp [familyDeposit, mass, packet, magnitude, sum_zero]
  | cons i rest ih =>
    let f := deposit d T (v i) (a i) (b i)
    let g := familyDeposit v a b d T rest
    have per (n : Int) : magnitude (packet (familyDeposit v a b d T (i::rest)) n) ≤
        magnitude (packet f n) + magnitude (packet g n) := by
      have h : packet (familyDeposit v a b d T (i::rest)) n = packet f n + packet g n := by
        simp only [packet, familyDeposit, f, g]
        omega
      rw [h]
      dsimp only [magnitude]
      omega
    have add : mass start k (familyDeposit v a b d T (i::rest)) ≤ mass start k f + mass start k g := by
      unfold mass
      apply Int.le_trans (sum_le (fun j => per (start+4*j)) k)
      simp only [sum_add, Int.le_refl]
    have bound : mass start k f ≤ 14 := birth_packet_budget ..
    change mass start k g ≤ _ at ih
    simp only [List.length_cons]
    omega

end Ruliology.CellularAutomata.Rule30GapPackets
