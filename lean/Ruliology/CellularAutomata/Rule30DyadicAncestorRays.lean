module

public import Ruliology.CellularAutomata.Rule30RightPeriods
public import Ruliology.CellularAutomata.Rule30TwoSidedInverse

/-!
# Recovering the singleton's past along arithmetic progressions

An eight-cell Hughes reset fixes the pair at its western end in *every*
one-step parent. The right-edge diagonal periods copy any finite arrangement
of such resets arbitrarily far east. This leaves room to prepend a fresh
reset at the genuine left edge one tick earlier. Iterating gives any finite
inverse depth and keeps the checks on successive time slices compatible.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DyadicAncestorRays

open Rule30Jen Rule30Realization Rule30TwoSidedInverse Rule30AgeEightInverse
  Rule30RightPeriods Rule30Diagonals

private def Marker (t d : Nat) : Prop :=
  EdgeGood8 (band (cell t) ((t : Int) - d) 8) = true

private theorem marker_edge (t : Nat) (ht : 8 ≤ t) : Marker t (2*t) := by
  have h := good8_of_age (x := seed) (lo := 0) (by rfl)
    (fun p hp => by simp [seed]; omega) t ht
  have he : evol seed t = cell t := funext (evol_seed t)
  rw [he] at h
  unfold Marker
  rw [show (t : Int) - ↑(2*t) = 0 - t by omega]
  exact h

private theorem marker_restart {t d J : Nat} (hd : 7 ≤ d) (hJ : d ≤ J)
    (hm : Marker t d) (u : Nat) : Marker (2^J*u + t) d := by
  unfold Marker at *
  rw [band_congr (c := cell (2^J*u + t)) (d := cell t)
    (f := ((2^J*u + t : Nat) : Int) - d) (g := (t : Int) - d) 8]
  · exact hm
  · intro j hj
    have h := restart (per_mono_le (show d-j ≤ J by omega) (per_R_periodic J)) u t
    unfold R at h
    simpa only [show (((2^J*u + t : Nat) : Int) - d + j) =
        ↑(2^J*u + t : Nat) - ↑(d-j) by omega,
      show (t : Int) - d + j = t - (↑(d-j) : Int) by omega] using h

/-- Diagonal depths in chronological order. Each later window lies east of all
earlier windows where reconstruction will need the image. -/
private def Chain : Nat → List Nat → Prop
  | _, [] => True
  | a, d :: ds => 7 ≤ d ∧ Marker (a+1) d ∧ (∀ e ∈ ds, e+7 ≤ d) ∧ Chain (a+1) ds

private theorem chain_restart {a J : Nat} {ds : List Nat} (hc : Chain a ds)
    (bound : ∀ d ∈ ds, d ≤ J) (u : Nat) : Chain (2^J*u + a) ds := by
  induction ds generalizing a with
  | nil => trivial
  | cons d ds ih =>
    obtain ⟨hd, hm, hsep, ht⟩ := hc
    exact ⟨hd, marker_restart hd (bound d (by simp)) hm u, hsep,
      ih ht (fun e he => bound e (by simp [he]))⟩

private theorem le_sum {d : Nat} {ds : List Nat} (h : d ∈ ds) : d ≤ ds.sum := by
  induction ds with
  | nil => simp at h
  | cons e es ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

/-- Build a chain while prescribing its final time modulo any positive modulus. -/
private theorem chains (n m r : Nat) (hm : 0 < m) :
    ∃ a ds v, ds.length = n ∧ Chain a ds ∧ a+n = r+m*v := by
  induction n with
  | zero => exact ⟨r, [], 0, rfl, trivial, by simp⟩
  | succ n ih =>
    obtain ⟨a, ds, v, hl, hc, ha⟩ := ih
    let u := m*(ds.sum+10)
    let b := 2^ds.sum*u+a
    have hpow : 0 < 2^ds.sum := Nat.two_pow_pos _
    have hu : ds.sum+10 ≤ u := Nat.le_mul_of_pos_left _ hm
    have hbig : u ≤ 2^ds.sum*u := Nat.le_mul_of_pos_left _ hpow
    have hb : ds.sum+10 ≤ b := by dsimp [b]; omega
    have hrec : Chain b ds := chain_restart hc (fun _ he => le_sum he) u
    have hs : b-1+1 = b := by omega
    refine ⟨b-1, 2*b :: ds, v + 2^ds.sum*(ds.sum+10), by simp [hl], ?_, ?_⟩
    · change 7 ≤ 2*b ∧ Marker (b-1+1) (2*b) ∧ _ ∧ Chain (b-1+1) ds
      rw [hs]
      exact ⟨by omega, marker_edge b (by omega), fun e he => by have := le_sum he; omega, hrec⟩
    · have hmul : 2^ds.sum*u = m*(2^ds.sum*(ds.sum+10)) := by
        dsimp [u]; ac_rfl
      rw [Nat.mul_add]
      dsimp [b] at *
      omega

private theorem pull (t : Nat) (z : Int → Bool) (f p : Int) (hp : p < f)
    (hm : EdgeGood8 (band (cell (t+1)) f 8) = true)
    (hz : ∀ q, p+1 ≤ q → q ≤ f+7 → stepLine z q = cell (t+1) q) :
    z p = cell t p := by
  have hb : band (stepLine z) f 8 = band (cell (t+1)) f 8 :=
    band_congr _ (fun j hj => hz _ (by omega) (by omega))
  have reset (x : Int → Bool) (hx : EdgeGood8 (band (stepLine x) f 8) = true) :
      x (f-1) = false ∧ x f = false := by
    have h := prun_spec (stepLine x) x (fun _ => rfl) f 8 8 (by decide)
    rw [prun_reset8 _ hx] at h
    have hh : (false, false) = (x (f-1), x f) := by
      simpa only [show f+(8:Nat)-1-(8:Nat) = f-1 by omega,
        show f+(8:Nat)-(8:Nat) = f by omega] using h
    exact ⟨(congrArg Prod.fst hh).symm, (congrArg Prod.snd hh).symm⟩
  have h1 := reset z (by rwa [hb])
  have h2 := reset (cell t) hm
  have pair : ∀ k : Nat, p ≤ f-k-1 →
      z (f-k-1) = cell t (f-k-1) ∧ z (f-k) = cell t (f-k) := by
    intro k
    induction k with
    | zero => intro _; simpa using And.intro (h1.1.trans h2.1.symm) (h1.2.trans h2.2.symm)
    | succ k ih =>
      intro hk
      obtain ⟨hl, hr⟩ := ih (by omega)
      have h := left_of (stepLine z) z (fun _ => rfl) (f-k-1)
      rw [hz _ (by omega) (by omega), hl, show f-(k:Int)-1+1 = f-k by omega, hr] at h
      have g := cell_left t (f-k-1)
      rw [show f-(k:Int)-1+1 = f-k by omega] at g
      simpa only [show f-((k+1:Nat):Int) = f-k-1 by omega] using
        And.intro (h.trans g.symm) hl
  simpa only [show f-((f-1-p).toNat:Int)-1 = p by omega] using
    (pair (f-1-p).toNat (by omega)).1

private theorem evol_first (z : Int → Bool) (n : Nat) : evol (stepLine z) n = evol z (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg stepLine ih

private theorem decode {ds : List Nat} {a : Nat} (hc : Chain a ds) (j : Int)
    (hj : j ≤ a) (hwest : ∀ d ∈ ds, j ≤ (a:Int)-d) (z : Int → Bool)
    (hz : ∀ q : Int, j+ds.length ≤ q → q ≤ (a+ds.length : Nat) →
      evol z ds.length q = cell (a+ds.length) q) : z j = cell a j := by
  induction ds generalizing a j z with
  | nil => exact hz j (by simp) (by simpa using hj)
  | cons d ds ih =>
    obtain ⟨hd, hm, hsep, ht⟩ := hc
    let f : Int := (a+1:Nat)- (d:Int)
    have := hwest d (by simp)
    apply pull a z f j (by dsimp [f]; omega) hm
    intro p hp hp'
    apply ih ht p (by dsimp [f] at hp'; omega)
      (fun e he => by have := hsep e he; dsimp [f] at hp'; omega) (stepLine z)
    intro q hq hq'
    rw [evol_first]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hz q (by simp; omega) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq')

/-- For every inverse depth and requested congruence class there is a base time
in that class (at the image) and a dyadic progression of reconstruction times.
The one later interval from p+n through the true right edge determines the
earlier bit p. The competing initial row and its unobserved cells are arbitrary. -/
theorem syndetic_ancestor_rays (n m r : Nat) (hm : 0 < m) :
    ∃ a D v : Nat, a+n = r+m*v ∧ ∀ u : Nat, ∀ z : Int → Bool,
      let t := 2^D*u+a
      ∀ p : Int, p ≤ (t:Int)-D →
      (∀ q : Int, p+n ≤ q → q ≤ (t+n : Nat) → evol z n q = cell (t+n) q) →
      z p = cell t p := by
  obtain ⟨a, ds, v, hl, hc, ha⟩ := chains n m r hm
  refine ⟨a, ds.sum, v, ha, ?_⟩
  intro u z
  dsimp only
  intro p hp hz
  subst n
  exact decode (chain_restart hc (fun _ he => le_sum he) u) _ (by omega)
    (fun d hd => by have := le_sum hd; omega) z hz

end Ruliology.CellularAutomata.Rule30DyadicAncestorRays
