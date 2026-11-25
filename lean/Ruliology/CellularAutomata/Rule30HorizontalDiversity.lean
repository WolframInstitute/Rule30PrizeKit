module

public import Ruliology.CellularAutomata.Rule30HorizontalDiversityBounds
public import Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity

/-! Entry point for the five-cell and first-visit bounds, together with the earlier four-cell estimates. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30HorizontalDiversity
open Ruliology.CellularAutomata Rule30Jen Rule30MaskedJen Rule30Realization Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity

/-- Under a period P after T, a single list of at most T+P floor(6(5/4)^w)
horizontal words covers the singleton row on [-w,0] at every age. -/
theorem horizontal_cover {T P : Nat} (hp : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0) (w : Nat) :
    ∃ L : List (List Bool), L.length ≤ T + P*(6*5^w/4^w) ∧ ∀ t, row w t ∈ L := by
  apply cover_of_channel (fun c => words c 0) (budget := fun n => 6*5^n/4^n)
    _ observations_mem hp per w
  intro c
  exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0<4))).mpr (masked_word_count c)

/-- Exact horizontal vocabulary is bounded by the phase cover including all transient ages. -/
theorem horizontal_count {T P : Nat} (hp : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0) (w : Nat) :
    H w ≤ T + P*(6*5^w/4^w) := by
  obtain ⟨L,cap,covers⟩ := horizontal_cover hp per w
  exact Nat.le_trans (count_le_cover covers) cap

/-- An unbounded ratio H(w)/(5/4)^w would settle the official first prize problem. -/
theorem problem1_of_horizontal_growth
    (growth : ∀ A : Nat, ∃ w, A*5^w < H w*4^w) : Rule30Prize.Problem1 := by
  rintro ⟨T,P,hp,per⟩
  obtain ⟨w,large⟩ := growth (T+6*P)
  have h := horizontal_count hp per w
  have bound : H w*4^w ≤ (T+6*P)*5^w := by
    calc
      _ ≤ (T+P*(6*5^w/4^w))*4^w := Nat.mul_le_mul_right _ h
      _ = T*4^w + P*((6*5^w/4^w)*4^w) := by rw [Nat.add_mul,Nat.mul_assoc]
      _ ≤ T*5^w + P*(6*5^w) := Nat.add_le_add
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 4≤5) w))
        (Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
      _ = _ := by rw [Nat.add_mul]; ac_rfl
  omega

/-- Growth can be witnessed entirely by finite lists of ages with pairwise distinct rows. -/
theorem growth_iff_finite_samples :
    (∀ A : Nat, ∃ w, A*5^w < H w*4^w) ↔
    ∀ A : Nat, ∃ (w : Nat) (ages : List Nat),
      (ages.map (row w)).Nodup ∧ A*5^w < ages.length*4^w := growth_iff_samples 5 4

/-- A finite horizontal sampling criterion for the first prize problem. -/
theorem problem1_of_finite_samples
    (samples : ∀ A : Nat, ∃ (w : Nat) (ages : List Nat), (ages.map (row w)).Nodup ∧
      A*5^w < ages.length*4^w) : Rule30Prize.Problem1 :=
  problem1_of_horizontal_growth (growth_iff_finite_samples.mpr samples)

/-- All Rule 30 histories sharing one temporal center word lie in a single bounded list of masked histories. -/
theorem uniform_mask_bound (c : List Bool) :
    ∃ candidates : List (List Bool), candidates.length * 4^c.length ≤ 6 * 5^c.length ∧
      ∀ (x : Int → Bool) (t : Nat), segment (fun k => evol x k 0) t c.length = c →
        segment (fun k => evol x k 0 || evol x k 1) t c.length ∈ candidates :=
  genuine_channel_bound c


end Ruliology.CellularAutomata.Rule30HorizontalDiversity
