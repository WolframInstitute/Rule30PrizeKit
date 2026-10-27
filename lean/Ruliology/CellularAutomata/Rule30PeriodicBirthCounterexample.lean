module

public import Ruliology.CellularAutomata.Rule30Prize

/-! A literal bi-infinite periodic Rule30 spacetime, not a single-seed history.
Its center has period2, but the coherent backward4-shift right mismatch
has a true birth in every six time steps. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodicBirthCounterexample
open Ruliology.CellularAutomata

/-- Physical columns advance backwards around the saved inverse-pair cycle. -/
def profiles : List Nat :=
  [42, 44, 52, 6, 51, 29, 20, 7, 53, 25, 1, 57, 12, 55, 21, 25, 41, 12,
   39, 58, 40, 14, 43, 50, 2, 51, 24, 47, 42, 50, 19, 24, 15, 53, 17, 28,
   23, 37, 4, 39, 48, 31, 21, 37, 38, 48, 30, 43, 34, 56, 46, 11, 8, 15,
   33, 62, 42, 11, 13, 33, 60, 23, 5, 49, 29, 22, 16, 30, 3, 61, 21, 22,
   26, 3, 57, 46, 10, 35, 58, 44, 32, 60, 6, 59]

def bit (t j : Nat) : Bool := (profiles.getD j 0).testBit t
def residue (t : Int) (n : Nat) : Nat := (t % (n : Int)).toNat
def orbit (t p : Int) : Bool := bit (residue t 6) (residue p 84)

theorem residue_lt (t : Int) (n : Nat) (hn : 0<n) : residue t n<n := by
  have h0 : 0≤t%(n:Int) := Int.emod_nonneg _ (by omega)
  have h1 : t%(n:Int)<n := Int.emod_lt_of_pos _ (by omega)
  unfold residue
  omega

theorem residue_succ6 (t : Int) : residue (t+1) 6=(residue t 6+1)%6 := by
  unfold residue
  have h0 := Int.emod_nonneg t (show (6:Int)≠0 by decide)
  have h1 := Int.emod_lt_of_pos t (show (0:Int)<6 by decide)
  have h2 := Int.emod_nonneg (t+1) (show (6:Int)≠0 by decide)
  have h3 := Int.emod_lt_of_pos (t+1) (show (0:Int)<6 by decide)
  omega

theorem residue_succ84 (p : Int) : residue (p+1) 84=(residue p 84+1)%84 := by
  unfold residue
  have h0 := Int.emod_nonneg p (show (84:Int)≠0 by decide)
  have h1 := Int.emod_lt_of_pos p (show (0:Int)<84 by decide)
  have h2 := Int.emod_nonneg (p+1) (show (84:Int)≠0 by decide)
  have h3 := Int.emod_lt_of_pos (p+1) (show (0:Int)<84 by decide)
  omega

theorem residue_pred84 (p : Int) : residue (p-1) 84=(residue p 84+83)%84 := by
  unfold residue
  have h0 := Int.emod_nonneg p (show (84:Int)≠0 by decide)
  have h1 := Int.emod_lt_of_pos p (show (0:Int)<84 by decide)
  have h2 := Int.emod_nonneg (p-1) (show (84:Int)≠0 by decide)
  have h3 := Int.emod_lt_of_pos (p-1) (show (0:Int)<84 by decide)
  omega

/-- Exactly504 local stencils, including both spatial and temporal wraps. -/
theorem stencils : ∀ t : Fin 6, ∀ j : Fin 84,
    bit ((t.val+1)%6) j.val = Rule30Jen.rule
      (bit t.val ((j.val+83)%84)) (bit t.val j.val) (bit t.val ((j.val+1)%84)) := by
  decide

/-- Literal Rule30 at every integer time and every integer physical position. -/
theorem physical_recurrence (t p : Int) :
    orbit (t+1) p = Rule30Jen.rule (orbit t (p-1)) (orbit t p) (orbit t (p+1)) := by
  unfold orbit
  rw [residue_succ6, residue_pred84, residue_succ84]
  exact stencils ⟨residue t 6,residue_lt t 6 (by decide)⟩
    ⟨residue p 84,residue_lt p 84 (by decide)⟩

theorem temporal_period6 (t p : Int) : orbit (t+6) p=orbit t p := by
  simp [orbit,residue]

theorem spatial_period84 (t p : Int) : orbit t (p+84)=orbit t p := by
  simp [orbit,residue]

theorem center_period2 (t : Int) : orbit (t+2) 0=orbit t 0 := by
  have h : ∀ r : Fin 6, bit ((r.val+2)%6) 0=bit r.val 0 := by decide
  have hr : residue (t+2) 6=(residue t 6+2)%6 := by
    unfold residue
    have h0 := Int.emod_nonneg t (show (6:Int)≠0 by decide)
    have h1 := Int.emod_lt_of_pos t (show (0:Int)<6 by decide)
    have h2 := Int.emod_nonneg (t+2) (show (6:Int)≠0 by decide)
    have h3 := Int.emod_lt_of_pos (t+2) (show (0:Int)<6 by decide)
    omega
  change bit (residue (t+2) 6) 0=bit (residue t 6) 0
  rw [hr]
  exact h ⟨residue t 6,residue_lt t 6 (by decide)⟩

theorem center_not_period1 : orbit 1 0 ≠ orbit 0 0 := by decide
theorem right_not_period4 : orbit (1+4) 1 ≠ orbit 1 1 := by decide

theorem right_short_period_failure : ∀ p : Fin 6, 0<p.val →
    ∃ t : Fin 6, bit ((t.val+p.val)%6) 1 ≠ bit t.val 1 := by decide

theorem temporal_least6 (p : Nat) (hp : 0<p)
    (h : ∀ t j : Int, orbit (t+p) j=orbit t j) : 6≤p := by
  apply Classical.byContradiction
  intro hn
  have hp6 : p<6 := by omega
  obtain ⟨t,ht⟩ := right_short_period_failure ⟨p,hp6⟩ hp
  apply ht
  have hx := h t.val 1
  have hr1 : residue ((t.val:Int)+p) 6=(t.val+p)%6 := by
    unfold residue
    omega
  have hr2 : residue (t.val:Int) 6=t.val := by
    unfold residue
    omega
  change bit (residue ((t.val:Int)+p) 6) 1=bit (residue (t.val:Int) 6) 1 at hx
  rw [hr1,hr2] at hx
  exact hx

theorem orbit_nat_phase (k r : Nat) (p : Int) :
    orbit (6*k+r : Nat) p=orbit r p := by
  simp [orbit,residue,Int.add_emod]

/-- Backward Nat subtraction; later birth claims have t>=4, so no truncation occurs. -/
def backwardMismatch (t : Nat) : Bool := xor (orbit t 1) (orbit (t-4 : Nat) 1)

theorem true_birth_every_six (k : Nat) :
    backwardMismatch (6*k+4)=false ∧ backwardMismatch (6*k+4+1)=true := by
  have h0 : 6*k+4-4=6*k+0 := by omega
  have h1 : 6*k+4+1-4=6*k+1 := by omega
  unfold backwardMismatch
  rw [h0,h1,show 6*k+4+1=6*k+5 by omega]
  rw [orbit_nat_phase k 4,orbit_nat_phase k 0,orbit_nat_phase k 5,orbit_nat_phase k 1]
  decide

theorem births_arbitrarily_late (B : Nat) :
    ∃ u, B≤u ∧ 4≤u ∧ backwardMismatch u=false ∧ backwardMismatch (u+1)=true := by
  exact ⟨6*B+4,by omega,by omega,(true_birth_every_six B).1,(true_birth_every_six B).2⟩

/-- Constructively, there are N distinct true births with both readings below6N. -/
theorem linear_birth_witnesses (N : Nat) :
    ∃ u : Fin N → Nat,
      (∀ i, 4≤u i ∧ u i+1<6*N) ∧
      (∀ i j, u i=u j → i=j) ∧
      (∀ i, backwardMismatch (u i)=false ∧ backwardMismatch (u i+1)=true) := by
  refine ⟨fun i => 6*i.val+4, ?_, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    dsimp
    constructor <;> omega
  · intro i j h
    apply Fin.ext
    dsimp at h
    omega
  · intro i
    exact true_birth_every_six i.val

/-- The initial row has black cells arbitrarily far right: this is not a finite seed. -/
theorem initial_support_unbounded (N : Nat) :
    ∃ p : Int, (N:Int)<p ∧ orbit 0 p=true := by
  refine ⟨84*(N+1)+4, by omega, ?_⟩
  have hm : residue (84*(N+1)+4) 84=4 := by
    simp [residue,Int.add_emod]
  unfold orbit
  rw [hm]
  decide

end Ruliology.CellularAutomata.Rule30PeriodicBirthCounterexample
