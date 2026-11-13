module

public import Ruliology.CellularAutomata.Rule30ControlledResponse

/-!
# A local obstruction to masking the first period doubling

This is a statement about five temporal columns satisfying the triangular
update, not about the vertical center column. If the second column reverses
color after an even half-period while the next two repeat, the OR of the
first two columns cannot stay black forever. A full-clock hypothesis on the
first column is explicit. No finite-tail period-detection theorem or prize
problem is proved here.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ClockMask

open Rule30ControlledResponse

private theorem mask_zero (a ah b c d : Bool)
    (h0 : (a || b)=true) (hh : (ah || !b)=true)
    (h1 : (xor a (b || c) || xor b (c || d))=true)
    (hh1 : (xor ah (!b || c) || xor (!b) (c || d))=true)
    (hk : xor a ah=false) : c=false ∧ d=false := by
  cases a <;> cases ah <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem difference_step (a ah b c : Bool) :
    xor (xor a (b || c)) (xor ah (!b || c)) = xor (xor a ah) (!c) := by
  cases a <;> cases ah <;> cases b <;> cases c <;> rfl

private theorem flip_sum (k b c : Bool) :
    xor (xor k (!c)) (xor b c) = !xor k b := by
  cases k <;> cases b <;> cases c <;> rfl

private theorem xor_not_right (a b : Bool) : xor a (!b)=!xor a b := by
  cases a <;> cases b <;> rfl

/-- An even half-clock cannot hide this particular clock onset behind constant OR. -/
theorem no_constant_OR_at_onset (a b c d e : Nat → Bool) (n : Nat)
    (ha : ∀ t, a (t+1)=xor (a t) (b t || c t))
    (hb : ∀ t, b (t+1)=xor (b t) (c t || d t))
    (hc : ∀ t, c (t+1)=xor (c t) (d t || e t))
    (haper : ∀ t, a (t+2*(2*n))=a t)
    (hanti : ∀ t, b (t+2*n)=!b t)
    (hcper : ∀ t, c (t+2*n)=c t)
    (hdper : ∀ t, d (t+2*n)=d t) :
    ¬ ∀ t, (a t || b t)=true := by
  intro hor
  let K (t : Nat) := xor (a t) (a (t+2*n))
  have Kstep (t : Nat) : K (t+1)=xor (K t) (!c t) := by
    dsimp [K]
    rw [show t+1+2*n=(t+2*n)+1 by omega,ha,ha,hanti,hcper]
    exact difference_step _ _ _ _
  have Kzero (t : Nat) (hk : K t=false) : c t=false ∧ d t=false := by
    apply mask_zero (a t) (a (t+2*n)) (b t) (c t) (d t) (hor t) ?_ ?_ ?_ hk
    · simpa only [hanti] using hor (t+2*n)
    · simpa only [ha,hb] using hor (t+1)
    · have h := hor ((t+2*n)+1)
      simpa only [ha,hb,hanti,hcper,hdper] using h
  have cd (t : Nat) : (c t || d t)=c t := by
    cases hct : c t with
    | true => rfl
    | false =>
        have hdt : d t=false := by
          cases hkt : K t with
          | false => exact (Kzero t hkt).2
          | true =>
              have hnext : K (t+1)=false := by rw [Kstep,hkt,hct]; rfl
              have hcn := (Kzero (t+1) hnext).1
              rw [hc,hct] at hcn
              cases hdt : d t <;> cases het : e t <;> simp_all
        rw [hdt]
        rfl
  let f (t : Nat) := xor (K t) (b t)
  have fstep (t : Nat) : f (t+1)=!f t := by
    dsimp [f]
    rw [Kstep,hb,cd]
    exact flip_sum _ _ _
  have f_even : ∀ m t, f (t+2*m)=f t := by
    intro m
    induction m with
    | zero => intro t; rfl
    | succ m ih =>
        intro t
        rw [show t+2*(m+1)=(t+2*m+1)+1 by omega,fstep,fstep,ih]
        exact Bool.not_not _
  have Kper (t : Nat) : K (t+2*n)=K t := by
    dsimp [K]
    rw [show t+2*n+2*n=t+2*(2*n) by omega,haper]
    exact Bool.xor_comm _ _
  have f_anti (t : Nat) : f (t+2*n)=!f t := by
    dsimp [f]
    rw [Kper,hanti]
    exact xor_not_right _ _
  have he := f_even n 0
  rw [f_anti] at he
  cases hf : f 0 <;> simp [hf] at he

theorem iterate_column_step (x : State) (k t : Nat) :
    iterate x (t+1) k=xor (iterate x t k)
      (iterate x t (k+1) || iterate x t (k+2)) := rfl

/-- The OR cannot even have the shorter half-clock: that would make it constant. -/
theorem OR_not_half_period (a b c d e : Nat → Bool) (n : Nat)
    (ha : ∀ t, a (t+1)=xor (a t) (b t || c t))
    (hb : ∀ t, b (t+1)=xor (b t) (c t || d t))
    (hc : ∀ t, c (t+1)=xor (c t) (d t || e t))
    (haper : ∀ t, a (t+2*(2*n))=a t)
    (hanti : ∀ t, b (t+2*n)=!b t)
    (hcper : ∀ t, c (t+2*n)=c t)
    (hdper : ∀ t, d (t+2*n)=d t) :
    ¬ ∀ t, (a (t+2*n) || b (t+2*n))=(a t || b t) := by
  intro hs
  apply no_constant_OR_at_onset a b c d e n ha hb hc haper hanti hcper hdper
  intro t
  cases hbt : b t with
  | true => simp
  | false =>
      have ht := hs t
      rw [hanti,hbt] at ht
      simpa using ht.symm

/-- One more column to the left must retain the larger clock as well. -/
theorem predecessor_not_half_period (z a b c d e : Nat → Bool) (n : Nat)
    (hz : ∀ t, z (t+1)=xor (z t) (a t || b t))
    (ha : ∀ t, a (t+1)=xor (a t) (b t || c t))
    (hb : ∀ t, b (t+1)=xor (b t) (c t || d t))
    (hc : ∀ t, c (t+1)=xor (c t) (d t || e t))
    (haper : ∀ t, a (t+2*(2*n))=a t)
    (hanti : ∀ t, b (t+2*n)=!b t)
    (hcper : ∀ t, c (t+2*n)=c t)
    (hdper : ∀ t, d (t+2*n)=d t) :
    ¬ ∀ t, z (t+2*n)=z t := by
  intro hzper
  apply OR_not_half_period a b c d e n ha hb hc haper hanti hcper hdper
  intro t
  have h1 := hz (t+2*n)
  rw [show t+2*n+1=(t+1)+2*n by omega,hzper,hzper,hz] at h1
  cases hz0 : z t <;> cases ho0 : (a t || b t) <;>
    cases hoH : (a (t+2*n) || b (t+2*n)) <;> simp_all

/-- Application to the actual triangular orbit, with every clock premise explicit. -/
theorem orbit_onset_not_constant_OR (x : State) (k n : Nat)
    (ha : ∀ t, iterate x (t+2*(2*n)) k=iterate x t k)
    (hb : ∀ t, iterate x (t+2*n) (k+1)=!iterate x t (k+1))
    (hc : ∀ t, iterate x (t+2*n) (k+2)=iterate x t (k+2))
    (hd : ∀ t, iterate x (t+2*n) (k+3)=iterate x t (k+3)) :
    ¬ ∀ t, (iterate x t k || iterate x t (k+1))=true := by
  apply no_constant_OR_at_onset (fun t => iterate x t k)
    (fun t => iterate x t (k+1)) (fun t => iterate x t (k+2))
    (fun t => iterate x t (k+3)) (fun t => iterate x t (k+4)) n
    (iterate_column_step x k) ?_ ?_ ha hb hc hd
  · intro t
    simpa only [Nat.add_assoc] using iterate_column_step x (k+1) t
  · intro t
    simpa only [Nat.add_assoc] using iterate_column_step x (k+2) t

/-! ## Triangular-orbit specializations of `OR_not_half_period` and `predecessor_not_half_period` -/

/-- **Triangular-Orbit Specializations of `OR_not_half_period` and `predecessor_not_half_period` (`orbit_onset_OR_and_predecessor_not_half_period`).** -/
theorem orbit_onset_OR_and_predecessor_not_half_period (x : State) (k n : Nat)
    (ha : ∀ t, iterate x (t + 2 * (2 * n)) (k + 1) = iterate x t (k + 1))
    (hb : ∀ t, iterate x (t + 2 * n) (k + 2) = !iterate x t (k + 2))
    (hc : ∀ t, iterate x (t + 2 * n) (k + 3) = iterate x t (k + 3))
    (hd : ∀ t, iterate x (t + 2 * n) (k + 4) = iterate x t (k + 4)) :
    (¬ ∀ t, (iterate x (t + 2 * n) (k + 1) || iterate x (t + 2 * n) (k + 2)) =
            (iterate x t (k + 1) || iterate x t (k + 2))) ∧
    (¬ ∀ t, iterate x (t + 2 * n) k = iterate x t k) := by
  have hstep1 : ∀ t, iterate x (t + 1) (k + 1) =
      xor (iterate x t (k + 1)) (iterate x t (k + 2) || iterate x t (k + 3)) :=
    fun t => by simpa only [Nat.add_assoc] using iterate_column_step x (k + 1) t
  have hstep2 : ∀ t, iterate x (t + 1) (k + 2) =
      xor (iterate x t (k + 2)) (iterate x t (k + 3) || iterate x t (k + 4)) :=
    fun t => by simpa only [Nat.add_assoc] using iterate_column_step x (k + 2) t
  have hstep3 : ∀ t, iterate x (t + 1) (k + 3) =
      xor (iterate x t (k + 3)) (iterate x t (k + 4) || iterate x t (k + 5)) :=
    fun t => by simpa only [Nat.add_assoc] using iterate_column_step x (k + 3) t
  exact ⟨OR_not_half_period (fun t => iterate x t (k + 1)) (fun t => iterate x t (k + 2))
           (fun t => iterate x t (k + 3)) (fun t => iterate x t (k + 4))
           (fun t => iterate x t (k + 5)) n hstep1 hstep2 hstep3 ha hb hc hd,
         predecessor_not_half_period (fun t => iterate x t k) (fun t => iterate x t (k + 1))
           (fun t => iterate x t (k + 2)) (fun t => iterate x t (k + 3))
           (fun t => iterate x t (k + 4)) (fun t => iterate x t (k + 5)) n
           (iterate_column_step x k) hstep1 hstep2 hstep3 ha hb hc hd⟩

end Ruliology.CellularAutomata.Rule30ClockMask
