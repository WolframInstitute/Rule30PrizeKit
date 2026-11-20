module
public import Ruliology.CellularAutomata.Rule30Certificates.ResetSwapCover

/-! At the fixed white wall, interchange the initial six- and ten-tick returns after 24 further legal returns of either size. The edit preserves finite width and the full row from tick 11 onward. A later edit after the seed width that rejoins the original orbit has infinite origin. -/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResetSwap
open Ruliology.CellularAutomata.Rule30ZeroBoundary

def height : Tree → Nat
  | .hit _ => 0
  | .fork l r => max (height l) (height r) + 1

theorem cover_height : height Certificate.cover = 24 := by decide +kernel

theorem covers_by (tree : Tree) (s : Pair) (h : valid tree s=true) (g : Nat → Bool) :
    ∃ k j, k≤height tree ∧ Good (path g s k).1 (path g s k).2 j=true := by
  induction tree generalizing s g with
  | hit j => exact ⟨0,j,Nat.le_refl 0,h⟩
  | fork l r il ir =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
    cases e : g 0 with
    | false =>
      obtain ⟨k,j,hn,hk⟩ := il _ hl (fun i => g (i+1))
      exact ⟨k+1,j,by simp only [height]; omega,by simpa only [path,e] using hk⟩
    | true =>
      obtain ⟨k,j,hn,hk⟩ := ir _ hr (fun i => g (i+1))
      exact ⟨k+1,j,by simp only [height]; omega,by simpa only [path,e] using hk⟩

/-- 65470 has bits 1 at ticks 1..5 and 7..15, and zero at 0,6,16.
Only the first 24 further gaps in g are inspected. -/
def First24 (u : Trace) (g : Nat → Bool) : Prop :=
  ∀ k, k≤24 → Fits u (path g (17,65470) k).1 (path g (17,65470) k).2

theorem toggle_twice (u : Trace) : toggle (toggle u) = u := by
  funext t
  simp only [toggle]
  cases u t <;> cases (1088 : Nat).testBit t <;> rfl

theorem switch_sync (u : Trace) (g : Nat → Bool) (h : First24 u g) :
    ∃ j≤174, ∀ d t, side (toggle u) (j+d) t=side u (j+d) t := by
  obtain ⟨m,j,hn,hj⟩ := covers_by _ _ Certificate.cover_ok g
  rw [cover_height] at hn
  exact ⟨j,(of_decide_eq_true hj).1,good_sync (h m hn) hj⟩

/-- Swap the first unlike ordered pair of gaps at the *current start*.
The two wall bits at ticks 6 and 10 change. The whole rows coincide
from tick 11, and initial cells at all kit depths ≥174 are unchanged. -/
theorem initial_swap (L : Trace) (g : Nat → Bool)
    (h : First24 (fun t => zrow L t 1) g ∨ First24 (toggle (fun t => zrow L t 1)) g) :
    ∃ M : Trace, (∀ t, zrow M t 1 = toggle (fun s => zrow L s 1) t) ∧
      (∀ k, 174≤k → M k=L k) ∧ (∀ t k, 11≤t → zrow M t k=zrow L t k) := by
  let u := fun t => zrow L t 1
  have ex : ∃ j≤174, ∀ d t, side (toggle u) (j+d) t=side u (j+d) t := by
    rcases h with ha | hb
    · exact switch_sync u g ha
    · obtain ⟨j,hj,h⟩ := switch_sync (toggle u) g hb
      rw [toggle_twice] at h
      exact ⟨j,hj,fun d t => (h d t).symm⟩
  obtain ⟨j,hj,he⟩ := ex
  refine ⟨seed (toggle u), fun t => realizes _ t 1, ?_, ?_⟩
  · intro k hk
    obtain ⟨d,rfl⟩ : ∃ d, k=j+d := ⟨k-j,by omega⟩
    exact (congrArg Prod.fst (he d 0)).trans
      ((congrArg Prod.fst (of_wall L _ 0)).trans (zrow_zero_of_pos L (by omega)))
  · intro t k ht
    exact (realizes _ t k).trans ((congrArg Prod.fst (tail_eq u k t ht)).trans
      (congrArg Prod.fst (of_wall L k t)))

/-- A finite competing seed reaching the same row must obey the
original seed's width bound. -/
theorem width_of_meeting {L M : Trace} {W T : Nat} (hl : ∀ k, W<k → L k=false)
    (hm : FinSupp M) (meet : ∀ k, zrow M T k = zrow L T k) : ∀ k, W<k → M k=false := by
  obtain ⟨B,hB⟩ := hm
  induction B with
  | zero => intro k hk; exact hB k (by omega)
  | succ B ih =>
    by_cases h : W<B+1
    · have off : M (B+1)=false := by
        cases e : M (B+1) with
        | false => rfl
        | true =>
          have a := (zrow_edge (by omega : 1≤B+1) e hB T).1
          rw [meet, zrow_fin hl T _ (by omega)] at a
          contradiction
      apply ih
      intro k hk
      by_cases hh : k=B+1
      · simpa only [hh] using off
      · exact hB k (by omega)
    · intro k hk; exact hB k (by omega)

theorem finite_initial_swap (L : Trace) (g : Nat → Bool) (W : Nat)
    (hl : ∀ k, W<k → L k=false)
    (h : First24 (fun t => zrow L t 1) g ∨ First24 (toggle (fun t => zrow L t 1)) g) :
    ∃ M : Trace, (∀ k, W<k → M k=false) ∧
      (∀ t, zrow M t 1 = toggle (fun s => zrow L s 1) t) ∧
      (∀ t k, 11≤t → zrow M t k=zrow L t k) := by
  obtain ⟨M,hm,hk,ht⟩ := initial_swap L g h
  have fin : FinSupp M := ⟨max W 174, fun k h => (hk k (by omega)).trans (hl k (by omega))⟩
  exact ⟨M,width_of_meeting hl fin (fun k => ht 11 k (by decide)),hm,ht⟩

theorem side_local {u v : Trace} {H : Nat} (h : ∀ t, t<H → u t=v t)
    (j t : Nat) (hj : j+t<H) : side u j t=side v j t := by
  induction j generalizing t with
  | zero => simp only [side_zero,h t (by omega)]
  | succ j ih => simp only [side_succ,ih t (by omega),ih (t+1) (by omega)]

/-- Once the first W wall bits of a width-W row are fixed, a different
trace that ever rejoins its complete row must come from infinite support. -/
theorem late_edit_infinite {L M : Trace} {W T : Nat} (hl : ∀ k, W<k → L k=false)
    (same : ∀ t, t<W → zrow M t 1=zrow L t 1)
    (diff : ∃ t, zrow M t 1≠zrow L t 1) (meet : ∀ k, zrow M T k=zrow L T k) :
    ¬ FinSupp M := by
  intro hm
  have bound := width_of_meeting hl hm meet
  have allpos : ∀ i, 1≤i → M i=L i := by
    intro i hi
    obtain ⟨j,rfl⟩ : ∃ j, i=j+1 := ⟨i-1,by omega⟩
    by_cases hj : j<W
    · have h := congrArg Prod.snd (side_local same j 0 (by omega))
      simpa only [of_wall,zrow_zero] using h
    · rw [bound _ (by omega),hl _ (by omega)]
  obtain ⟨t,hd⟩ := diff
  exact hd (zrow_congr allpos t 1)

/-- At the first infinite-to-finite step, the earlier row is eventually
black. Beyond the finite image the sideways update is just Boolean OR. -/
theorem black_tail_before_finite {M : Trace} {t : Nat}
    (hi : ¬FinSupp (zrow M t)) (hf : FinSupp (zrow M (t+1))) :
    ∃ J, ∀ k, J≤k → zrow M t k=true := by
  obtain ⟨B,hB⟩ := hf
  obtain ⟨j,hj,hblack⟩ : ∃ j, B+1<j ∧ zrow M t j=true := by
    apply Classical.byContradiction
    intro hn
    apply hi
    refine ⟨B+1, fun k hk => ?_⟩
    cases e : zrow M t k with
    | false => rfl
    | true => exact False.elim (hn ⟨k,hk,e⟩)
  have grow : ∀ d, zrow M t (j+d)=true := by
    intro d
    induction d with
    | zero => exact hblack
    | succ d ih =>
      have h := zrow_inv M t (j+d-1)
      rw [show j+d-1+2=j+(d+1) by omega,show j+d-1+1=j+d by omega,
        hB _ (by omega),ih] at h
      simpa using h
  exact ⟨j,fun k hk => by simpa only [Nat.add_sub_of_le hk] using grow (k-j)⟩

theorem finite_transition {M : Trace} {s : Nat}
    (hi : ¬FinSupp (zrow M 0)) (hf : FinSupp (zrow M s)) :
    ∃ t, t<s ∧ FinSupp (zrow M (t+1)) ∧ ∃ J, ∀ k, J≤k → zrow M t k=true := by
  induction s with
  | zero => exact False.elim (hi hf)
  | succ s ih =>
    by_cases h : FinSupp (zrow M s)
    · obtain ⟨t,ht,hf',hb⟩ := ih h
      exact ⟨t,by omega,hf',hb⟩
    · exact ⟨s,by omega,hf,black_tail_before_finite h hf⟩

/-- Prescribe an entire row at a later time while keeping the earlier
wall trace. The resulting starting row may have infinite support. -/
theorem lift_past (L : Trace) (s : Nat) (Y : Trace) : ∃ M : Trace,
    (∀ t, t<s → zrow M t 1=zrow L t 1) ∧ (∀ k, 1≤k → zrow M s k=Y k) := by
  induction s generalizing Y with
  | zero => exact ⟨Y,fun _ ht => by omega,fun _ hk => zrow_zero_of_pos _ hk⟩
  | succ s ih =>
    let b := zrow L s 1
    obtain ⟨M,h₁,h₂⟩ := ih (back b Y)
    refine ⟨M,?_,?_⟩
    · intro t ht
      by_cases hts : t=s
      · subst t; exact h₂ 1 (by decide)
      · exact h₁ t (by omega)
    · intro k hk
      exact (zrow_shift M s 1 k).trans ((zrow_congr h₂ 1 k).trans (zrow_back b Y k hk))

/-- An unlike pair at a reset after the seed width can be swapped at
that reset in finite support. Restoring the earlier wall history forces
a cofinite-black row strictly before that reset, with finite next row. -/
theorem late_swap_transition (L : Trace) (s W : Nat) (g : Nat → Bool)
    (hl : ∀ k, W<k → L k=false) (hs : W≤s)
    (h : First24 (fun t => zrow (zrow L s) t 1) g ∨
         First24 (toggle (fun t => zrow (zrow L s) t 1)) g) :
    ∃ M : Trace, (∀ t, t<s → zrow M t 1=zrow L t 1) ∧
      (∀ t, zrow M (s+t) 1=toggle (fun r => zrow L (s+r) 1) t) ∧
      FinSupp (zrow M s) ∧
      ∃ t, t<s ∧ FinSupp (zrow M (t+1)) ∧ ∃ J, ∀ k, J≤k → zrow M t k=true := by
  obtain ⟨Y,hy,hw,hmeet⟩ := finite_initial_swap (zrow L s) g (W+s) (zrow_fin hl s) h
  obtain ⟨M,hpre,hrow⟩ := lift_past L s Y
  have after (t k : Nat) : zrow M (s+t) k=zrow Y t k :=
    (zrow_shift M s t k).trans (zrow_congr hrow t k)
  have wall (t : Nat) : zrow M (s+t) 1=toggle (fun r => zrow L (s+r) 1) t := by
    rw [after,hw]; simp only [toggle,zrow_shift L s]
  have different : ∃ t, zrow M t 1≠zrow L t 1 := by
    refine ⟨s+6,?_⟩
    rw [wall]; change xor (zrow L (s+6) 1) true ≠ zrow L (s+6) 1
    cases zrow L (s+6) 1 <;> decide
  have inf := late_edit_infinite hl (fun t ht => hpre t (by omega)) different
      (fun k => (after 11 k).trans ((hmeet 11 k (by decide)).trans (zrow_shift L s 11 k).symm))
  have inf0 : ¬ FinSupp (zrow M 0) := by
    rintro ⟨B,hB⟩
    exact inf ⟨B,fun k hk => (zrow_zero_of_pos M (by omega : 1≤k)).symm.trans (hB k hk)⟩
  have fs : FinSupp (zrow M s) := ⟨W+s,fun k hk => (hrow k (by omega)).trans (hy k hk)⟩
  exact ⟨M,hpre,wall,fs,finite_transition inf0 fs⟩

/-! ## Exact `{6, 10}` support of `toggle`, uniqueness of `lift_past` on positive cells, and exact edge preservation -/

/-- **Exact `{6, 10}` Support of `toggle`, Positive-Half Uniqueness of `lift_past`, and Exact Edge Preservation (`toggle_support_and_lift_past_unique`).** -/
theorem toggle_support_and_lift_past_unique :
    (∀ u : Trace, toggle u 6 = !u 6 ∧ toggle u 10 = !u 10 ∧
      ∀ t : Nat, t ≠ 6 → t ≠ 10 → toggle u t = u t) ∧
    (∀ (M₁ M₂ : Trace) (s : Nat),
      (∀ t, t < s → zrow M₁ t 1 = zrow M₂ t 1) →
      (∀ k, 1 ≤ k → zrow M₁ s k = zrow M₂ s k) →
      ∀ k, 1 ≤ k → M₁ k = M₂ k) ∧
    (∀ (L M : Trace) (W T : Nat), 1 ≤ W → L W = true →
      (∀ k, W < k → L k = false) → FinSupp M →
      (∀ k, zrow M T k = zrow L T k) →
      M W = true ∧ ∀ k, W < k → M k = false) := by
  refine ⟨fun u => ⟨?_, ?_, ?_⟩, fun M₁ M₂ s hwall hrow k hk => ?_,
    fun L M W T hW hLW hLfin hMfin hmeet => ?_⟩
  · unfold toggle; cases u 6 <;> decide
  · unfold toggle; cases u 10 <;> decide
  · intro t ht6 ht10
    unfold toggle
    have hbit : (1088 : Nat).testBit t = false := by
      by_cases hlt : t < 11
      · have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨
            t = 7 ∨ t = 8 ∨ t = 9 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 1088 < 2 ^ 11)
          (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hbit, Bool.xor_false]
  · have hfull : ∀ j : Nat, zrow M₁ s j = zrow M₂ s j := by
      intro j
      cases j with
      | zero => rw [zrow_wall, zrow_wall]
      | succ j => exact hrow (j + 1) (by omega)
    have hdet := history_det hfull hwall 0 (Nat.zero_le s) k
    simpa only [zrow_zero_of_pos _ hk] using hdet
  · have hMbound := width_of_meeting hLfin hMfin hmeet
    refine ⟨?_, hMbound⟩
    cases hMW : M W with
    | true => rfl
    | false =>
      have hM_le : ∀ k, W - 1 < k → M k = false := by
        intro k hk
        by_cases heq : k = W
        · subst heq; exact hMW
        · exact hMbound k (by omega)
      have htop_false : zrow M T (W + T) = false :=
        zrow_fin hM_le T (W + T) (by omega)
      have htop_true : zrow L T (W + T) = true :=
        (zrow_edge hW hLW hLfin T).1
      rw [hmeet (W + T), htop_true] at htop_false
      cases htop_false

end Ruliology.CellularAutomata.Rule30ResetSwap
