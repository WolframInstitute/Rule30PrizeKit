module
public import Ruliology.CellularAutomata.Rule30ResetSwap
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe

/-!
# Finite wall observations and finite ancestry

Every length-H record at the fixed white wall is compatible with two finite
rows differing in one outer cell when k is positive. One realizes all 2^k
earlier wall words at a common time-k endpoint, from finite starts. The
other has no finite one-step predecessor. In fact a single outer completion
for each H,k realizes exactly k generations for every H-cell spatial
prefix, even at k=0. The terminal width is H+7k+3. This construction
quantifies over finite observation windows and allows width to grow.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30WallRecordAncestry
open Rule30ZeroBoundary Rule30ZeroBoundaryStripe
abbrev Row := Nat → Bool

/-- Keep the first B physical cells and finish with a white cell and a
black cell. This isolated outer cell rules out every finite parent. -/
def cut (B : Nat) (x : Row) (j : Nat) : Bool :=
  if j≤B then x j else decide (j=B+2)

theorem cut_edge (x : Row) (B : Nat) :
    cut B x (B+2)=true ∧ (∀ j, B+2<j → cut B x j=false) := by
  exact ⟨by simp [cut],fun j h => by simp [cut,show ¬j≤B by omega,show j≠B+2 by omega]⟩

theorem cut_cone (x : Row) (B t j : Nat) (h : j+t≤B) :
    zrow (cut B x) t j=zrow x t j :=
  zrow_light_cone t j (fun i _ hi => by simp [cut,show i≤B by omega])

/-- The penultimate physical cell stays black as the outer edge advances. -/
theorem cut_outer_pair (x : Row) (B k : Nat) (hk : 0<k) :
    zrow (cut B x) k (B+2+k)=true ∧ zrow (cut B x) k (B+1+k)=true ∧
    ∀ j, B+2+k<j → zrow (cut B x) k j=false := by
  have h := cut_edge x B
  have edge := zrow_edge (by omega : 1≤B+2) h.1 h.2
  refine ⟨(edge k).1,?_,(edge k).2⟩
  cases k with
  | zero => omega
  | succ t =>
    rw [show B+1+(t+1)=(B+1+t)+1 by omega,zrow_succ]
    rw [(edge t).2 _ (by omega),show B+1+t+1=B+2+t by omega,(edge t).1]
    rfl

/-- Every binary k-word is realized on the wall by a finite k-step
predecessor of the same row Y. Different words give different starts. -/
def FullPast (Y : Row) (k : Nat) : Prop :=
  ∀ b : Row, ∃ X : Row, FinSupp X ∧ (∀ t, t<k → zrow X t 1=b t) ∧
    ∀ j, zrow X k j=Y j

def fill (H : Nat) (x tail : Row) (j : Nat) :=
  if j=0 then false else if j≤H then x j else tail j

/-- A single computable outer completion works simultaneously for ALL
H-bit spatial prefixes and all k-bit past wall words. -/
def outer (H k : Nat) : Row := zrow (cut (H+1+6*k) stripe) k

theorem cut_pasts (x : Row) (H k : Nat) (b : Row) :
    ∃ r, (∀ t, t<k → zrow (cut (H+1+6*k) r) t 1=b t) ∧
      ∀ j, zrow (cut (H+1+6*k) r) k j=fill H x (outer H k) j := by
  let J := H+1+4*k
  let B := J+2*k
  have beq : H+1+6*k=B := by dsimp [B,J]; omega
  have hJ : 1≤J := by dsimp [J]; omega
  obtain ⟨X,hb,hx⟩ := Rule30ResetSwap.lift_past (lam b) k (fill H x stripe)
  have far : AgreesFrom X J := agrees_pre_run X (H+1) (by omega) k (fun j hj => by
    rw [hx _ (by omega)]; simp [fill,show j≠0 by omega,show ¬j≤H by omega])
  refine ⟨X,?_,?_⟩ <;> rw [beq]
  · intro t ht
    exact (cut_cone X B t 1 (by dsimp [B,J]; omega)).trans ((hb t ht).trans ((realization b).1 t))
  · intro j
    by_cases zero : j=0
    · subst j; exact zrow_wall _ _
    by_cases small : j≤J+k
    · rw [cut_cone _ _ _ _ (by dsimp [B]; omega),hx _ (by omega)]
      have oe : outer H k j=stripe j := by
        unfold outer
        rw [beq,cut_cone _ _ _ _ (by dsimp [B]; omega),zrow_stripe]
      simp only [fill,oe]
    · have large : ¬j≤H := by dsimp [J] at small; omega
      simp only [fill,ite_eq_right zero,ite_eq_right large,outer,beq]
      exact zrow_local hJ (fun i hi => by simp only [cut,far i hi]) k j (by omega)

theorem universal_outer_completion (x : Row) (H k : Nat) :
    FullPast (fill H x (outer H k)) k := by
  intro b
  obtain ⟨r,hb,hm⟩ := cut_pasts x H k b
  exact ⟨_,⟨_,(cut_edge r _).2⟩,hb,hm⟩

theorem full_past_with_record (u : Row) (H k : Nat) (hk : 0<k) :
    ∃ Y : Row, FullPast Y k ∧ (∀ t, t<H → zrow Y t 1=u t) ∧
      Y (H+7*k+3)=true ∧ Y (H+7*k+2)=true ∧ ∀ j, H+7*k+3<j → Y j=false := by
  let Y := fill H (lam u) (outer H k)
  refine ⟨Y,universal_outer_completion _ _ _,?_,?_⟩
  · intro t ht
    exact (zrow_light_cone t 1 (L:=Y) (L':=lam u)
      (fun i hi hB => by simp [Y,fill,show i≠0 by omega,show i≤H by omega])).trans ((realization u).1 t)
  · have e := cut_outer_pair stripe (H+1+6*k) k hk
    have far (j : Nat) (hj : H<j) : Y j=outer H k j := by
      simp [Y,fill,show j≠0 by omega,show ¬j≤H by omega]
    refine ⟨?_,?_,?_⟩
    · rw [far _ (by omega)]
      simpa only [outer,show H+1+6*k+2+k=H+7*k+3 by omega] using e.1
    · rw [far _ (by omega)]
      simpa only [outer,show H+1+6*k+1+k=H+7*k+2 by omega] using e.2.1
    · intro j hj; exact (far _ (by omega)).trans (e.2.2 _ (by omega))

/-- Reading the outputs 0,1,0 forces a black predecessor bit, regardless
of the two incoming bits. Further zero outputs keep the tail black. -/
theorem isolated_edge_parent {X Y : Row} {p : Nat} (hp : 1≤p)
    (h0 : Y p=false) (h1 : Y (p+1)=true) (hz : ∀ j, p+1<j → Y j=false)
    (parent : ∀ j, 1≤j → zrow X 1 j=Y j) :
    ∀ d, X (p+3+d)=true := by
  have eqn (i : Nat) (hi : 1≤i) :
      X (i+1)=xor (Y i) (X i || zrow X 0 (i-1)) := by
    have e := zrow_inv X 0 (i-1)
    rw [show i-1+2=i+1 by omega,show i-1+1=i by omega,
        parent i hi,zrow_zero_of_pos X hi,zrow_zero] at e
    exact e
  have e0 := eqn p hp
  have e1 := eqn (p+1) (by omega)
  have e2 := eqn (p+2) (by omega)
  rw [h0] at e0
  rw [h1,show p+1-1=p by omega,zrow_zero_of_pos X hp,e0] at e1
  rw [hz _ (by omega),show p+2-1=p+1 by omega,zrow_zero,e1,e0] at e2
  have start : X (p+3)=true := by
    revert e2
    cases X p <;> cases zrow X 0 (p-1) <;> exact id
  intro d
  induction d with
  | zero => exact start
  | succ d ih =>
    have e := eqn (p+3+d) (by omega)
    rw [hz _ (by omega),ih] at e
    simpa only [Nat.add_assoc,Bool.true_or,Bool.false_xor] using e

/-- The same outer completion prohibits even one additional step of
finite ancestry, including when k=0. -/
theorem exact_height (x : Row) (H k : Nat) :
    FullPast (fill H x (outer H k)) k ∧
    ¬∃ U : Row, FinSupp U ∧ ∀ j, zrow U (k+1) j=fill H x (outer H k) j := by
  refine ⟨universal_outer_completion _ _ _,?_⟩
  rintro ⟨U,⟨W,hW⟩,hu⟩
  let b := fun t => zrow (zrow U 1) t 1
  let B := H+1+6*k
  obtain ⟨r,hb,hm⟩ := cut_pasts x H k b
  have meet (j : Nat) : zrow (zrow U 1) k j=zrow (cut B r) k j := by
    rw [← zrow_shift,Nat.add_comm 1 k,hu]; exact (hm j).symm
  have walls (t : Nat) (ht : t<k) : zrow (zrow U 1) t 1=zrow (cut B r) t 1 := (hb t ht).symm
  have par (j : Nat) (hj : 1≤j) : zrow U 1 j=cut B r j := by
    have h := history_det meet walls 0 (Nat.zero_le _) j
    simpa only [zrow_zero_of_pos _ hj] using h
  have allblack := isolated_edge_parent (p:=B+1) (by omega)
    (by simp [cut,show ¬B+1≤B by omega] : cut B r (B+1)=false)
    (cut_edge r B).1 (cut_edge r B).2 par W
  rw [hW _ (by omega)] at allblack
  contradiction

/-- In particular, **every** prescribed finite temporal record admits a
finite realization with a complete finite predecessor tree of exactly
the requested height. -/
theorem exact_height_with_record (u : Row) (H k : Nat) :
    ∃ Y : Row, FinSupp Y ∧ (∀ t, t<H → zrow Y t 1=u t) ∧ FullPast Y k ∧
      ¬∃ U : Row, FinSupp U ∧ ∀ j, zrow U (k+1) j=Y j := by
  let Y := fill H (lam u) (outer H k)
  refine ⟨Y,?_,?_,exact_height _ _ _⟩
  · refine ⟨H+7*k+3,fun j hj => ?_⟩
    simp only [Y,fill,ite_eq_right (by omega : j≠0),ite_eq_right (by omega : ¬j≤H),outer]
    exact zrow_fin (cut_edge stripe _).2 k j (by omega)
  · intro t ht
    exact (zrow_light_cone t 1 (L:=Y) (L':=lam u)
      (fun i hi hB => by simp [Y,fill,show i≠0 by omega,show i≤H by omega])).trans ((realization u).1 t)

theorem opposite_ancestry (u : Row) (H k : Nat) (hk : 0<k) :
    ∃ Y Z : Row, FullPast Y k ∧ FinSupp Y ∧ FinSupp Z ∧
      (∀ t, t<H → zrow Y t 1=u t ∧ zrow Z t 1=u t) ∧
      (∀ j, j≠H+7*k+2 → Y j=Z j) ∧ Y (H+7*k+2)≠Z (H+7*k+2) ∧
      Y (H+7*k+3)=true ∧ Z (H+7*k+3)=true ∧
      (∀ j, H+7*k+3<j → Y j=false ∧ Z j=false) ∧
      (∀ X : Row, (∀ j, 1≤j → zrow X 1 j=Z j) → ∀ d, X (H+7*k+5+d)=true) := by
  obtain ⟨Y,hpast,ht,h1,h0,hz⟩ := full_past_with_record u H k hk
  let p := H+7*k+2
  let Z : Row := fun j => if j=p then false else Y j
  have far (j : Nat) (hj : p+1<j) : Z j=false := by
    simpa [Z,show j≠p by omega] using hz j hj
  refine ⟨Y,Z,hpast,⟨p+1,hz⟩,⟨p+1,far⟩,?_,?_,?_,h1,?_,?_,?_⟩
  · intro t h
    refine ⟨ht t h,(zrow_light_cone t 1 ?_).trans (ht t h)⟩
    intro i _ hi
    simp [Z,show i≠p by dsimp [p]; omega]
  · intro j hj; simp [Z,hj,p]
  · simp [Z,p,h0]
  · simpa [Z,p] using h1
  · exact fun j hj => ⟨hz j hj,far j hj⟩
  · intro X h
    exact isolated_edge_parent (p:=p) (by dsimp [p]; omega) (by simp [Z])
      (by simpa [Z,p] using h1) far h

theorem white_row (t j : Nat) : zrow (fun _ => false) t j=false := by
  induction t generalizing j with
  | zero => cases j <;> rfl
  | succ t ih =>
    cases j with
    | zero => exact zrow_wall _ _
    | succ i => rw [zrow_succ,ih,ih,ih]; rfl

theorem white_prefix (X : Row) (n : Nat) (hw : ∀ t, t<n → zrow X t 1=false) :
    ∀ i, 1≤i → i≤n → X i=false := by
  intro i h1 h2
  obtain ⟨j,rfl⟩ : ∃ j, i=j+1 := ⟨i-1,by omega⟩
  have h := congrArg Prod.snd (Rule30ResetSwap.side_local (u:=fun t => zrow X t 1)
    (v:=fun t => zrow (fun _ => false) t 1)
    (fun t ht => (hw t ht).trans (white_row t 1).symm) j 0 (by omega))
  simpa only [Rule30ResetSwap.of_wall,zrow_zero] using h

theorem last_of_nonempty {X : Row} {i : Nat} (hi : 1≤i) (black : X i=true)
    (h : FinSupp X) : ∃ m, i≤m ∧ X m=true ∧ ∀ j, m<j → X j=false := by
  obtain ⟨B,hB⟩ := h
  induction B with
  | zero =>
    have eq := hB i (by omega)
    rw [black] at eq; contradiction
  | succ B ih =>
    by_cases e : X (B+1)=true
    · refine ⟨B+1,?_,e,hB⟩
      apply Nat.le_of_not_gt; intro h
      have eq := hB i h
      rw [black] at eq; contradiction
    · apply ih
      intro j hj
      by_cases he : j=B+1
      · rw [he]; cases hh : X (B+1) <;> simp_all
      · exact hB _ (by omega)

/-- A nonzero terminal row with H white wall observations and a finite
k-step all-white past needs physical width at least H+2k+1. -/
theorem white_record_width_lower {X Y : Row} {H k W : Nat}
    (hfin : FinSupp X) (hp : ∀ t, t<k → zrow X t 1=false)
    (meet : ∀ j, zrow X k j=Y j) (hf : ∀ t, t<H → zrow Y t 1=false)
    (nonempty : ∃ j, 1≤j ∧ Y j=true) (bound : ∀ j, W<j → Y j=false) :
    H+2*k+1≤W := by
  have hw : ∀ t, t<k+H → zrow X t 1=false := by
    intro t ht
    by_cases h : t<k
    · exact hp t h
    · obtain ⟨a,rfl⟩ : ∃ a, t=k+a := ⟨t-k,by omega⟩
      exact (zrow_shift X k a 1).trans ((zrow_congr (fun j _ => meet j) a 1).trans (hf a (by omega)))
  obtain ⟨i,hi,bi⟩ : ∃ i, 1≤i ∧ X i=true := by
    apply Classical.byContradiction
    intro hn
    have empty : ∀ j, 1≤j → X j=false := by
      intro j hj; cases e : X j with
      | false => rfl
      | true => exact False.elim (hn ⟨j,hj,e⟩)
    obtain ⟨j,_,bj⟩ := nonempty
    have eq := (meet j).symm.trans ((zrow_congr (L':=fun _ => false) empty k j).trans (white_row k j))
    rw [bj] at eq; contradiction
  obtain ⟨m,hm,bm,tail⟩ := last_of_nonempty hi bi hfin
  have pos : k+H<m := by
    apply Nat.lt_of_not_ge; intro hm'
    have eq := white_prefix X (k+H) hw m (by omega) hm'
    rw [bm] at eq; contradiction
  have edge := (zrow_edge (by omega : 1≤m) bm tail k).1
  rw [meet] at edge
  by_cases h : W<m+k
  · rw [bound _ h] at edge; contradiction
  · omega

/-- A single fixed nonempty finite origin is different: once its age
reaches its initial width, its actual row cannot also have a finite
history of that entire length with an all-white wall trace. -/
theorem fixed_origin_white_past_cutoff {L X : Row} {W k : Nat}
    (hl : ∀ j, W<j → L j=false) (nonempty : ∃ i, 1≤i ∧ L i=true)
    (hx : FinSupp X) (white : ∀ t, t<k → zrow X t 1=false)
    (meet : ∀ j, zrow X k j=zrow L k j) : k<W := by
  obtain ⟨i,hi,bi⟩ := nonempty
  obtain ⟨m,hm,bm,hz⟩ := last_of_nonempty hi bi ⟨W,hl⟩
  have edge := (zrow_edge (by omega : 1≤m) bm hz k).1
  have bound := white_record_width_lower (H:=0) hx white meet (fun _ ht => by omega)
    ⟨m+k,by omega,edge⟩ (zrow_fin hl k)
  omega

/-! ## Universal sharpness of `white_record_width_lower` (`W = H + 2*k + 1`) and `fixed_origin_white_past_cutoff` (`k = W - 1`) -/

private def singleCell (p : Nat) : Row := fun j => decide (j = p)

private theorem zrow_singleCell_white_before (p t : Nat) (ht : t + 1 < p) :
    zrow (singleCell p) t 1 = false := by
  rw [zrow_light_cone t 1 (L := singleCell p) (L' := fun _ => false)
    (fun i _ hi => by simp [singleCell, show i ≠ p by omega])]
  exact white_row t 1

/-- **Universal Sharpness of `white_record_width_lower` and `fixed_origin_white_past_cutoff` (`white_record_width_sharp_and_cutoff_tight`):**
for every `(H, k)`, a single black start cell at depth `H + k + 1` achieves exact terminal width
`W = H + 2*k + 1` with a `k`-step all-white past and `H`-step all-white future; and for every `W ≥ 1`,
a single black cell at depth `W` achieves `k = W - 1` all-white steps, matching `k < W` to within `1`. -/
theorem white_record_width_sharp_and_cutoff_tight :
    (∀ H k : Nat, ∃ X Y : Row, FinSupp X ∧
      (∀ t, t < k → zrow X t 1 = false) ∧
      (∀ j, zrow X k j = Y j) ∧
      (∀ t, t < H → zrow Y t 1 = false) ∧
      Y (H + 2 * k + 1) = true ∧
      (∀ j, H + 2 * k + 1 < j → Y j = false)) ∧
    (∀ W : Nat, 1 ≤ W → ∃ L X : Row,
      (∀ j, W < j → L j = false) ∧
      (∃ i, 1 ≤ i ∧ L i = true) ∧
      FinSupp X ∧
      (∀ t, t < W - 1 → zrow X t 1 = false) ∧
      (∀ j, zrow X (W - 1) j = zrow L (W - 1) j)) := by
  refine ⟨fun H k => ?_, fun W hW => ?_⟩
  · let p := H + k + 1
    let X := singleCell p
    let Y := zrow X k
    have hp_edge : X p = true ∧ ∀ j, p < j → X j = false :=
      ⟨by simp [X, singleCell], fun j hj => by simp [X, singleCell, show j ≠ p by omega]⟩
    have hedge_k := zrow_edge (by dsimp [p]; omega : 1 ≤ p) hp_edge.1 hp_edge.2 k
    refine ⟨X, Y, ⟨p, hp_edge.2⟩, ?_, fun _ => rfl, ?_, ?_, ?_⟩
    · intro t ht
      exact zrow_singleCell_white_before p t (by dsimp [p]; omega)
    · intro t ht
      rw [show zrow Y t 1 = zrow X (k + t) 1 from (zrow_shift X k t 1).symm]
      exact zrow_singleCell_white_before p (k + t) (by dsimp [p]; omega)
    · simpa [Y, show p + k = H + 2 * k + 1 by dsimp [p]; omega] using hedge_k.1
    · intro j hj
      exact hedge_k.2 j (by dsimp [p]; omega)
  · let L := singleCell W
    have hL_edge : L W = true ∧ ∀ j, W < j → L j = false :=
      ⟨by simp [L, singleCell], fun j hj => by simp [L, singleCell, show j ≠ W by omega]⟩
    refine ⟨L, L, hL_edge.2, ⟨W, hW, hL_edge.1⟩, ⟨W, hL_edge.2⟩, ?_, fun _ => rfl⟩
    intro t ht
    exact zrow_singleCell_white_before W t (by omega)

end Ruliology.CellularAutomata.Rule30WallRecordAncestry
