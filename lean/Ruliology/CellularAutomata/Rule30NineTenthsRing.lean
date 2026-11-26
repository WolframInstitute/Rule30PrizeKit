module

public import Ruliology.CellularAutomata.Rule30DensityEscape

/-! A bounded upper-corner deficit forces the two observed columns onto one
ten-tick cycle. Its sideways reconstruction identifies the entire left half,
from a common onset, with a single 155-column film. This gives the least width
at the corner on rings of arbitrary temporal period. The proof uses S9's
nonnegative losses and its checked graph of zero-loss edges. -/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30NineTenthsRing

open Ruliology.CellularAutomata Rule30Jen Rule30SourceDensityRegion

abbrev Word := BitVec 10
abbrev Pair := Word × Word

/-- Bit t is the cell at tick t. Rotate right to read the next temporal bit. -/
def previous (p : Pair) : Pair :=
  (p.1.rotateRight 1 ^^^ (p.1 ||| p.2), p.1)

def table : Array Pair :=
  (List.range 155).foldl (fun a _ => a.push (previous a.back!)) #[(511,341)]

def column (d t : Nat) : Bool := (table[d%155]!).1.getLsbD (t%10)
def right (d t : Nat) : Bool := (table[d%155]!).2.getLsbD (t%10)

private theorem origin_bits (t : Nat) :
    column 0 t = decide (t%10 < 9) ∧ right 0 t = decide (t%2=0) := by
  have bits : ∀ i : Fin 10, column 0 i = decide (i.val<9) ∧ right 0 i = decide (i.val%2=0) := by
    decide +kernel
  simpa only [column, right, show t%10%10=t%10 by omega, show t%10%2=t%2 by omega] using
    bits ⟨t%10,by omega⟩

private theorem seam (d t : Nat) :
    column (d+1) t = xor (column d (t+1)) (column d t || right d t) ∧ right (d+1) t=column d t := by
  have rows : ∀ i : Fin 155, ∀ s : Fin 10,
      column (i.val+1) s = xor (column i (s.val+1)) (column i s || right i s) ∧
      right (i.val+1) s = column i s := by decide +kernel
  simpa only [column, right, show d%155%155=d%155 by omega, show (d%155+1)%155=(d+1)%155 by omega,
    show t%10%10=t%10 by omega, show (t%10+1)%10=(t+1)%10 by omega] using
    rows ⟨d%155,by omega⟩ ⟨t%10,by omega⟩

private theorem distinct (d : Nat) (h : ∀ t, column d t = column 0 t ∧ right d t = right 0 t) :
    155 ∣ d := by
  have first : ∀ i : Fin 155, (∀ t : Fin 10,
      column i t = column 0 t ∧ right i t = right 0 t) → i.val=0 := by decide +kernel
  apply Nat.dvd_of_mod_eq_zero
  apply first ⟨d%155,by omega⟩
  intro t
  simpa only [column, right, show d%155%155=d%155 by omega] using h t

/-- Normalized phase at the observed bond. -/
def Aligned (u : History) (j : Int) : Prop := ∀ t : Nat,
  u t j = decide (t%10 < 9) ∧ u t (j+1) = decide (t%2=0)

private theorem forced_left {u : History} (hu : Evolution u) {j : Int} (h : Aligned u j)
    (d t : Nat) : u t (j-(d:Int)) = column d t ∧ u t (j-(d:Int)+1) = right d t := by
  induction d generalizing t with
  | zero => simpa only [show j-((0:Nat):Int)=j by omega] using
      And.intro ((h t).1.trans (origin_bits t).1.symm) ((h t).2.trans (origin_bits t).2.symm)
  | succ d ih =>
    have step := hu t (j-(d:Int))
    have inv : u t (j-(d:Int)-1) = xor (u (t+1) (j-(d:Int))) (u t (j-(d:Int)) || u t (j-(d:Int)+1)) := by
      rw [step]
      cases u t (j-(d:Int)-1) <;> cases u t (j-(d:Int)) <;> cases u t (j-(d:Int)+1) <;> rfl
    rw [(ih (t+1)).1,(ih t).1,(ih t).2] at inv
    rw [show j-((d+1:Nat):Int)=j-(d:Int)-1 by omega, show j-(d:Int)-1+1=j-(d:Int) by omega]
    exact ⟨inv.trans (seam d t).1.symm, (ih t).1.trans (seam d t).2.symm⟩

/-- Any spatial return of this two-column movie has width divisible by 155.
There is no assumption about the rest of the initial row. -/
theorem return_multiple {u : History} (hu : Evolution u) {j : Int} (h : Aligned u j) (w : Nat)
    (again : Aligned u (j-(w:Int))) : 155 ∣ w := by
  apply distinct
  intro t
  obtain ⟨f,g⟩ := forced_left hu h w t
  exact ⟨f.symm.trans ((again t).1.trans (origin_bits t).1.symm),
         g.symm.trans ((again t).2.trans (origin_bits t).2.symm)⟩

/-- Two histories with the aligned movie agree on the whole left half at every time. -/
theorem left_unique {u v : History} (hu : Evolution u) (hv : Evolution v) {j k : Int}
    (h : Aligned u j) (g : Aligned v k) (d t : Nat) : u t (j-(d:Int))=v t (k-(d:Int)) :=
  (forced_left hu h d t).1.trans (forced_left hv g d t).1.symm

/-! Four rounds of removing vertices without a surviving incoming and outgoing edge
leave fourteen words in S9's zero-loss graph. Each has one of ten phases. -/
open Rule30DensityEscape

private def mask (n : Nat) : Nat :=
  #[18446744073709551615,9946906258802117130,9946906224442376706,
    9946906224408822272,723534187554046464].getD n 0
private def live (n : Nat) (v : W) := (mask n).testBit v.val
private def phase (v : W) : Nat := match v.val with
  | 39 => 0 | 57 => 1 | 15 => 2 | 17 | 49 => 3 | 27 | 59 => 4
  | 9 | 41 => 5 | 31 | 47 => 6 | 33 => 7 | 51 => 8 | _ => 9

private theorem survive (path : Nat → W) (edges : ∀ t, path (t+1) ∈ Rule30DensityEscape.next true (path t))
    (n : Nat) (hn : n≤4) (t : Nat) (ht : n≤t) : live n (path t)=true := by
  have full : ∀ v : W, live 0 v=true := by decide +kernel
  have prune : ∀ k : Fin 4, ∀ x : W, live k x=true →
      (∃ p : W, live k p=true ∧ x ∈ Rule30DensityEscape.next true p) →
      (∃ q : W, live k q=true ∧ q ∈ Rule30DensityEscape.next true x) →
      live (k.val+1) x=true := by decide +kernel
  induction n generalizing t with
  | zero => exact full _
  | succ n ih =>
    obtain ⟨s,rfl⟩ : ∃ s,t=s+1 := ⟨t-1,by omega⟩
    exact prune ⟨n,by omega⟩ _ (ih (by omega) _ (by omega))
      ⟨path s,ih (by omega) _ (by omega),edges s⟩
      ⟨path (s+1+1),ih (by omega) _ (by omega),edges (s+1)⟩

private theorem tight_tail {u : History} (hu : Evolution u) (j : Int) (s : Nat)
    (flat : ∀ t, loss true (band u j (s+t)) (band u j (s+t+1))=0) :
    ∃ b, Aligned (fun t => u (b+t)) j := by
  let path (t : Nat) := band u j (s+t)
  have edges (t : Nat) : path (t+1) ∈ Rule30DensityEscape.next true (path t) :=
    (band_edge hu true j (s+t)).2 (flat t)
  have adv : ∀ x y : W, live 4 x=true → live 4 y=true → y ∈ Rule30DensityEscape.next true x →
      phase y=(phase x+1)%10 := by decide +kernel
  have labels : ∀ a b c d e f : Bool, let x := pack a b c d e f
    live 4 x=true → a=decide (phase x<9) ∧ b=decide (phase x%2=0) := by decide +kernel
  have ph (t : Nat) : phase (path (4+t))=(phase (path 4)+t)%10 := by
    induction t with
    | zero =>
      have small : ∀ x : W, phase x<10 := by decide +kernel
      simp [Nat.mod_eq_of_lt (small _)]
    | succ t ih =>
      rw [show 4+(t+1)=4+t+1 by omega, adv _ _ (survive path edges 4 (by decide) _ (by omega))
        (survive path edges 4 (by decide) _ (by omega)) (edges _),ih]
      omega
  let shift := 10-phase (path 4)
  have small : ∀ x : W, phase x<10 := by decide +kernel
  refine ⟨s+4+shift,fun t => ?_⟩
  let n := 4+(shift+t)
  have pp : phase (path n)=t%10 := by
    rw [ph]
    dsimp [shift]
    have := small (path 4)
    omega
  have v := labels (u (s+n) j) (u (s+n) (j+1)) (u (s+n) (j+2))
    (u (s+n) (j+3)) (u (s+n) (j+4)) (u (s+n) (j+5))
    (survive path edges 4 (by decide) n (by dsimp [n];omega))
  change u (s+n) j=decide (phase (path n)<9) ∧ u (s+n) (j+1)=decide (phase (path n)%2=0) at v
  change u (s+4+shift+t) j=_ ∧ u (s+4+shift+t) (j+1)=_
  simpa only [show s+4+shift+t=s+n by dsimp [n];omega, pp, show t%10%2=t%2 by omega] using v

private theorem acc_mono {u : History} (hu : Evolution u) (j : Int) {t n : Nat} (h : t≤n) :
    accumulated true u j t ≤ accumulated true u j n := by
  induction n with
  | zero => have : t=0 := by omega
            subst t; exact Int.le_refl _
  | succ n ih =>
    by_cases eq : t=n+1
    · subst t; exact Int.le_refl _
    · have old := ih (by omega)
      have nonneg := (band_edge hu true j n).1
      rw [accumulated_step];omega

/-- Bounded upper-corner deficit eventually forces the aligned pair, on any full-line history. -/
theorem aligned_of_bounded {u : History} (hu : Evolution u) (j : Int) (B : Int)
    (h : ∀ n : Nat, 6*(n:Int)+3*ends u j 0 n-8*black u j 0 n ≤ B) :
    ∃ s, Aligned (fun t => u (s+t)) j := by
  classical
  let F := accumulated true u j
  have bound (n : Nat) : F n ≤ B+6 := by
    have p := (range_potential true (band u j 0)).2
    have q := (range_potential true (band u j n)).1
    change potential true (band u j 0)-potential true (band u j n)+6*(n:Int)+
      3*ends u j 0 n-8*black u j 0 n ≤ B+6
    have := h n
    omega
  have attain (k s : Nat) (hk : (B+6-F s).toNat≤k) : ∃ z, ∀ t, F t≤F z := by
    induction k generalizing s with
    | zero => exact ⟨s,fun t => by have := bound t; omega⟩
    | succ k ih =>
      by_cases top : ∀ t, F t≤F s
      · exact ⟨s,top⟩
      · have better : ∃ t, F s<F t := Classical.byContradiction (fun no =>
          top (fun t => by
            by_cases gt : F s<F t
            · exact False.elim (no ⟨t,gt⟩)
            · omega))
        obtain ⟨t,lt⟩ := better
        exact ih t (by have := bound t;omega)
  obtain ⟨s,maximal⟩ := attain _ 0 (Nat.le_refl _)
  apply tight_tail hu j s
  intro t
  have hi := maximal (s+t+1)
  have lo := acc_mono hu j (t:=s) (n:=s+t) (by omega)
  have next := accumulated_step true u j (s+t)
  have pos := (band_edge hu true j (s+t)).1
  dsimp [F] at hi
  omega

/-- A spatially periodic physical cycle of arbitrary temporal period can attain the
upper corner only at a width divisible by 155. The one exposing equality suffices. -/
theorem ring_width {u : History} (hu : Evolution u) (j : Int) (w p : Nat) (hp : 0<p)
    (time : ∀ t, u (t+p)=u t) (space : ∀ t i, u t (i-(w:Int))=u t i)
    (balance : 6*(p:Int)+3*ends u j 0 p-8*black u j 0 p=0) : 155 ∣ w := by
  let L (t : Nat) := loss true (band u j t) (band u j (t+1))
  have bp (t : Nat) : band u j (t+p)=band u j t := by simp only [band,time]
  have lp (t : Nat) : L (t+p)=L t := by
    simp only [L,show t+p+1=t+1+p by omega,bp]
  have e₀ : accumulated true u j 0=0 := by simp [accumulated,black,ends,Rule30SourceObservables.count]
  have ep : accumulated true u j p=0 := by
    change potential true (band u j 0)-potential true (band u j p)+6*(p:Int)+
      3*ends u j 0 p-8*black u j 0 p=0
    have same : band u j p=band u j 0 := by simpa using bp 0
    rw [same];omega
  have first (t : Nat) (ht : t<p) : L t=0 := by
    have lo := acc_mono hu j (t:=0) (n:=t) (by omega)
    have hi := acc_mono hu j (t:=t+1) (n:=p) (by omega)
    have pos := (band_edge hu true j t).1
    have eq := accumulated_step true u j t
    dsimp [L];omega
  have flat (t : Nat) : L t=0 := by
    induction t using Nat.strongRecOn with
    | ind t ih =>
      by_cases early : t<p
      · exact first t early
      · rw [← Nat.sub_add_cancel (show p≤t by omega),lp]
        exact ih _ (by omega)
  obtain ⟨s,align⟩ := tight_tail hu j 0 (fun t => by simpa [L] using flat t)
  have phys : Evolution (fun t => u (s+t)) := fun t i => hu (s+t) i
  apply return_multiple phys align w
  intro t
  obtain ⟨b,r⟩ := align t
  change u (s+t) (j-(w:Int))=_ ∧ u (s+t) (j-(w:Int)+1)=_
  rw [space, show j-(w:Int)+1=j+1-(w:Int) by omega,space]
  exact ⟨b,r⟩

/-- The normalized ten-by-155 corner film, observed at sites 0 and 1. -/
def film (t : Nat) (i : Int) : Bool := column (155-(i%155).toNat) t

private theorem film_step : Evolution film := by
  have cells : ∀ t : Fin 10, ∀ j : Fin 155, film (t.val+1) j.val =
      rule (film t (j.val-1 : Int)) (film t j.val) (film t (j.val+1 : Int)) := by decide +kernel
  intro t i
  let j := (i%155).toNat
  have hj : j<155 := by dsimp [j];omega
  have idx : (j:Int)=i%155 := by dsimp [j];omega
  have v := cells ⟨t%10,by omega⟩ ⟨j,hj⟩
  simpa only [film,column,idx,show (t%10+1)%10=(t+1)%10 by omega,show t%10%10=t%10 by omega,
    show i%155%155=i%155 by omega,show (i%155-1)%155=(i-1)%155 by omega,
    show (i%155+1)%155=(i+1)%155 by omega] using v

/-- A common onset identifies every column at and to the left of the observed
site with this one periodic film, even when the full history is aperiodic. -/
theorem rigid_left_of_bounded {u : History} (hu : Evolution u) (j : Int) (B : Int)
    (h : ∀ n : Nat, 6*(n:Int)+3*ends u j 0 n-8*black u j 0 n ≤ B) :
    ∃ s, ∀ d t : Nat, u (s+t) (j-(d:Int))=film t (0-(d:Int)) := by
  have aligned : Aligned film 0 := by
    have bits : ∀ i : Fin 10, film i 0=decide (i.val<9) ∧ film i 1=decide (i.val%2=0) := by
      decide +kernel
    intro t
    simpa only [Int.zero_add,film,column,show t%10%10=t%10 by omega,show t%10%2=t%2 by omega] using
      bits ⟨t%10,by omega⟩
  obtain ⟨s,hp⟩ := aligned_of_bounded hu j B h
  have hs : Evolution (fun t => u (s+t)) := fun t i => hu (s+t) i
  exact ⟨s,fun d t => left_unique hs film_step hp aligned d t⟩

/-- The bound is attained on a physical ten-tick cycle with the stated corner counts. -/
theorem sharp_ring : ∃ u : History, Evolution u ∧ (∀ t, u (t+10)=u t) ∧
    (∀ t i, u t (i-155)=u t i) ∧ black u 0 0 10=9 ∧ ends u 0 0 10=4 := by
  refine ⟨film,film_step,?_,?_,by decide +kernel,by decide +kernel⟩
  · intro t;funext i
    simp only [film,column,show (t+10)%10=t%10 by omega]
  · intro t i
    simp only [film,show (i-155)%155=i%155 by omega]

end Ruliology.CellularAutomata.Rule30NineTenthsRing

