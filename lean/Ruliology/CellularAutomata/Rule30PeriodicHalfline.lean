module

public import Ruliology.CellularAutomata.Rule30Period21Profiles
public import Ruliology.CellularAutomata.Rule30Ether

/-!
# Periodic right halves: columnwise onsets and inverse-chain rigidity

For any positive common temporal period, column-dependent onsets admit an
actual globally periodic representative with the same eventual absolute
time profiles. A finitely coded inverse chain propagates any forward-closed
property from its head. Applied to Rule30 profile pairs, any temporal
symmetry of the two head columns propagates through the whole right half.
The generic module has no t001-family or TrapPeriod21-certificate dependency.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodicHalfline

open Ruliology.CellularAutomata Rule30Ether

def representative (F : Nat → Nat → Bool) (p : Nat) (onset : Nat → Nat) :
    Nat → Nat → Bool := fun t i => F (t + onset i * p) i

theorem le_mul_period (n p : Nat) (hp : 0 < p) : n ≤ n * p := by
  have h := Nat.mul_le_mul_left n (show 1 ≤ p by omega)
  simpa using h

/-- Any valid onset for this column suffices, not just the chosen onset. -/
theorem representative_agrees_from (F : Nat → Nat → Bool) (p : Nat)
    (onset : Nat → Nat) (i T : Nat)
    (h : ∀ t, T ≤ t → F (t+p) i = F t i) (t : Nat) (ht : T ≤ t) :
    representative F p onset t i = F t i := by
  exact Rule30Jen.periodic_mul (f := fun t => F t i) (P := p) h (onset i) t ht

theorem representative_periodic (F : Nat → Nat → Bool) (p : Nat) (hp : 0 < p)
    (onset : Nat → Nat)
    (h : ∀ i t, onset i ≤ t → F (t+p) i = F t i) :
    ∀ t i, representative F p onset (t+p) i = representative F p onset t i := by
  intro t i
  have ht : onset i ≤ t + onset i * p := by
    have := le_mul_period (onset i) p hp
    omega
  simpa only [representative, Nat.add_right_comm] using h i (t + onset i * p) ht

theorem representative_shift (F : Nat → Nat → Bool) (p : Nat) (hp : 0 < p)
    (onset : Nat → Nat)
    (h : ∀ i t, onset i ≤ t → F (t+p) i = F t i) (i k t : Nat) :
    representative F p onset (t+k*p) i = representative F p onset t i := by
  exact Rule30Jen.periodic_mul (f := fun t => representative F p onset t i)
    (T := 0) (P := p) (fun t _ => representative_periodic F p hp onset h t i) k t (by omega)

/-- The three columns in one stencil are aligned at a common multiple of p. -/
theorem representative_isR30 (F : Nat → Nat → Bool) (hF : IsR30 F)
    (p : Nat) (hp : 0 < p) (onset : Nat → Nat)
    (h : ∀ i t, onset i ≤ t → F (t+p) i = F t i) :
    IsR30 (representative F p onset) := by
  intro t i
  let m := onset i + onset (i+1) + onset (i+2)
  have hm : m ≤ m*p := le_mul_period m p hp
  have bound0 : onset i ≤ t+m*p := by dsimp [m] at *; omega
  have bound1 : onset (i+1) ≤ t+m*p := by dsimp [m] at *; omega
  have bound2 : onset (i+2) ≤ t+m*p := by dsimp [m] at *; omega
  have eq0 : representative F p onset t i = F (t+m*p) i :=
    (representative_shift F p hp onset h i m t).symm.trans
      (representative_agrees_from F p onset i (onset i) (h i) _ bound0)
  have eq1 : representative F p onset t (i+1) = F (t+m*p) (i+1) :=
    (representative_shift F p hp onset h (i+1) m t).symm.trans
      (representative_agrees_from F p onset (i+1) (onset (i+1)) (h (i+1)) _ bound1)
  have eq2 : representative F p onset t (i+2) = F (t+m*p) (i+2) :=
    (representative_shift F p hp onset h (i+2) m t).symm.trans
      (representative_agrees_from F p onset (i+2) (onset (i+2)) (h (i+2)) _ bound2)
  have eqn : representative F p onset (t+1) (i+1) = F ((t+m*p)+1) (i+1) := by
    have he := (representative_shift F p hp onset h (i+1) m (t+1)).symm.trans
      (representative_agrees_from F p onset (i+1) (onset (i+1)) (h (i+1))
        (t+1+m*p) (by omega))
    simpa only [Nat.add_right_comm] using he
  rw [eqn, hF (t+m*p) i, eq0, eq1, eq2]

/-- Every already periodic column is preserved, including a prescribed boundary. -/
theorem representative_preserves_column (F : Nat → Nat → Bool) (p : Nat)
    (onset : Nat → Nat) (i : Nat) (h : ∀ t, F (t+p) i = F t i) :
    ∀ t, representative F p onset t i = F t i := by
  intro t
  exact representative_agrees_from F p onset i 0 (fun t _ => h t) t (by omega)

/-- Simultaneous late agreement is available on every finite spatial prefix. -/
theorem representative_finite_agreement (F : Nat → Nat → Bool) (p : Nat)
    (onset : Nat → Nat)
    (h : ∀ i t, onset i ≤ t → F (t+p) i = F t i) (b : Nat) :
    ∃ S, ∀ i, i ≤ b → ∀ t, S ≤ t → representative F p onset t i = F t i := by
  induction b with
  | zero =>
    refine ⟨onset 0, ?_⟩
    intro i hi t ht
    have he : i=0 := by omega
    subst i
    exact representative_agrees_from F p onset 0 (onset 0) (h 0) t ht
  | succ b ih =>
    obtain ⟨S,hS⟩ := ih
    refine ⟨S + onset (b+1), ?_⟩
    intro i hi t ht
    by_cases hb : i ≤ b
    · exact hS i hb t (by omega)
    · have he : i=b+1 := by omega
      subst i
      exact representative_agrees_from F p onset (b+1) (onset (b+1)) (h (b+1)) t (by omega)

/-- No uniform spatial onset is required. All profiles retain absolute time residues. -/
theorem exists_periodic_representative (F : Nat → Nat → Bool) (hF : IsR30 F)
    (p : Nat) (hp : 0 < p)
    (h : ∀ i, ∃ T, ∀ t, T ≤ t → F (t+p) i = F t i) :
    ∃ G : Nat → Nat → Bool, IsR30 G ∧
      (∀ t i, G (t+p) i = G t i) ∧
      (∀ i, ∃ T, ∀ t, T ≤ t → G t i = F t i) := by
  classical
  let onset : Nat → Nat := fun i => Classical.choose (h i)
  have ho : ∀ i t, onset i ≤ t → F (t+p) i = F t i :=
    fun i => Classical.choose_spec (h i)
  refine ⟨representative F p onset, representative_isR30 F hF p hp onset ho,
    representative_periodic F p hp onset ho, ?_⟩
  intro i
  exact ⟨onset i, representative_agrees_from F p onset i (onset i) (ho i)⟩

open Ruliology.CellularAutomata Rule30Ether
open Rule30Period21Profiles

theorem coded_inverse_return {α : Type} (f : α → α) (s : Nat → α)
    (w : Nat) (code : α → List Bool)
    (hlen : ∀ n, (code (s n)).length = w)
    (hinj : ∀ i j, code (s i) = code (s j) → s i = s j)
    (hs : ∀ n, f (s (n+1)) = s n) :
    ∃ q, 0 < q ∧ advance f q (s 0) = s 0 := by
  obtain ⟨i,j,hij,_,he⟩ := Rule30Jen.pigeonhole w (fun n => code (s n)) hlen
  exact inverse_collision f s hs hij (hinj i j he)

/-- Every state on a finitely coded infinite inverse chain is forward-reachable from its head. -/
theorem coded_inverse_forward {α : Type} (f : α → α) (s : Nat → α)
    (w : Nat) (code : α → List Bool)
    (hlen : ∀ n, (code (s n)).length = w)
    (hinj : ∀ i j, code (s i) = code (s j) → s i = s j)
    (hs : ∀ n, f (s (n+1)) = s n) (n : Nat) :
    ∃ k, advance f k (s 0) = s n := by
  obtain ⟨q,hq,hr⟩ := coded_inverse_return f (fun j => s (n+j)) w code
    (fun j => hlen (n+j)) (fun i j => hinj (n+i) (n+j))
    (fun j => by simpa only [Nat.add_assoc] using hs (n+j))
  change advance f q (s n) = s n at hr
  have hn : advance f n (s n) = s 0 := by
    simpa using inverse_advance f s hs 0 n
  refine ⟨(q-1)*n, ?_⟩
  have he : n+(q-1)*n = n*q := by
    rw [Nat.mul_comm n q, Nat.add_comm n ((q-1)*n), ← Nat.succ_mul]
    congr 1
    omega
  calc advance f ((q-1)*n) (s 0)
      = advance f ((q-1)*n) (advance f n (s n)) := by rw [hn]
    _ = advance f (n+(q-1)*n) (s n) := (advance_add f n ((q-1)*n) (s n)).symm
    _ = s n := by rw [he]; exact advance_return_mul hr n

theorem advance_preserves {α : Type} (f : α → α) (P : α → Prop)
    (h : ∀ a, P a → P (f a)) (n : Nat) (a : α) (ha : P a) :
    P (advance f n a) := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih => exact ih (f a) (h a ha)

theorem coded_inverse_propagates {α : Type} (f : α → α) (s : Nat → α)
    (w : Nat) (code : α → List Bool)
    (hlen : ∀ n, (code (s n)).length = w)
    (hinj : ∀ i j, code (s i) = code (s j) → s i = s j)
    (hs : ∀ n, f (s (n+1)) = s n)
    (P : α → Prop) (hstep : ∀ a, P a → P (f a)) (h0 : P (s 0)) :
    ∀ n, P (s n) := by
  intro n
  obtain ⟨k,hk⟩ := coded_inverse_forward f s w code hlen hinj hs n
  rw [← hk]
  exact advance_preserves f P hstep k (s 0) h0

/-- Equivalent commuting-map form of the same rigidity principle. -/
theorem coded_inverse_commuting {α : Type} (f H : α → α) (s : Nat → α)
    (w : Nat) (code : α → List Bool)
    (hlen : ∀ n, (code (s n)).length = w)
    (hinj : ∀ i j, code (s i) = code (s j) → s i = s j)
    (hs : ∀ n, f (s (n+1)) = s n)
    (hc : ∀ a, H (f a) = f (H a)) (h0 : H (s 0) = s 0) :
    ∀ n, H (s n) = s n := by
  apply coded_inverse_propagates f s w code hlen hinj hs (fun a => H a = a)
  · intro a ha
    rw [hc, ha]
  · exact h0

abbrev Pair := (Nat → Bool) × (Nat → Bool)
def predecessor (a : Pair) : Pair :=
  (fun t => xor (a.1 (t+1)) (a.1 t || a.2 t), a.1)
def PairPeriodic (p : Nat) (a : Pair) : Prop :=
  (∀ t, a.1 (t+p) = a.1 t) ∧ (∀ t, a.2 (t+p) = a.2 t)
def pairCode (p : Nat) (a : Pair) : List Bool :=
  (List.range (2*p)).map (fun k => if k<p then a.1 k else a.2 (k-p))

theorem periodic_mod (f : Nat → Bool) (p : Nat) (h : ∀ t, f (t+p)=f t) (t : Nat) :
    f t = f (t%p) := by
  have he : t%p+(t/p)*p=t := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div t p
  have hm := Rule30Jen.periodic_mul (f:=f) (T:=0) (P:=p) (fun t _ => h t)
    (t/p) (t%p) (by omega)
  rwa [he] at hm

theorem pairCode_injective (p : Nat) (hp : 0<p) (a b : Pair)
    (ha : PairPeriodic p a) (hb : PairPeriodic p b) (he : pairCode p a = pairCode p b) :
    a=b := by
  have hbit (k : Nat) (hk : k<2*p) :
      (if k<p then a.1 k else a.2 (k-p)) =
      (if k<p then b.1 k else b.2 (k-p)) := by
    have h := congrArg (fun l : List Bool => l.getD k false) he
    simpa only [pairCode, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some] using h
  apply Prod.ext
  · funext t
    rw [periodic_mod a.1 p ha.1 t, periodic_mod b.1 p hb.1 t]
    have ht := Nat.mod_lt t hp
    simpa only [ite_eq_left ht] using hbit (t%p) (by omega)
  · funext t
    rw [periodic_mod a.2 p ha.2 t, periodic_mod b.2 p hb.2 t]
    have ht := Nat.mod_lt t hp
    simpa only [ite_eq_right (show ¬ p+t%p<p by omega), Nat.add_sub_cancel_left] using
      hbit (p+t%p) (by omega)

theorem predecessor_preserves_period (r : Nat) (a : Pair) (h : PairPeriodic r a) :
    PairPeriodic r (predecessor a) := by
  constructor
  · intro t
    change xor (a.1 (t+r+1)) (a.1 (t+r) || a.2 (t+r)) = _
    rw [show t+r+1=(t+1)+r by omega,h.1 (t+1),h.1 t,h.2 t]
    rfl
  · exact h.1

/-- Any common temporal clock makes the head's temporal symmetry propagate right. -/
theorem common_period_head_rigidity (F : Nat → Nat → Bool) (hF : IsR30 F)
    (p : Nat) (hp : 0<p) (hper : ∀ t j, F (t+p) j=F t j)
    (r : Nat) (h0 : ∀ t, F (t+r) 0=F t 0) (h1 : ∀ t, F (t+r) 1=F t 1) :
    ∀ t j, F (t+r) j=F t j := by
  let s : Nat → Pair := fun j => (fun t => F t j, fun t => F t (j+1))
  have sp : ∀ j, PairPeriodic p (s j) := fun j => ⟨fun t => hper t j,fun t => hper t (j+1)⟩
  have hs : ∀ j, predecessor (s (j+1))=s j := by
    intro j
    apply Prod.ext
    · funext t
      change xor (F (t+1) (j+1)) (F t (j+1) || F t (j+2)) = F t j
      rw [hF t j]
      unfold Rule30Jen.rule
      cases F t j <;> cases (F t (j+1) || F t (j+2)) <;> rfl
    · rfl
  have hall := coded_inverse_propagates predecessor s (2*p) (pairCode p)
    (fun j => by simp only [pairCode,List.length_map,List.length_range])
    (fun i j => pairCode_injective p hp (s i) (s j) (sp i) (sp j)) hs
    (PairPeriodic r) (predecessor_preserves_period r) (show PairPeriodic r (s 0) from ⟨h0,h1⟩)
  intro t j
  exact (hall j).1 t

theorem periodic_of_eventual_period (f : Nat → Bool) (p : Nat) (hp : 0<p)
    (hper : ∀ t, f (t+p)=f t) (r T : Nat)
    (h : ∀ t, T≤t → f (t+r)=f t) : ∀ t, f (t+r)=f t := by
  intro t
  have hT := le_mul_period T p hp
  have hs (u : Nat) : f (u+T*p)=f u :=
    Rule30Jen.periodic_mul (f:=f) (T:=0) (P:=p) (fun t _ => hper t) T u (by omega)
  calc f (t+r) = f (t+r+T*p) := (hs (t+r)).symm
    _ = f (t+T*p+r) := by congr 1; omega
    _ = f (t+T*p) := h _ (by omega)
    _ = f t := hs t

theorem eventual_period_congr (f g : Nat → Bool) (r S T : Nat)
    (he : ∀ t, S≤t → f t=g t) (hp : ∀ t, T≤t → f (t+r)=f t) :
    ∀ t, S+T≤t → g (t+r)=g t := by
  intro t ht
  rw [← he (t+r) (by omega),← he t (by omega),hp t (by omega)]

/-- The common period may have a different onset in EVERY column. -/
theorem eventual_common_period_head_rigidity (F : Nat → Nat → Bool) (hF : IsR30 F)
    (p : Nat) (hp : 0<p) (hper : ∀ j, ∃ S, ∀ t, S≤t → F (t+p) j=F t j)
    (r : Nat) (h0 : ∃ T, ∀ t, T≤t → F (t+r) 0=F t 0)
    (h1 : ∃ T, ∀ t, T≤t → F (t+r) 1=F t 1) :
    ∀ j, ∃ T, ∀ t, T≤t → F (t+r) j=F t j := by
  obtain ⟨G,hG,hGp,he⟩ := exists_periodic_representative F hF p hp hper
  have gh (j : Nat) (hj : ∃ T, ∀ t, T≤t → F (t+r) j=F t j) :
      ∀ t, G (t+r) j=G t j := by
    obtain ⟨S,hS⟩ := he j
    obtain ⟨T,hT⟩ := hj
    exact periodic_of_eventual_period (fun t => G t j) p hp (fun t => hGp t j) r (S+T)
      (eventual_period_congr (fun t => F t j) (fun t => G t j) r S T
        (fun t ht => (hS t ht).symm) hT)
  have gr := common_period_head_rigidity G hG p hp hGp r (gh 0 h0) (gh 1 h1)
  intro j
  obtain ⟨S,hS⟩ := he j
  refine ⟨S, ?_⟩
  intro t ht
  rw [← hS (t+r) (by omega),← hS t ht,gr t j]

end Ruliology.CellularAutomata.Rule30PeriodicHalfline
