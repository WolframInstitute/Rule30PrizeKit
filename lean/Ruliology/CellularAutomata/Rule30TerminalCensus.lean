module
public import Ruliology.CellularAutomata.Rule30HorizontalDiversityBounds

/-! Disjoint pairs of agreeing singleton histories bound a whole horizontal vocabulary.
The same terminal spatial width may be used at every transport depth. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30TerminalCensus
open Rule30Jen Rule30Prize

def bit (t j : Nat) := cell t (-(j:Int))
def Agree (s t u : Nat) : Prop := ∀ j<s, bit t j=bit u j
def Fork (s t u : Nat) : Prop := Agree s t u ∧ bit t s≠bit u s

private theorem tick {t j : Nat} (hj : 0<j) :
    bit (t+1) j = rule (bit t (j+1)) (bit t j) (bit t (j-1)) := by
  unfold bit; rw [cell]; congr 2 <;> omega

theorem fork_step {s t u : Nat} (hs : 0<s) (old : Fork (s+1) t u)
    (hc : bit (t+1) 0=bit (u+1) 0) : Fork s (t+1) (u+1) := by
  obtain ⟨same,diff⟩ := old
  constructor
  · intro j hj
    by_cases z : j=0
    · simpa [z] using hc
    · rw [tick (by omega : 0<j),tick (by omega : 0<j),same (j+1) (by omega),
         same j (by omega),same (j-1) (by omega)]
  · simpa [tick hs,rule,same s (by omega),same (s-1) (by omega)] using diff

theorem fork_transport {s r t u : Nat} (hr : r<s) (old : Fork s t u)
    (hc : ∀ j, 0<j → j≤r → bit (t+j) 0=bit (u+j) 0) : Fork (s-r) (t+r) (u+r) := by
  induction r with
  | zero => simpa using old
  | succ r ih =>
    have h := ih (by omega) (fun j hj hjr => hc j hj (by omega))
    have h' : Fork ((s-(r+1))+1) (t+r) (u+r) := by rwa [show s-(r+1)+1=s-r by omega]
    exact fork_step (by omega) h' (by simpa [Nat.add_assoc] using hc (r+1) (by omega) (Nat.le_refl _))

/-- Count represented words agreeing with the observed prefix. Repetitions in the cover are allowed. -/
noncomputable def pool (C : List Nat) (j t : Nat) : Nat := by
  classical exact (C.filter (fun u => decide (Agree j u t))).length

private theorem cons_pool (a : Nat) (C : List Nat) (j t : Nat) :
    pool (a::C) j t = pool C j t + (if @decide (Agree j a t) (Classical.propDecidable _) then 1 else 0) := by
  classical by_cases h : Agree j a t <;> simp [pool,h]

private theorem shrink (C : List Nat) (j t : Nat) : pool C (j+1) t ≤ pool C j t := by
  classical
  induction C with
  | nil => simp [pool]
  | cons a C ih =>
    have imp (h : Agree (j+1) a t) : Agree j a t := fun i hi => h i (by omega)
    by_cases h : Agree (j+1) a t <;> by_cases g : Agree j a t <;> simp [cons_pool,h,g] <;> grind

private theorem pool_eq (C : List Nat) {j t u : Nat} (same : Agree j t u) : pool C j t = pool C j u := by
  classical
  have ab (k : Nat) : Agree j k t ↔ Agree j k u :=
    ⟨fun h i hi => (h i hi).trans (same i hi), fun h i hi => (h i hi).trans (same i hi).symm⟩
  simp only [pool,ab]

private theorem capacity (C : List Nat) {j t u : Nat} (hf : Fork j t u) :
    pool C (j+1) t + pool C (j+1) u ≤ pool C j t := by
  classical
  induction C with
  | nil => simp [pool]
  | cons a C ih =>
    have only (h : Agree (j+1) a t) (g : Agree (j+1) a u) : False :=
      hf.2 ((h j (by omega)).symm.trans (g j (by omega)))
    have ht (h : Agree (j+1) a t) : Agree j a t := fun i hi => h i (by omega)
    have hu (h : Agree (j+1) a u) : Agree j a t := fun i hi => (h i (by omega)).trans (hf.1 i hi).symm
    by_cases h : Agree (j+1) a t <;> by_cases g : Agree (j+1) a u <;> by_cases f : Agree j a t <;>
      simp [cons_pool,h,g,f] <;> grind

private theorem geom_aux (a d : Nat) : 4*(a*(a+d)) ≤ (a+(a+d))*(a+(a+d)) := by
  simp [Nat.mul_add,Nat.add_mul,Nat.mul_comm]
  omega

private theorem geom (a b : Nat) : 4*(a*b) ≤ (a+b)*(a+b) := by
  rcases Nat.le_total a b with h|h
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h; exact geom_aux a d
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
    simpa [Nat.add_comm,Nat.mul_comm] using geom_aux b d

private theorem fork_cost (C : List Nat) {j t u : Nat} (hf : Fork j t u) :
    4*(pool C (j+1) t * pool C (j+1) u) ≤ pool C j t * pool C j u := by
  have h := capacity C hf
  rw [←pool_eq C hf.1]
  exact Nat.le_trans (geom _ _) (Nat.mul_le_mul h h)

private def prod (f : Nat→Nat) : List Nat → Nat
  | []=>1
  | t::ts=>f t*prod f ts

private theorem perm_prod (f : Nat→Nat) {xs ys : List Nat} (h : xs.Perm ys) : prod f xs=prod f ys := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [prod,ih]
  | swap a b l => simp [prod,Nat.mul_left_comm]
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem append_prod (f : Nat→Nat) (xs ys : List Nat) : prod f (xs++ys) = prod f xs * prod f ys := by
  induction xs with
  | nil => simp [prod]
  | cons a l ih => simp [prod,ih,Nat.mul_assoc]

private theorem prod_mono {f g : Nat→Nat} (xs : List Nat) (h : ∀ t ∈ xs, f t ≤ g t) : prod f xs ≤ prod g xs := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a l ih => exact Nat.mul_le_mul (h _ (by simp)) (ih (fun t ht => h _ (by simp [ht])))

private theorem complete (xs ys : List Nat) (hn : xs.Nodup) (hs : xs ⊆ ys) : ∃ zs, ys.Perm (xs++zs) := by
  induction xs generalizing ys with
  | nil => exact ⟨ys,List.Perm.refl _⟩
  | cons a xs ih =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp hn
    have hm : a∈ys := hs (by simp)
    obtain ⟨zs,hz⟩ := ih (ys.erase a) hn (fun t ht =>
      (List.mem_erase_of_ne (show t≠a by intro eq; subst t; exact ha ht)).mpr (hs (by simp [ht])))
    exact ⟨zs,(List.perm_cons_erase hm).trans (hz.cons a)⟩

def endpoints : List (Nat×Nat) → List Nat
  | []=>[]
  | p::l=>p.1::p.2::endpoints l

private theorem raw_cost (C : List Nat) (j : Nat) (pairs : List (Nat×Nat))
    (h : ∀ p ∈ pairs,Fork j p.1 p.2) :
    4^pairs.length*prod (pool C (j+1)) (endpoints pairs) ≤ prod (pool C j) (endpoints pairs) := by
  induction pairs with
  | nil => simp [prod,endpoints]
  | cons a l ih =>
    have one := fork_cost C (h a (by simp))
    have tail := ih (fun t ht => h t (by simp [ht]))
    have z := Nat.mul_le_mul one tail
    simpa only [List.length_cons,Nat.pow_succ,endpoints,prod,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using z

private noncomputable def ledger (C : List Nat) (N j : Nat) := prod (pool C j) (List.range N)

private theorem step_cost (C : List Nat) (N j : Nat) (pairs : List (Nat×Nat))
    (hn : (endpoints pairs).Nodup) (inside : ∀ t∈endpoints pairs,t<N)
    (h : ∀ p∈pairs,Fork j p.1 p.2) : 4^pairs.length*ledger C N (j+1) ≤ ledger C N j := by
  obtain ⟨rest,perm⟩ := complete (endpoints pairs) (List.range N) hn (fun t ht => List.mem_range.mpr (inside t ht))
  unfold ledger
  rw [perm_prod _ perm,perm_prod (pool C j) perm,append_prod,append_prod,←Nat.mul_assoc]
  exact Nat.mul_le_mul (raw_cost C j pairs h) (prod_mono rest (fun t _ => shrink C j t))


private def moved (r : Nat) (pairs : List (Nat×Nat)) := pairs.map (fun p => (p.1+r,p.2+r))

private theorem moved_ends (r : Nat) (l : List (Nat×Nat)) :
    endpoints (moved r l)=(endpoints l).map (fun t=>t+r) := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [moved,List.map_cons,endpoints,List.cons.injEq,true_and] using ih

/-- Each list uses distinct starting ages. Different transport depths can use different lists. -/
structure Census (s N : Nat) where
  pairs : Nat → List (Nat×Nat)
  disjoint : ∀ r<s, (endpoints (pairs r)).Nodup
  within : ∀ r<s, ∀ t∈endpoints (pairs r),t+r<N
  split : ∀ r<s, ∀ p∈pairs r,Fork s p.1 p.2
  future : ∀ (r : Nat), r < s → ∀ (p : Nat × Nat), p ∈ pairs r →
    ∀ (i : Nat), (0 < i) → (i ≤ r) → bit (p.1+i) 0 = bit (p.2+i) 0

def pairSum (pairs : Nat→List (Nat×Nat)) : Nat→Nat
  | 0=>0
  | r+1=>pairSum pairs r+(pairs r).length

private theorem one_level {s N : Nat} (c : Census s N) (C : List Nat) {r : Nat} (hr : r<s) :
    4^(c.pairs r).length * ledger C N (s-r+1) ≤ ledger C N (s-r) := by
  let l := moved r (c.pairs r)
  have sz : l.length=(c.pairs r).length := by simp [l,moved]
  rw [←sz]
  apply step_cost C N (s-r) l
  · rw [show endpoints l=(endpoints (c.pairs r)).map (fun t=>t+r) from moved_ends _ _]
    exact List.Pairwise.map (fun t=>t+r) (by intro a b h0 eq; exact h0 (by omega)) (c.disjoint r hr)
  · intro t ht
    rw [show endpoints l=(endpoints (c.pairs r)).map (fun t=>t+r) from moved_ends _ _] at ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    exact c.within r hr a ha
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact fork_transport hr (c.split r hr a ha) (c.future r hr a ha)

/-- The collection `C` may be any set of representative ages for the old rows and newly exposed bit. -/
def Covers (C : List Nat) (s N : Nat) : Prop := ∀ t<N, ∃ u∈C,Agree (s+1) u t

private theorem pool_pos (C : List Nat) {j t u : Nat} (hu : u∈C) (h : Agree j u t) : 0<pool C j t := by
  classical
  have hm : u∈C.filter (fun v=>decide (Agree j v t)) := List.mem_filter.mpr ⟨hu,by simp [h]⟩
  exact List.length_pos_of_mem hm

private theorem prod_one (l : List Nat) : prod (fun _=>1) l=1 := by
  induction l with | nil => rfl | cons a l ih => simp [prod,ih]

private theorem prod_constant (l : List Nat) (v : Nat) : prod (fun _=>v) l=v^l.length := by
  induction l with | nil => rfl | cons a l ih => simp [prod,ih,Nat.pow_succ,Nat.mul_comm]

/-- Transport all levels of one terminal width against any horizontal row cover. -/
theorem single_width_budget {s N : Nat} (c : Census s N) (C : List Nat) (covers : Covers C s N) :
    4^(pairSum c.pairs s) ≤ C.length^N := by
  have sweep : ∀ r, r≤s → 4^(pairSum c.pairs r)*ledger C N (s+1) ≤ ledger C N (s+1-r) := by
    intro r
    induction r with
    | zero => simp [pairSum]
    | succ r ih =>
      intro hr
      have h := Nat.mul_le_mul_left (4^(c.pairs r).length) (ih (by omega))
      have level := one_level c C (r:=r) (by omega)
      rw [show s-r+1=s+1-r by omega] at level
      rw [pairSum,Nat.pow_add,show s+1-(r+1)=s-r by omega]
      exact Nat.le_trans (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h) level
  have init : 1≤ledger C N (s+1) := by
    rw [ledger,←prod_one (List.range N)]
    apply prod_mono
    intro t ht
    obtain ⟨u,hu,ha⟩ := covers t (List.mem_range.mp ht)
    exact pool_pos C hu (by simpa [prod_one] using ha)
  have last : ledger C N 1≤C.length^N := by
    have z := prod_mono (f:=pool C 1) (g:=fun _=>C.length) (List.range N)
      (fun _ _=>List.length_filter_le _ _)
    simpa [ledger,prod_constant] using z
  have main := sweep s (Nat.le_refl _)
  rw [show s+1-s=1 by omega] at main
  exact Nat.le_trans (by simpa using Nat.mul_le_mul_left (4^(pairSum c.pairs s)) init) (Nat.le_trans main last)


/-- Three disjoint pairs per twenty age-depth positions force ten powers of the vocabulary
to dominate eight to the terminal width. -/
theorem single_width_tenth {s N : Nat} (c : Census s N) (C : List Nat) (covers : Covers C s N)
    (hn : 0 < N) (many : 3 * (s*N) ≤ 20 * pairSum c.pairs s) : 8^s ≤ C.length^10 := by
  let M := pairSum c.pairs s
  have budget : 4^M ≤ C.length^N := single_width_budget c C covers
  have raised : (8^s)^N ≤ (C.length^10)^N := by
    calc
      _ = 2^(3*(s*N)) := by rw [show (8:Nat)=2^3 by decide, ←Nat.pow_mul, ←Nat.pow_mul]
      _ ≤ 2^(20*M) := Nat.pow_le_pow_right (by decide) many
      _ = (4^M)^10 := by
        rw [show (4:Nat)=2^2 by decide, ←Nat.pow_mul, ←Nat.pow_mul]
        congr 1; omega
      _ ≤ (C.length^N)^10 := Nat.pow_le_pow_left budget 10
      _ = _ := Nat.pow_right_comm ..
  exact Nat.le_of_not_lt (fun h => Nat.not_lt_of_ge raised (Nat.pow_lt_pow_left h (by omega)))

/-- At arbitrarily large widths a suitable finite horizon admits the stated mean pair rate. -/
def Abundant : Prop := ∀ K : Nat, ∃ s ≥ K, ∃ N > 0, ∃ c : Census s N,
  3 * (s*N) ≤ 20 * pairSum c.pairs s

private theorem rate_gap (b k : Nat) : (k+b)*b^k ≤ b*(b+1)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have step : b*(k+1+b) ≤ (b+1)*(k+b) := by
      rw [show k+1+b=(k+b)+1 by omega, Nat.mul_add, Nat.add_mul]
      simp
    calc
      _ = (b*(k+1+b))*b^k := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ ((b+1)*(k+b))*b^k := Nat.mul_le_mul_right _ step
      _ = (b+1)*((k+b)*b^k) := Nat.mul_assoc ..
      _ ≤ (b+1)*(b*(b+1)^k) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [Nat.pow_succ]; ac_rfl

/-- The rate beats the five-cell bound since 8·32¹⁰ > 39¹⁰. -/
theorem single_width_growth (abundant : Abundant) (A : Nat) :
    ∃ s N, 0 < N ∧ ∀ C : List Nat, Covers C s N → A*39^s < C.length*32^s := by
  let b : Nat := 39^10
  obtain ⟨s,hs,N,hn,c,hm⟩ := abundant (b*A^10+1)
  refine ⟨s,N,hn,?_⟩
  intro C covers
  have large := single_width_tenth c C covers hn hm
  apply Nat.lt_of_not_ge
  intro low
  have cap : (b+1)^s ≤ A^10*b^s := by
    calc
      _ ≤ (8*32^10)^s := Nat.pow_le_pow_left (by decide : b+1 ≤ 8*32^10) _
      _ = 8^s*(32^s)^10 := by rw [Nat.mul_pow,Nat.pow_right_comm 32 10 s]
      _ ≤ C.length^10*(32^s)^10 := Nat.mul_le_mul_right _ large
      _ = (C.length*32^s)^10 := (Nat.mul_pow ..).symm
      _ ≤ (A*39^s)^10 := Nat.pow_le_pow_left low 10
      _ = _ := by rw [Nat.mul_pow,Nat.pow_right_comm 39 s 10]
  have bound := Nat.le_trans (rate_gap b s) (Nat.mul_le_mul_left b cap)
  rw [←Nat.mul_assoc] at bound
  have pos : 0 < b^s := Nat.pow_pos (by decide)
  exact (Nat.not_lt_of_ge bound) (Nat.mul_lt_mul_of_pos_right (by omega) pos)

open Rule30HorizontalDiversity

private noncomputable def ageOf (s : Nat) (v : List Bool) : Nat := by
  classical exact if h : ∃ t, row s t=v then Classical.choose h else 0

private theorem covered_language (s N : Nat) : Rule30TerminalCensus.Covers ((language s).map (ageOf s)) s N := by
  classical
  intro t _
  have exist : ∃ u, row s u=row s t := ⟨t,rfl⟩
  have eq : row s (ageOf s (row s t))=row s t := by
    simpa only [ageOf,dite_eq_left exist] using Classical.choose_spec exist
  refine ⟨ageOf s (row s t),List.mem_map.mpr ⟨row s t,mem_language.mpr ⟨t,rfl⟩,rfl⟩,?_⟩
  intro i hi
  exact List.map_inj_left.mp eq i (List.mem_range.mpr hi)

/-- All depth-specific pairings from a single terminal spatial width give an exact product budget. -/
theorem vocabulary_budget {s N : Nat} (c : Census s N) :
    4^(pairSum c.pairs s) ≤ (H s)^N := by
  simpa [H] using Rule30TerminalCensus.single_width_budget c _ (covered_language s N)


/-- The singleton vocabulary at one width given a mean pair rate of at least 3/20. -/
theorem vocabulary_tenth {s N : Nat} (c : Census s N) (hn : 0 < N)
    (many : 3 * (s*N) ≤ 20 * pairSum c.pairs s) : 8^s ≤ (H s)^10 := by
  simpa [H] using single_width_tenth c _ (covered_language s N) hn many

/-- The mean pair bound at unbounded widths excludes eventual periodicity of the center. -/
theorem single_width_problem1 (test : Abundant) : Rule30Prize.Problem1 := by
  apply problem1_of_five_cell_growth
  intro A
  obtain ⟨s,N,_,gain⟩ := single_width_growth test A
  refine ⟨s,?_⟩
  simpa [H] using gain _ (covered_language s N)

end Ruliology.CellularAutomata.Rule30TerminalCensus
