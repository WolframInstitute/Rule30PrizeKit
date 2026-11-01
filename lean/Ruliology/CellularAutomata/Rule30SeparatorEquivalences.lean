module

public import Ruliology.CellularAutomata.Rule30SeparatorBridge

/-!
# The orbit separator and the constant-tail separator are equivalent

`separator_equivalence`: `OrbitSeparator ↔ ConstantTailSeparator`, by normalizing the symbol `3` to `1`
in the label word (`normalizeSym`, `lift_normalize_label`) and factoring a stack of lifts
(`stack_factorization`). Consequences: `separator_excludes_zero_cut` and
`separator_excludes_finite_peel_rank` exclude a zero cut and a finite peel rank for hard-core streams
from `ConstantTailSeparator`. The full reversed dependency frontier is retained in the label word.
Neither separator is proved here. For how the separators relate to `Rule30PeriodTwo.Q01` and to mortality of the auxiliary frontier
(`Rule30AlternatingTraceBridge.Mortality`), see `Rule30SEPToPeriodTwo`: no implication is proved in
either direction.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30SeparatorEquivalences

open Rule30WedgeBridge Rule30SeparatorBridge


def normalizeSym (a : Sym) : Sym := if a=3 then 1 else a
def normalizeHead (v : Stream) : Stream
  | 0 => normalizeSym (v 0)
  | i+1 => v (i+1)

theorem unphi_normalize : ∀ a b : Sym, unphi (normalizeSym a) b=unphi a b := by decide
theorem normalize_valid : ∀ a : Sym, (normalizeSym a).val≤2 := by decide

theorem lift_normalize_input (a : Sym) (v : Stream) :
    lift a (normalizeHead v)=lift a v := by
  funext i
  induction i with
  | zero => rfl
  | succ i ih => simp only [lift, normalizeHead, ih]

theorem unphi_normalize_head (v : Stream) (i : Nat) (b : Sym) :
    unphi (normalizeHead v i) b=unphi (v i) b := by
  cases i with
  | zero => exact unphi_normalize (v 0) b
  | succ i => rfl

theorem lift_normalize_label (a : Sym) (v : Stream) :
    lift (normalizeSym a) v=normalizeHead (lift a v) := by
  funext i
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [lift, normalizeHead]
    rw [ih, unphi_normalize_head]

theorem word_normalize_input (u : List Sym) (h : u≠[]) (v : Stream) :
    liftWord u (normalizeHead v)=liftWord u v := by
  cases u with
  | nil => contradiction
  | cons a u => simp only [liftWord, lift_normalize_input]

theorem word_normalize_labels (u : List Sym) (h : u≠[]) (v : Stream) :
    liftWord (u.map normalizeSym) v=normalizeHead (liftWord u v) := by
  induction u generalizing v with
  | nil => contradiction
  | cons a u ih =>
    by_cases hu : u=[]
    · subst u
      exact lift_normalize_label a v
    · simp only [List.map_cons, liftWord]
      rw [ih hu, lift_normalize_label, word_normalize_input u hu]

theorem hc_normalize_inverse (e : Stream) (hh : HardCore e) :
    normalizeHead (inverse e)=inverse e := by
  funext t
  cases t with
  | zero =>
    rcases hh.1 0 with h | h <;>
      simp [normalizeHead, inverse, cone, h, boundary, normalizeSym]
  | succ t => rfl

theorem orbit_separator_full_labels (hs : OrbitSeparator) (c : Sym)
    (hc : constantTail c) (u : List Sym) (e : Stream) (hh : HardCore e) :
    liftWord u (fun _=>c) ≠ inverse e := by
  intro h
  have hn : liftWord (u.map normalizeSym) (fun _=>c)=inverse e := by
    by_cases hu : u=[]
    · subst u
      exact h
    · rw [word_normalize_labels u hu, h, hc_normalize_inverse e hh]
  apply hs c hc (u.map normalizeSym) ?_ e hh hn
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact normalize_valid b

theorem lift_unique (a : Sym) (v x : Stream) (h0 : x 0=a)
    (hp : peel x=shift v) : x=lift a v := by
  funext t
  induction t with
  | zero => exact h0
  | succ t ih =>
    have h := congrFun hp t
    change phi (x t) (x (t+1))=v (t+1) at h
    rw [lift, ← ih, ← h, unphi_phi]

theorem cone_shiftN (e : Stream) (k t j : Nat) :
    cone (shiftN e k) t j=cone e t (j+k) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    rw [shiftN_succ, cone_shift, ih]
    congr 1 <;> omega

/-- The full reversed dependency frontier is retained in the label word. -/
theorem stack_factorization (e : Stream) (n j : Nat) :
    ∃ u : List Sym, u.length=n ∧
      liftWord u (fun t=>cone e (t+n) j)=(fun t=>cone e t (j+n)) := by
  induction n generalizing j with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ n ih =>
    let v : Stream := fun t=>cone e (t+(n+1)) j
    let w : Stream := fun t=>cone e (t+n) (j+1)
    let a := cone e n (j+1)
    have hw : w=lift a v := by
      apply lift_unique a v w (by simp [w,a])
      funext t
      change phi (cone e (t+n) (j+1)) (cone e (t+1+n) (j+1)) =
        cone e (t+1+(n+1)) j
      have hi : t+1+(n+1)=(t+n)+2 := by omega
      have hj : t+1+n=(t+n)+1 := by omega
      rw [hi,hj,cone]
    obtain ⟨u,hu,hf⟩ := ih (j+1)
    refine ⟨a::u, by simp [hu], ?_⟩
    change liftWord u (lift a v)=(fun t=>cone e t (j+(n+1)))
    rw [← hw]
    change liftWord u (fun t=>cone e (t+n) (j+1))=_
    rw [hf]
    funext t
    congr 1 <;> omega

theorem orbit_separator_implies_constant_separator (hs : OrbitSeparator) :
    ConstantTailSeparator := by
  intro c hc e hh ⟨N,he⟩
  obtain ⟨u,_,hu⟩ := stack_factorization e N 0
  have hstart : (fun t=>cone e (t+N) 0)=(fun _=>c) := by
    funext t
    exact he (t+N) (by omega)
  have hend : (fun t=>cone e t (0+N))=inverse (shiftN e N) := by
    funext t
    exact (cone_shiftN e N t 0).symm
  rw [hstart,hend] at hu
  exact orbit_separator_full_labels hs c hc u (shiftN e N) (hc_shift e N hh) hu

theorem separator_equivalence : OrbitSeparator ↔ ConstantTailSeparator := by
  constructor
  · exact orbit_separator_implies_constant_separator
  · intro h c hc u _ e hh
    exact constant_separator_implies_full_orbit_separator h c hc u e hh

theorem zero_lift_fixed : ∀ a : Sym, unphi (unphi a 0) 0=unphi a 0 := by decide
theorem zero_lift_values : ∀ a : Sym, unphi a 0=0 ∨ constantTail (unphi a 0) := by
  unfold constantTail
  decide
theorem phi_right_zero : ∀ a : Sym, phi a 0=0 → a=0 := by decide

theorem peel_zero_classification (x : Stream) (K : Nat)
    (h : ∀ t, K≤t → peel x t=0) :
    ∃ a, (a=0 ∨ constantTail a) ∧ ∀ t, K+1≤t → x t=a := by
  have nextZero (t : Nat) (ht : K≤t) : x (t+1)=unphi (x t) 0 := by
    calc
      x (t+1)=unphi (x t) (peel x t) := (unphi_phi _ _).symm
      _ = unphi (x t) 0 := by rw [h t ht]
  let a := unphi (x K) 0
  have tail (n : Nat) : x (K+1+n)=a := by
    induction n with
    | zero => exact nextZero K (by omega)
    | succ n ih =>
      have hi : K+1+(n+1)=(K+1+n)+1 := by omega
      rw [hi,nextZero (K+1+n) (by omega),ih]
      exact zero_lift_fixed (x K)
  refine ⟨a,zero_lift_values (x K),?_⟩
  intro t ht
  have heq : K+1+(t-(K+1))=t := by omega
  simpa only [heq] using tail (t-(K+1))

theorem separator_peel_zero (hs : ConstantTailSeparator) (e : Stream)
    (hh : HardCore e) (K : Nat) (hp : ∀ t, K≤t → peel (inverse e) t=0) :
    ∀ t, K≤t → inverse e t=0 := by
  obtain ⟨a,ha,he⟩ := peel_zero_classification (inverse e) K hp
  rcases ha with h0 | hc
  · subst a
    intro t ht
    by_cases hkt : t=K
    · subst t
      have h := hp K (by omega)
      change phi (inverse e K) (inverse e (K+1))=0 at h
      rw [he (K+1) (by omega)] at h
      exact phi_right_zero _ h
    · exact he t (by omega)
  · exact False.elim (hs a hc e hh ⟨K+1,he⟩)

/-- No least-infinite-index assumption is needed: the cutoff decreases. -/
theorem separator_excludes_zero_cut (hs : ConstantTailSeparator) :
    ∀ K e, HardCore e → (∀ t, K≤t → inverse e t=0) → False := by
  intro K
  induction K using Nat.strongRecOn with
  | ind K ih =>
    intro e hh hz
    by_cases hK : K=0
    · subst K
      have h := hz 0 (by omega)
      rcases hh.1 0 with he | he <;> simp [inverse,cone,he,boundary] at h
    · have hn : K-2<K := by omega
      apply ih (K-2) hn (shiftN e 1) (hc_shift e 1 hh)
      apply separator_peel_zero hs (shiftN e 1) (hc_shift e 1 hh) (K-2)
      intro t ht
      have hs1 : shiftN e 1=shift e := rfl
      rw [hs1,rotated_peel]
      exact hz (t+2) (by omega)

theorem separator_excludes_finite_peel_rank (hs : ConstantTailSeparator)
    (e : Stream) (hh : HardCore e) (d K : Nat)
    (hz : ∀ t, K≤t → peelPow d (inverse e) t=0) : False := by
  apply separator_excludes_zero_cut hs (K+2*d) (prependTwos e d) (hc_prepend e d hh)
  intro t ht
  have hi := rotated_iterate (prependTwos e d) d (t-2*d)
  rw [shift_prepend] at hi
  have hindex : t-2*d+2*d=t := by omega
  rw [hindex] at hi
  change peelPow d (inverse e) (t-2*d)=_ at hi
  rw [hz (t-2*d) (by omega)] at hi
  exact hi.symm


end Rule30SeparatorEquivalences
end Ruliology.CellularAutomata
