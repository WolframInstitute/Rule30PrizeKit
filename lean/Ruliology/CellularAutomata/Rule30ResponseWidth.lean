module
public import Ruliology.CellularAutomata.Rule30ResponseAncestry

/-!
# Exact minimum width of singleton right-response classes

For every age `a`, any finite state universally response equivalent to the
center-INCLUSIVE right tail of `cell a` needs at least `a + 1` cells. The actual
tail attains this bound (`actual_response_width_exact`). Consequently different
singleton ages have different response classes, without assuming equal center
traces or a hypothetical period. They never coalesce at a common future time.

Proof: splice the proposed shorter representative onto the unchanged negative
half of `cell a`. The coupled ancestry theorem transports its depth-`a` finite
ancestor. But two advancing support edges require width at least `2*a`, whereas
the spliced row would have width at most `a + W - 1`. Hence `a < W`.

This strengthens the earlier trace-conditional response separation. It does NOT
separate actual center traces, establish a center-trace ancestry bound, or prove
Problem 1. Finite support alone cannot justify response-class recurrence: the
minimum representation width along the actual singleton orbit grows linearly.
Universal response comparisons allow all boundary inputs; the actual boundary
input is fixed by the left half. That observability gap remains open.

The support-width inequality is standard; the ancestry transport is the existing
`Rule30ResponseAncestry` theorem. No new claim is made for either helper.

Troy Lowry, with OpenAI Codex, November 2026.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResponseWidth
open Ruliology.CellularAutomata Rule30Jen Rule30Realization Rule30ControlledResponse
open Rule30ResponseAncestry Rule30PeriodTwoSideways Rule30Diagonals

theorem ancestry_width {x : Row} {lo hi : Int} (xe : FiniteEdges x lo hi)
    {n : Nat} (past : HasAncestor x n) : 2*(n:Int)≤hi-lo := by
  obtain ⟨z,l,r,ze,hz⟩ := past
  have order : l≤r := by
    apply Classical.byContradiction
    intro hn
    have bad := ze.2.2.2 l (by omega)
    rw [ze.1] at bad
    contradiction
  have e := edges_evol ze n
  have eq : evol z n=x := funext hz
  rw [eq] at e
  have lb : lo≤l-(n:Int) := by
    apply Classical.byContradiction
    intro hn
    have bad := xe.2.2.1 (l-(n:Int)) (by omega)
    rw [e.1] at bad
    contradiction
  have rb : r+(n:Int)≤hi := by
    apply Classical.byContradiction
    intro hn
    have bad := xe.2.2.2 (r+(n:Int)) (by omega)
    rw [e.2.1] at bad
    contradiction
  omega

theorem seed_edges : FiniteEdges seed 0 0 := by
  refine ⟨rfl,rfl,?_,?_⟩ <;> intro p hp <;> simp [seed] <;> omega

theorem cell_ancestor (a : Nat) : HasAncestor (cell a) a :=
  ⟨seed,0,0,seed_edges,evol_seed a⟩

/-- Keep the negative half of the ACTUAL row, replacing only the center-inclusive right tail. -/
def join (a : Nat) (v : State) (p : Int) : Bool :=
  if p<0 then cell a p else v p.toNat

theorem join_tail (a : Nat) (v : State) : tailAt (join a v) 0=v := by
  funext k
  simp [tailAt,join,show ¬ (k:Int)<0 by omega]

theorem join_left_white (a : Nat) (v : State) (p : Int) (hp : p < -(a:Int)) :
    join a v p=false := by
  rw [join,ite_eq_left (by omega)]
  exact cell_eq_false_of_lt a p hp

theorem join_right_white (a W : Nat) (v : State) (bound : ∀ k,W≤k → v k=false)
    (p : Int) (hp : (W:Int)≤p) : join a v p=false := by
  rw [join,ite_eq_right (by omega)]
  exact bound p.toNat (by omega)

/-- A universal-response representative of the actual age-a right tail cannot be shorter.
No assumed period, trace equality, change of observation point or finite scan is used. -/
theorem singleton_response_minimum_width (a W : Nat) (v : State)
    (bound : ∀ k,W≤k → v k=false)
    (response : SameResponse (centerTail (cell a)) v) : a<W := by
  have finite : FinConfig (join a v) := by
    refine ⟨a+W+1,?_⟩
    intro p hp
    by_cases neg : p<0
    · exact join_left_white a v p (by omega)
    · exact join_right_white a W v bound p (by omega)
  have nonzero : ∃ p,join a v p=true := by
    by_cases zero : a=0
    · subst a
      have head := (sameResponse_observe response).1
      have hv : v 0=true := by
        change true=v 0 at head
        exact head.symm
      exact ⟨0,by simpa [join] using hv⟩
    · refine ⟨-(a:Int),?_⟩
      rw [join,ite_eq_left (by omega)]
      exact cell_left_edge a
  obtain ⟨lo,hi,edges⟩ := finite_edges finite nonzero
  have coupled : CoupledAt 0 (cell a) (join a v) := by
    constructor
    · intro p hp; simp [join,hp]
    · rw [join_tail]
      have eq : tailAt (cell a) 0=centerTail (cell a) := by
        funext k
        simp [tailAt,centerTail]
      rw [eq]
      exact response
  have past := ancestry_transport a edges coupled (cell_ancestor a)
  have width := ancestry_width edges past
  have lower : -(a:Int)≤lo := by
    apply Classical.byContradiction
    intro hn
    have bad := join_left_white a v lo (by omega)
    rw [edges.1] at bad
    contradiction
  have upper : hi<(W:Int) := by
    apply Classical.byContradiction
    intro hn
    have bad := join_right_white a W v bound hi (by omega)
    rw [edges.2.1] at bad
    contradiction
  omega

theorem actual_tail_bound (a : Nat) :
    ∀ k,a+1≤k → centerTail (cell a) k=false := by
  intro k hk
  exact cell_eq_false_of_gt a k (by omega)

/-- Every actual age has a different class even WITHOUT comparing center histories. -/
theorem actual_response_age_injective {a b : Nat}
    (response : SameResponse (centerTail (cell a)) (centerTail (cell b))) : a=b := by
  have ab := singleton_response_minimum_width a (b+1) _ (actual_tail_bound b) response
  have ba := singleton_response_minimum_width b (a+1) _ (actual_tail_bound a)
    (sameResponse_symm response)
  omega

/-- Different actual ages never coalesce at a common future time. -/
theorem actual_response_never_coalesces {a b : Nat} (ne : a≠b) (t : Nat) :
    ¬ SameResponse (centerTail (cell (a+t))) (centerTail (cell (b+t))) := by
  intro response
  have h := actual_response_age_injective response
  exact ne (by omega)

/-- The exact minimum representation width grows as a+t+1 along the actual history. -/
theorem actual_response_width_exact (a t W : Nat) :
    (∃ v : State,(∀ k,W≤k → v k=false) ∧
      SameResponse (centerTail (cell (a+t))) v) ↔ a+t<W := by
  constructor
  · rintro ⟨v,bound,response⟩
    exact singleton_response_minimum_width (a+t) W v bound response
  · intro h
    refine ⟨centerTail (cell (a+t)),?_,?_⟩
    · intro k hk
      exact actual_tail_bound (a+t) k (by omega)
    · intro n
      exact (responseEq_iff_runs n _ _).mpr (by intro c t ht; rfl)

/-! ## Exact age equivalence `SameResponse (centerTail (cell a)) (centerTail (cell b)) ↔ a = b` and no periodic response return -/

/-- **Exact Age Equivalence for `centerTail` Responses and Absence of Positive-Period Returns (`sameResponse_centerTail_iff_eq_and_no_pos_period`).** -/
theorem sameResponse_centerTail_iff_eq_and_no_pos_period (a b t P : Nat) :
    (SameResponse (centerTail (cell a)) (centerTail (cell b)) ↔ a = b) ∧
    (0 < P → ¬ SameResponse (centerTail (cell (t + P))) (centerTail (cell t))) := by
  refine ⟨⟨actual_response_age_injective, ?_⟩, fun hP hresp => ?_⟩
  · rintro rfl
    exact sameResponse_refl (centerTail (cell a))
  · have heq := actual_response_age_injective hresp
    omega

end Ruliology.CellularAutomata.Rule30ResponseWidth
