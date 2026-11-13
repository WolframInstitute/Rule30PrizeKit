module
public import Ruliology.CellularAutomata.Rule30ControlledResponse
public import Ruliology.CellularAutomata.Rule30FiniteDiagonals
public import Ruliology.CellularAutomata.Rule30FrozenRuler

/-!
# Finite ancestry is invariant under controlled-response aliases

Two finite nonzero full rows with the same entire center trace have identical
finite ancestry depths if their right tails, INCLUDING the center, have the same
universal controlled response. It suffices that the response classes agree after
any finite number of actual evolution steps (`finite_feedback_ancestry`).

The constructive step transports a finite predecessor across a coupled pair and
moves the comparison cut from q to q-1. Finite diagonal registers return by the
existing right-diagonal clocks; this permits pulling response equivalence backward.
The head and head/next OR observations validate the seam of the spliced predecessor.

The center trace alone is NOT shown to determine or bound ancestry. No completeness
of controlled aliases, eventual response coalescence, or prize result is claimed.
All ancestry depths and support widths in the theorems are unrestricted.

The helper `one_injective` is a core-Lean specialization of the known
right-asymptotic injectivity also formalized in `Rule30Equivalents.Preimages`;
no novelty is claimed for that helper or the finite diagonal clocks.

Troy Lowry, with OpenAI Codex, November 2026.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResponseAncestry
open Rule30Jen Rule30Realization Rule30ControlledResponse
open Rule30FiniteDiagonals Rule30FiniteConfigs Rule30PeriodTwoSideways Rule30FrozenRuler

abbrev Row := Int → Bool
def FiniteEdges (x : Row) (lo hi : Int) : Prop :=
  x lo=true ∧ x hi=true ∧ (∀ p,p<lo → x p=false) ∧ ∀ p,hi<p → x p=false

/-- An actual nonzero finite full-row ancestor, with both spatial edges retained. -/
def HasAncestor (x : Row) (n : Nat) : Prop :=
  ∃ z lo hi,FiniteEdges z lo hi ∧ ∀ p,evol z n p=x p

theorem left_white (x : Row) (lo : Int) (zero : ∀ p,p<lo → x p=false) :
    ∀ (t : Nat) (p : Int),p<lo-(t:Int) → evol x t p=false
  | 0,p,h => zero p (by omega)
  | t+1,p,h => by
    change rule (evol x t (p-1)) (evol x t p) (evol x t (p+1))=false
    rw [left_white x lo zero t (p-1) (by omega),left_white x lo zero t p (by omega),
      left_white x lo zero t (p+1) (by omega)]
    rfl

theorem left_black (x : Row) (lo : Int) (black : x lo=true)
    (zero : ∀ p,p<lo → x p=false) : ∀ t,evol x t (lo-(t:Int))=true
  | 0 => by simpa [evol] using black
  | t+1 => by
    change rule (evol x t (lo-((t+1:Nat):Int)-1))
      (evol x t (lo-((t+1:Nat):Int))) (evol x t (lo-((t+1:Nat):Int)+1))=true
    rw [left_white x lo zero t _ (by omega),left_white x lo zero t _ (by omega),
      show lo-((t+1:Nat):Int)+1=lo-(t:Int) by omega,left_black x lo black zero t]
    rfl

def SameTrace (x y : Row) : Prop := ∀ t,evol x t 0=evol y t 0

theorem restart (x : Row) (a : Nat) : ∀ t p,evol (evol x a) t p=evol x (a+t) p
  | 0,p => rfl
  | t+1,p => by
    change rule (evol (evol x a) t (p-1)) (evol (evol x a) t p)
      (evol (evol x a) t (p+1)) =
      rule (evol x (a+t) (p-1)) (evol x (a+t) p) (evol x (a+t) (p+1))
    rw [restart x a t (p-1),restart x a t p,restart x a t (p+1)]

theorem edges_evol {x : Row} {lo hi : Int} (h : FiniteEdges x lo hi) (t : Nat) :
    FiniteEdges (evol x t) (lo-(t:Int)) (hi+(t:Int)) := by
  have r := edge_evol x hi h.2.1 h.2.2.2 t
  exact ⟨left_black x lo h.1 h.2.2.1 t,r.1,
    fun p hp => left_white x lo h.2.2.1 t p hp,r.2.1⟩

def FiniteState (x : State) : Prop := ∃ W,∀ k,W≤k → x k=false
def tailAt (x : Int → Bool) (p : Int) : State := fun k => x (p+(k:Int))
def embed (x : State) (p : Int) : Bool := if 0≤p then x p.toNat else false

theorem tail_embed (x : State) : tailAt (embed x) 0=x := by
  funext k
  simp [tailAt,embed]

theorem iterate_add (x : State) (a b : Nat) :
    iterate x (a+b)=iterate (iterate x a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change diagonal (iterate x (a+b))=diagonal (iterate (iterate x a) b)
    rw [ih]

theorem iter_tail (x : Int → Bool) (p : Int) : ∀ t k,
    iterate (tailAt x p) t k=evol x t (p+(t:Int)+(k:Int))
  | 0,k => by simp [iterate,tailAt,evol]
  | t+1,k => by
    change xor (iterate (tailAt x p) t k)
      (iterate (tailAt x p) t (k+1) || iterate (tailAt x p) t (k+2)) =
      rule (evol x t (p+((t+1:Nat):Int)+(k:Int)-1))
        (evol x t (p+((t+1:Nat):Int)+(k:Int)))
        (evol x t (p+((t+1:Nat):Int)+(k:Int)+1))
    rw [iter_tail x p t k,iter_tail x p t (k+1),iter_tail x p t (k+2)]
    rw [show p+((t+1:Nat):Int)+(k:Int)-1=p+(t:Int)+(k:Int) by omega,
      show p+((t+1:Nat):Int)+(k:Int)=p+(t:Int)+((k+1:Nat):Int) by omega,
      show p+(t:Int)+((k+1:Nat):Int)+1=p+(t:Int)+((k+2:Nat):Int) by omega]
    rfl

theorem iter_zero {x : State} {W : Nat} (h : ∀ k,W≤k → x k=false) :
    ∀ t k,W≤k → iterate x t k=false
  | 0,k,hk => h k hk
  | t+1,k,hk => by
    change xor (iterate x t k) (iterate x t (k+1) || iterate x t (k+2))=false
    rw [iter_zero h t k hk,iter_zero h t (k+1) (by omega),iter_zero h t (k+2) (by omega)]
    rfl

theorem iter_finite {x : State} (h : FiniteState x) (t : Nat) : FiniteState (iterate x t) := by
  obtain ⟨W,hW⟩ := h
  exact ⟨W,iter_zero hW t⟩

/-- The finite diagonal register returns. This is a specialization of the
public right-diagonal clocks, not a new clock-growth theorem. -/
theorem finite_return (x : State) (W : Nat) (h : ∀ k,W≤k → x k=false) :
    iterate x (2^W)=x := by
  have right : ∀ p,(W:Int)<p → embed x p=false := by
    intro p hp
    simp only [embed,ite_eq_left (show 0≤p by omega)]
    exact h p.toNat (by omega)
  funext k
  by_cases hk : k<W
  · have clock := Rd_periodic_mul (hi:=(W:Int)) right (W-k) (2^k) 0
    have power : 2^k*2^(W-k)=2^W := by
      rw [←Nat.pow_add,show k+(W-k)=W by omega]
    rw [Nat.zero_add,power] at clock
    have dynamic := iter_tail (embed x) 0 (2^W) k
    rw [tail_embed] at dynamic
    rw [dynamic]
    unfold Rd at clock
    have loc : (W:Int)+((2^W:Nat):Int)-((W-k:Nat):Int)=0+((2^W:Nat):Int)+(k:Int) := by omega
    have loc0 : (W:Int)+(0:Nat)-((W-k:Nat):Int)=(k:Int) := by omega
    rw [loc,loc0] at clock
    simpa [evol,embed] using clock
  · rw [iter_zero h _ k (by omega),h k (by omega)]

theorem return_many {x : State} {P : Nat} (h : iterate x P=x) :
    ∀ m,iterate x (P*m)=x
  | 0 => rfl
  | m+1 => by
    rw [Nat.mul_succ,iterate_add,return_many h m,h]

theorem response_iterate {x y : State} (h : SameResponse x y) :
    ∀ t,SameResponse (iterate x t) (iterate y t)
  | 0 => h
  | t+1 => sameResponse_shift (response_iterate h t)

/-- On finite registers, universal-response equivalence also runs backward
under the diagonal map. The finite-word assumption is essential to this proof. -/
theorem response_backward {x y : State} (fx : FiniteState x) (fy : FiniteState y)
    (n : Nat) (h : SameResponse (iterate x n) (iterate y n)) : SameResponse x y := by
  obtain ⟨Wx,hx⟩ := fx
  obtain ⟨Wy,hy⟩ := fy
  let W := max Wx Wy
  let P := 2^W*(n+1)
  have hp : n≤P := by
    have hh := Nat.mul_le_mul_right (n+1) (Nat.one_le_two_pow (n:=W))
    dsimp [P];omega
  have rx : iterate x P=x := return_many (finite_return x W (fun k hk => hx k (by dsimp [W] at hk;omega))) (n+1)
  have ry : iterate y P=y := return_many (finite_return y W (fun k hk => hy k (by dsimp [W] at hk;omega))) (n+1)
  have hh := response_iterate h (P-n)
  rw [←iterate_add,←iterate_add,show n+(P-n)=P by omega,rx,ry] at hh
  exact hh

theorem finite_previous {x : State} (fx : FiniteState x) :
    ∃ y,FiniteState y ∧ diagonal y=x := by
  obtain ⟨W,hW⟩ := fx
  refine ⟨iterate x (2^W-1),iter_finite ⟨W,hW⟩ _,?_⟩
  change iterate x (2^W-1+1)=x
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow),finite_return x W hW]

theorem tail_finite {x : Int → Bool} {hi : Int}
    (h : ∀ p,hi<p → x p=false) (p : Int) : FiniteState (tailAt x p) := by
  refine ⟨(hi-p).toNat+1,?_⟩
  intro k hk
  exact h _ (by omega)

/-- Includes the observed center. The external driver is column -1. -/
def centerTail (x : Row) : State := fun k => x (k:Int)

theorem tail_next (x : Row) (t : Nat) :
    centerTail (evol x (t+1))=step (evol x t (-1)) (centerTail (evol x t)) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    simp [centerTail,evol,step,prepend,diagonal,rule,Int.natCast_add]
    congr 1 <;> omega

theorem left_from_pair {x y : Row} (p : Int)
    (h0 : ∀ t,evol x t p=evol y t p)
    (h1 : ∀ t,evol x t (p+1)=evol y t (p+1)) :
    ∀ t,evol x t (p-1)=evol y t (p-1) := by
  intro t
  have hx := rule_left (evol x t (p-1)) (evol x t p) (evol x t (p+1))
  have hy := rule_left (evol y t (p-1)) (evol y t p) (evol y t (p+1))
  change evol x t (p-1)=xor (evol x (t+1) p) (evol x t p || evol x t (p+1)) at hx
  change evol y t (p-1)=xor (evol y (t+1) p) (evol y t p || evol y t (p+1)) at hy
  rw [hx,hy,h0 (t+1),h0 t,h1 t]

/-- A whole center trace and a universal response class jointly determine
the actual driver, despite not assuming it in advance. -/
theorem driver_and_response {x y : Row} (trace : SameTrace x y)
    (responses : SameResponse (centerTail x) (centerTail y)) :
    ∀ t,SameResponse (centerTail (evol x t)) (centerTail (evol y t)) ∧
      evol x t (-1)=evol y t (-1) := by
  have getDriver : ∀ t,SameResponse (centerTail (evol x t)) (centerTail (evol y t)) →
      evol x t (-1)=evol y t (-1) := by
    intro t h
    have o := (sameResponse_observe h).2
    change (evol x t 0 || evol x t 1)=(evol y t 0 || evol y t 1) at o
    have hx := rule_left (evol x t (-1)) (evol x t 0) (evol x t 1)
    have hy := rule_left (evol y t (-1)) (evol y t 0) (evol y t 1)
    change evol x t (-1)=xor (evol x (t+1) 0) (evol x t 0 || evol x t 1) at hx
    change evol y t (-1)=xor (evol y (t+1) 0) (evol y t 0 || evol y t 1) at hy
    rw [hx,hy,trace (t+1),o]
  intro t
  induction t with
  | zero => exact ⟨responses,getDriver 0 responses⟩
  | succ t ih =>
    have h : SameResponse (centerTail (evol x (t+1))) (centerTail (evol y (t+1))) := by
      rw [tail_next,tail_next,ih.2]
      exact sameResponse_step ih.1 _
    exact ⟨h,getDriver (t+1) h⟩

/-- No initial common-left assumption is needed once both the whole center
trace and the center-including universal-response class are supplied. -/
theorem same_left_history {x y : Row} (trace : SameTrace x y)
    (responses : SameResponse (centerTail x) (centerTail y)) :
    ∀ t p,p≤0 → evol x t p=evol y t p := by
  have pair : ∀ n : Nat,
      (∀ t,evol x t (-(n:Int)-1)=evol y t (-(n:Int)-1)) ∧
      (∀ t,evol x t (-(n:Int))=evol y t (-(n:Int))) := by
    intro n
    induction n with
    | zero => exact ⟨fun t => (driver_and_response trace responses t).2,trace⟩
    | succ n ih =>
      have next := left_from_pair (-(n:Int)-1) ih.1
        (by intro t;simpa using ih.2 t)
      constructor
      · intro t
        rw [show -((n+1:Nat):Int)-1=-(n:Int)-1-1 by omega]
        exact next t
      · intro t
        rw [show -((n+1:Nat):Int)=-(n:Int)-1 by omega]
        exact ih.1 t
  intro t p hp
  have h := (pair (-p).toNat).2 t
  have loc : -(((-p).toNat:Int))=p := by omega
  simpa only [loc] using h

/-- Common left part and universal responses of the tail beginning at q. -/
def CoupledAt (q : Int) (x y : Row) : Prop :=
  (∀ p,p<q → x p=y p) ∧ SameResponse (tailAt x q) (tailAt y q)

theorem edges_finite {x : Row} {lo hi : Int} (e : FiniteEdges x lo hi) : FinConfig x := by
  refine ⟨lo.natAbs+hi.natAbs,?_⟩
  intro p hp
  by_cases l : p<lo
  · exact e.2.2.1 p l
  · exact e.2.2.2 p (by omega)

theorem finite_edges {x : Row} (f : FinConfig x) (ne : ∃ p,x p=true) :
    ∃ lo hi,FiniteEdges x lo hi := by
  obtain ⟨lo,black,left⟩ := exists_leftmost f ne
  have fr : FinConfig (fun p => x (-p)) := by
    obtain ⟨W,hW⟩ := f
    exact ⟨W,fun p hp => hW (-p) (by simpa using hp)⟩
  have nr : ∃ p,x (-p)=true := by
    obtain ⟨p,hp⟩ := ne
    exact ⟨-p,by simpa using hp⟩
  obtain ⟨r,br,hr⟩ := exists_leftmost fr nr
  refine ⟨lo,-r,black,br,left,?_⟩
  intro p hp
  have h := hr (-p) (by omega)
  simpa using h

theorem tail_image (u x : Row) (q : Int) (h : ∀ p,evol u 1 p=x p) :
    diagonal (tailAt u (q-1))=tailAt x q := by
  funext k
  have ht := iter_tail u (q-1) 1 k
  change diagonal (tailAt u (q-1)) k=evol u 1 (q-1+(1:Nat)+(k:Int)) at ht
  rw [show q-1+(1:Nat)+(k:Int)=q+(k:Int) by omega,h] at ht
  exact ht

/-- A finite predecessor can be transported across a coupled pair. The
comparison cut moves left by one. This does not assume a common driver. -/
theorem predecessor_transport {u x y : Row} {q loU hiU loY hiY : Int}
    (ue : FiniteEdges u loU hiU) (ye : FiniteEdges y loY hiY)
    (parent : ∀ p,evol u 1 p=x p) (coupled : CoupledAt q x y) :
    ∃ v loV hiV,FiniteEdges v loV hiV ∧
      (∀ p,evol v 1 p=y p) ∧ CoupledAt (q-1) u v := by
  obtain ⟨b,fb,hb⟩ := finite_previous (tail_finite ye.2.2.2 q)
  have backward : SameResponse (tailAt u (q-1)) b := by
    apply response_backward (tail_finite ue.2.2.2 (q-1)) fb 1
    change SameResponse (diagonal (tailAt u (q-1))) (diagonal b)
    rw [tail_image u x q parent,hb]
    exact coupled.2
  let v : Row := fun p => if p<q-1 then u p else b (p-(q-1)).toNat
  have vt : tailAt v (q-1)=b := by
    funext k
    simp only [tailAt,v,ite_eq_right (show ¬ q-1+(k:Int)<q-1 by omega)]
    congr 1
    omega
  have common : ∀ p,p≤q-1 → v p=u p := by
    intro p hp
    by_cases lt : p<q-1
    · simp [v,lt]
    · have eq : p=q-1 := by omega
      subst p
      have head := (sameResponse_observe backward).1
      change u (q-1+0)=b 0 at head
      simpa [v] using head.symm
  have fy : ∀ p,evol v 1 p=y p := by
    intro p
    by_cases low : p<q
    · by_cases seam : p=q-1
      · subst p
        have hor := (sameResponse_observe backward).2
        have hor : (u (q-1) || u q)=(b 0 || b 1) := by
          simpa [tailAt,show q-1+1=q by omega] using hor
        have v0 : v (q-1)=b 0 := by simp [v]
        have v1 : v (q-1+1)=b 1 := by
          simp [v,show ¬ q<q-1 by omega,show q-(q-1)=1 by omega]
        change xor (v (q-1-1)) (v (q-1) || v (q-1+1))=y (q-1)
        rw [common _ (by omega),v0,v1,←hor]
        have hp := parent (q-1)
        change xor (u (q-1-1)) (u (q-1) || u (q-1+1))=x (q-1) at hp
        rw [show q-1+1=q by omega] at hp
        rw [hp,coupled.1 _ (by omega)]
      · change rule (v (p-1)) (v p) (v (p+1))=y p
        rw [common _ (by omega),common _ (by omega),common _ (by omega)]
        exact (parent p).trans (coupled.1 p low)
    · let k := (p-q).toNat
      have pk : p=q+(k:Int) := by dsimp [k];omega
      have h := congrFun hb k
      have actual := iter_tail v (q-1) 1 k
      rw [vt] at actual
      change diagonal b k=evol v 1 (q-1+(1:Nat)+(k:Int)) at actual
      rw [show q-1+(1:Nat)+(k:Int)=p by omega] at actual
      rw [actual] at h
      simpa [tailAt,←pk] using h
  have fv : FinConfig v := by
    obtain ⟨W,hW⟩ := edges_finite ue
    obtain ⟨V,hV⟩ := fb
    refine ⟨W+(q-1).natAbs+V+1,?_⟩
    intro p hp
    by_cases lt : p<q-1
    · simp only [v,ite_eq_left lt]
      exact hW p (by omega)
    · simp only [v,ite_eq_right lt]
      exact hV _ (by omega)
  have nv : ∃ p,v p=true := by
    apply Classical.byContradiction
    intro hn
    have zero : ∀ p,v p=false := by
      intro p
      cases h : v p
      · rfl
      · exact (hn ⟨p,h⟩).elim
    have bad := fy hiY
    change rule (v (hiY-1)) (v hiY) (v (hiY+1))=y hiY at bad
    rw [zero,zero,zero,ye.2.1] at bad
    contradiction
  obtain ⟨loV,hiV,ve⟩ := finite_edges fv nv
  refine ⟨v,loV,hiV,ve,fy,?_,?_⟩
  · intro p hp
    exact (common p (by omega)).symm
  · rw [vt]
    exact backward

/-- All finite ancestry depths transport, with the cut moving in the past.
There is no finite bound on n, support size or response period. -/
theorem ancestry_transport : ∀ n {x y : Row} {q loY hiY : Int},
    FiniteEdges y loY hiY → CoupledAt q x y → HasAncestor x n → HasAncestor y n
  | 0,x,y,q,loY,hiY,ye,_,_ => ⟨y,loY,hiY,ye,fun _ => rfl⟩
  | n+1,x,y,q,loY,hiY,ye,coupled,past => by
    obtain ⟨z,lo,hi,ze,hz⟩ := past
    have ue := edges_evol ze n
    have parent : ∀ p,evol (evol z n) 1 p=x p := by
      intro p
      rw [restart]
      exact hz p
    obtain ⟨v,loV,hiV,ve,pv,cv⟩ := predecessor_transport ue ye parent coupled
    have old : HasAncestor (evol z n) n := ⟨z,lo,hi,ze,fun _ => rfl⟩
    obtain ⟨w,loW,hiW,we,hw⟩ := ancestry_transport n ve cv old
    refine ⟨w,loW,hiW,we,?_⟩
    have eq : evol w n=v := funext hw
    intro p
    rw [←restart,eq]
    exact pv p

theorem coupled_ancestry_iff {x y : Row} {q loX hiX loY hiY : Int}
    (xe : FiniteEdges x loX hiX) (ye : FiniteEdges y loY hiY)
    (h : CoupledAt q x y) (n : Nat) : HasAncestor x n ↔ HasAncestor y n := by
  constructor
  · exact ancestry_transport n ye h
  · exact ancestry_transport n xe
      ⟨fun p hp => (h.1 p hp).symm,sameResponse_symm h.2⟩

/-- The infinite trace and CENTER-INCLUDING response class jointly determine
finite ancestry. The center trace alone is still an open problem. -/
theorem trace_response_ancestry_iff {x y : Row} {loX hiX loY hiY : Int}
    (xe : FiniteEdges x loX hiX) (ye : FiniteEdges y loY hiY)
    (trace : SameTrace x y) (response : SameResponse (centerTail x) (centerTail y))
    (n : Nat) : HasAncestor x n ↔ HasAncestor y n := by
  apply coupled_ancestry_iff xe ye (q:=0) ?_ n
  constructor
  · intro p hp
    exact same_left_history trace response 0 p (by omega)
  · have tx : tailAt x 0=centerTail x := by funext k;simp [tailAt,centerTail]
    have ty : tailAt y 0=centerTail y := by funext k;simp [tailAt,centerTail]
    rw [tx,ty]
    exact response

theorem ancestor_forward {x : Row} {n : Nat} (past : HasAncestor x n) (d : Nat) :
    HasAncestor (evol x d) (n+d) := by
  obtain ⟨z,lo,hi,e,h⟩ := past
  refine ⟨z,lo,hi,e,?_⟩
  have eq : evol z n=x := funext h
  intro p
  rw [←restart,eq]

theorem trace_forward {x y : Row} (same : SameTrace x y) (d : Nat) :
    SameTrace (evol x d) (evol y d) := by
  intro t
  rw [restart,restart]
  exact same (d+t)

theorem one_injective {x y : Row} (H : Int)
    (hx : ∀ p,H<p → x p=false) (hy : ∀ p,H<p → y p=false)
    (same : ∀ p,evol x 1 p=evol y 1 p) : x=y := by
  have pair : ∀ n : Nat,x (H-(n:Int))=y (H-(n:Int)) ∧
      x (H-(n:Int)+1)=y (H-(n:Int)+1) := by
    intro n
    induction n with
    | zero =>
      have h := same (H+1)
      change rule (x (H+1-1)) (x (H+1)) (x (H+1+1))=
        rule (y (H+1-1)) (y (H+1)) (y (H+1+1)) at h
      rw [show H+1-1=H by omega,hx (H+1) (by omega),hx (H+1+1) (by omega),
        hy (H+1) (by omega),hy (H+1+1) (by omega)] at h
      refine ⟨?_,?_⟩
      · simpa [rule] using h
      · simpa using (hx (H+1) (by omega)).trans (hy (H+1) (by omega)).symm
    | succ n ih =>
      have h := same (H-(n:Int))
      change rule (x (H-(n:Int)-1)) (x (H-(n:Int))) (x (H-(n:Int)+1))=
        rule (y (H-(n:Int)-1)) (y (H-(n:Int))) (y (H-(n:Int)+1)) at h
      rw [ih.1,ih.2] at h
      have left : x (H-(n:Int)-1)=y (H-(n:Int)-1) := by
        cases a:x (H-(n:Int)-1) <;> cases b:y (H-(n:Int)-1) <;>
          cases c:y (H-(n:Int)) <;> cases d:y (H-(n:Int)+1) <;> simp_all [rule]
      constructor
      · rwa [show H-((n+1:Nat):Int)=H-(n:Int)-1 by omega]
      · rw [show H-((n+1:Nat):Int)+1=H-(n:Int) by omega]
        exact ih.1
  funext p
  by_cases above : H<p
  · rw [hx p above,hy p above]
  · have h := (pair (H-p).toNat).1
    have loc : H-(((H-p).toNat:Int))=p := by omega
    simpa only [loc] using h

theorem evol_injective {x y : Row} {loX hiX loY hiY : Int}
    (xe : FiniteEdges x loX hiX) (ye : FiniteEdges y loY hiY) :
    ∀ t,evol x t=evol y t → x=y
  | 0,h => h
  | t+1,h => by
    have xx := edges_evol xe t
    have yy := edges_evol ye t
    have earlier : evol x t=evol y t := by
      apply one_injective (max hiX hiY+(t:Int))
        (fun p hp => xx.2.2.2 p (by omega)) (fun p hp => yy.2.2.2 p (by omega))
      intro p
      rw [restart,restart]
      exact congrFun h p
    exact evol_injective xe ye t earlier

theorem ancestry_after_iff {x : Row} {lo hi : Int} (xe : FiniteEdges x lo hi)
    (n t : Nat) : HasAncestor (evol x t) (n+t) ↔ HasAncestor x n := by
  constructor
  · rintro ⟨z,loZ,hiZ,ze,hz⟩
    have images : evol (evol z n) t=evol x t := by
      funext p
      rw [restart]
      exact hz p
    have eq := evol_injective (edges_evol ze n) xe t images
    exact ⟨z,loZ,hiZ,ze,fun p => congrFun eq p⟩
  · exact fun past => ancestor_forward past t

/-- The response classes may differ initially. If the actual equal-center
histories enter the same class at any finite time, ancestry is still exact. -/
theorem finite_feedback_ancestry {x y : Row} {loX hiX loY hiY : Int}
    (xe : FiniteEdges x loX hiX) (ye : FiniteEdges y loY hiY)
    (trace : SameTrace x y) (t : Nat)
    (response : SameResponse (centerTail (evol x t)) (centerTail (evol y t)))
    (n : Nat) : HasAncestor x n ↔ HasAncestor y n := by
  rw [←ancestry_after_iff xe n t,←ancestry_after_iff ye n t]
  exact trace_response_ancestry_iff (edges_evol xe t) (edges_evol ye t)
    (trace_forward trace t) response (n+t)


/-! ## Uniqueness of `FiniteEdges` endpoints and uniqueness of finite-edge depth-`n` ancestors -/

/-- **Uniqueness of `FiniteEdges` Endpoints and Uniqueness of Finite-Edge Depth-`n` Ancestors (`finiteEdges_unique_and_ancestor_unique`).** -/
theorem finiteEdges_unique_and_ancestor_unique
    {x z1 z2 : Row} {lo1 hi1 lo2 hi2 : Int} (n : Nat) :
    (FiniteEdges x lo1 hi1 → FiniteEdges x lo2 hi2 → lo1 = lo2 ∧ hi1 = hi2) ∧
    (FiniteEdges z1 lo1 hi1 → FiniteEdges z2 lo2 hi2 →
      (∀ p, evol z1 n p = x p) → (∀ p, evol z2 n p = x p) → z1 = z2) := by
  refine ⟨fun h1 h2 => ⟨?_, ?_⟩, fun hz1 hz2 he1 he2 => ?_⟩
  · rcases Int.lt_trichotomy lo1 lo2 with hlt | rfl | hgt
    · have hf := h2.2.2.1 lo1 hlt; rw [h1.1] at hf; cases hf
    · rfl
    · have hf := h1.2.2.1 lo2 hgt; rw [h2.1] at hf; cases hf
  · rcases Int.lt_trichotomy hi1 hi2 with hlt | rfl | hgt
    · have hf := h1.2.2.2 hi2 hlt; rw [h2.2.1] at hf; cases hf
    · rfl
    · have hf := h2.2.2.2 hi1 hgt; rw [h1.2.1] at hf; cases hf
  · apply evol_injective hz1 hz2 n
    funext p
    exact (he1 p).trans (he2 p).symm

end Ruliology.CellularAutomata.Rule30ResponseAncestry
