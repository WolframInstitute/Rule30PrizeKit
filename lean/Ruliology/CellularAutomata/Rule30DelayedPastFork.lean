module

public import Ruliology.CellularAutomata.Rule30FiniteWhiteRuns
public import Ruliology.CellularAutomata.Rule30LateObservation

/-!
# Periodic-center past forks with one black cell on the initial right

For every first observation age M and auxiliary clock Q>0, a single actual
Rule 30 orbit has a nonconstant periodic center from time zero and opposite
right readings at two white times separated by Q whole periods. Its masked
right readings agree forever starting one tick later, as do its entire left
halves. The initial right half contains just one black cell. The initial
left half has no leftmost black cell. The center clock varies with M.

The construction uses the kit's center realization and its eight-white
period lock for a white run followed by two black ticks. It tests which
origin hypotheses a past reader for the singleton needs.

Contributed by Troy Lowry with OpenAI Codex.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DelayedPastFork

open Rule30Realization Rule30FiniteWhiteRuns

abbrev Row := Int → Bool
def clock (r t : Nat) := decide (r ≤ t%(r+2))
def source (M : Nat) : Row := fun p => decide (p=(M:Int)+2)
def start (M : Nat) : Row := conf (source M) (clock (M+9))
def mask (x : Row) (t : Nat) := evol x t 0 || evol x t 1

theorem right_init (M : Nat) {z : Int} (hz : 1≤z) : start M z=source M z :=
  (realize _ _).1 z hz

theorem center_clock (M t : Nat) : evol (start M) t 0=clock (M+9) t :=
  (realize _ _).2 t

private theorem phase (r q u : Nat) (h : u<r+2) :
    clock r (q*(r+2)+u)=decide (r≤u) := by
  simp [clock,Nat.add_mod,Nat.mod_eq_of_lt h]

private theorem block (M q : Nat) :
    (∀ i, i<M+9 → evol (start M) (q*(M+11)+i) 0=false) ∧
    evol (start M) (q*(M+11)+(M+9)) 0=true ∧
    evol (start M) (q*(M+11)+(M+9)+1) 0=true := by
  have h (u : Nat) (hu : u<M+11) :
      evol (start M) (q*(M+11)+u) 0=decide (M+9≤u) :=
    (center_clock M _).trans (phase (M+9) q u hu)
  refine ⟨fun i hi => (h i (by omega)).trans (by simp; omega),?_,?_⟩
  · simpa using h (M+9) (by omega)
  · rw [Nat.add_assoc]
    simpa using h (M+9+1) (by omega)

private theorem initial_front (M : Nat) :
    (∀ p : Nat, 1≤p → p≤M+1 → evol (start M) 0 p=false) ∧
    evol (start M) 0 (((M+1)+1:Nat):Int)=true := by
  constructor
  · intro p hp ht
    change start M p=false
    rw [right_init M (by omega)]
    simp [source]; omega
  · change start M _=true
    rw [right_init M (by omega)]
    simp [source]; omega

private theorem first_lock (M : Nat) :
    (∀ i, M+1≤i → i≤M+9 → evol (start M) i 1=true) ∧
    evol (start M) (M+11) 1=true := by
  obtain ⟨hw,hb,hb'⟩ := block M 0
  simp only [Nat.zero_mul,Nat.zero_add] at hw hb hb'
  have v := period_lock (start M) 0 (M+9) (by simpa using hw) (by simpa using hb)
    (by simpa using hb') (by omega) (M+1) (by omega) (initial_front M).1 (initial_front M).2
  simpa using And.intro v.1 v.2.2

private theorem later_lock (M q : Nat) :
    ∀ i, i≤M+9 → evol (start M) ((q+1)*(M+11)+i) 1=true := by
  have first : ∀ n : Nat, evol (start M) ((n+1)*(M+11)) 1=true := by
    intro n
    induction n with
    | zero => simpa using (first_lock M).2
    | succ n ih =>
      obtain ⟨hw,hb,hb'⟩ := block M (n+1)
      have v := period_lock (start M) ((n+1)*(M+11)) (M+9) hw hb hb' (by omega)
        0 (by omega) (by omega) (by simpa using ih)
      rw [Nat.succ_mul]
      exact v.2.2
  obtain ⟨hw,hb,hb'⟩ := block M (q+1)
  exact black_stays (start M) ((q+1)*(M+11)) (M+9) hw (first q)

/-- From one tick after the exceptional reading the masked future is all black. -/
theorem saturated (M t : Nat) (ht : M<t) : mask (start M) t=true := by
  let P := M+11
  let u := t%P
  let q := t/P
  have decomp : q*P+u=t := by
    dsimp [q,u]; rw [Nat.mul_comm,Nat.add_comm]; exact Nat.mod_add_div t P
  have hu : u<M+11 := Nat.mod_lt _ (by dsimp [P]; omega)
  unfold mask
  by_cases early : u<M+9
  · have hb : evol (start M) t 1=true := by
      cases hq : q with
      | zero =>
        have su : t=u := by simpa [hq] using decomp.symm
        exact (first_lock M).1 t (by omega) (by omega)
      | succ n =>
        rw [← decomp,hq]; exact later_lock M n u (by omega)
    simp [hb]
  · have hc : evol (start M) t 0=true := by
      rw [center_clock,← decomp,phase (M+9) q u hu]; simp; omega
    simp [hc]

private theorem earlier (M : Nat) : evol (start M) M 1=false := by
  obtain ⟨hw,_,_⟩ := block M 0
  have v := front_moves (start M) 0 (M+1) (M+9) (by simpa using hw)
    (initial_front M).1 (initial_front M).2 M (by omega) (by omega)
  simpa using v.1 1 (by decide) (by omega)

private theorem add_phase (M q t : Nat) :
    evol (start M) (t+q*(M+11)) 0=evol (start M) t 0 := by
  simp [center_clock,clock,Nat.add_mod]

/-- Future center and OR observations match at every horizon, including
the entire left ray after each common future shift. The two readings at
the white observation times differ. -/
theorem delayed_fork (M Q : Nat) (hq : 0<Q) :
    let j := M+Q*(M+11)
    let x := start M
    M<j ∧ evol x M 0=false ∧ evol x j 0=false ∧
    evol x M 1=false ∧ evol x j 1=true ∧
    (∀ t, evol x (t+Q*(M+11)) 0=evol x t 0) ∧
    (∀ s, mask x (M+1+s)=true ∧ mask x (j+1+s)=true) ∧
    (∀ s (z : Int), z≤0 → evol x (M+1+s) z=evol x (j+1+s) z) := by
  let j := M+Q*(M+11)
  have lt : M<j := Nat.lt_add_of_pos_right (Nat.mul_pos hq (by omega))
  have c := (block M 0).1 M (by omega)
  simp only [Nat.zero_mul,Nat.zero_add] at c
  have cj : evol (start M) j 0=false := (add_phase M Q M).trans c
  have rj : evol (start M) j 1=true := by
    have h := saturated M j lt
    simpa [mask,cj] using h
  refine ⟨lt,c,cj,earlier M,rj,add_phase M Q,fun s =>
    ⟨saturated M _ (by omega),saturated M _ (by change M<j+1+s; omega)⟩,?_⟩
  intro s z hz
  let X : Nat → Row := fun t => evol (start M) (M+1+s+t)
  let Y : Nat → Row := fun t => evol (start M) (j+1+s+t)
  have Xh : Rule30LateObservation.History X := fun _ => rfl
  have Yh : Rule30LateObservation.History Y := fun _ => rfl
  have obs : Rule30LateObservation.Observed X Y 0 (-z).toNat := by
    constructor
    · intro k _
      dsimp [X,Y]
      simp only [Nat.zero_add]
      rw [show j+1+s+k=(M+1+s+k)+Q*(M+11) by dsimp [j]; omega,add_phase]
    · intro k _
      change mask (start M) (M+1+s+(0+k))=mask (start M) (j+1+s+(0+k))
      rw [saturated M _ (by omega),saturated M _ (by omega)]
  exact Rule30LateObservation.observed_row X Y Xh Yh 0 _ obs z (by omega) hz

/-- The origin condition the construction necessarily loses. -/
theorem no_leftmost (M : Nat) :
    ¬ ∃ lo : Int, start M lo=true ∧ ∀ p, p<lo → start M p=false := by
  rintro ⟨lo,hl,hw⟩
  let j := M+1*(M+11)
  let d := lo.toNat
  let z : Int := lo-((j+1+d:Nat):Int)
  have e := (delayed_fork M 1 (by decide)).2.2.2.2.2.2.2 d z (by dsimp [z,d]; omega)
  have h₁ := Rule30FiniteConfigs.evol_left_edge hl hw (j+1+d)
  have h₂ := Rule30FiniteConfigs.evol_eq_false_of_lt hw (M+1+d) z (by dsimp [z,j]; omega)
  exact Bool.noConfusion (h₂.symm.trans (e.trans h₁))

/-- Keep the right origin, and retain only a bounded portion of the left. -/
def cut (x : Row) (L : Nat) : Row := fun z => if z < -(L:Int) then false else x z

private theorem cut_agrees (x : Row) (L t : Nat) (z : Int) (h : -(L:Int)+t≤z) :
    evol (cut x L) t z=evol x t z := by
  induction t generalizing z with
  | zero => simp [evol,cut,show ¬z < -(L:Int) by omega]
  | succ t ih =>
    simp only [evol]
    rw [ih (z-1) (by omega),ih z (by omega),ih (z+1) (by omega)]

/-- Every finite horizon has a finite-seed counterexample. The center clock
is prescribed from the seed through the end of the observations and the
initial right half contains a single black cell. Both observation ages
are independent of the chosen window width. -/
theorem finite_delayed_fork (M Q K : Nat) (hq : 0<Q) :
    let j := M+Q*(M+11)
    let L := j+1+K
    ∃ y : Row, (∀ z, z< -(L:Int) ∨ (M:Int)+2<z → y z=false) ∧
      (∀ z, 1≤z → y z=source M z) ∧
      (∀ t, t≤L → evol y t 0=clock (M+9) t) ∧
      evol y M 1=false ∧ evol y j 1=true ∧
      (∀ s, s<K → mask y (M+1+s)=true ∧ mask y (j+1+s)=true) ∧
      (∀ z : Int, -(K:Int)≤z → z≤0 → evol y (M+1) z=evol y (j+1) z) := by
  let j := M+Q*(M+11)
  let L := j+1+K
  let x := start M
  let y := cut x L
  obtain ⟨lt,_,_,before,after,_,sat,same⟩ := delayed_fork M Q hq
  change M<j at lt
  have copy (t : Nat) (z : Int) (ok : -(L:Int)+t≤z) : evol y t z=evol x t z :=
    cut_agrees x L t z ok
  have right (z : Int) (hz : 1≤z) : y z=source M z := by
    simp [y,cut,show ¬z < -(L:Int) by omega,x,right_init M hz]
  have obs (t : Nat) (h : t≤L) : mask y t=mask x t := by
    simp only [mask,copy t 0 (by omega),copy t 1 (by omega)]
  refine ⟨y,?_,right,?_,?_,?_,?_,?_⟩
  · intro z hz
    rcases hz with h|h
    · exact ite_eq_left h
    · rw [right z (by omega)]; simp [source]; omega
  · intro t ht; exact (copy t 0 (by omega)).trans (center_clock M t)
  · exact (copy M 1 (by dsimp [L]; omega)).trans before
  · exact (copy j 1 (by dsimp [L]; omega)).trans after
  · intro s hs
    exact ⟨(obs _ (by dsimp [L]; omega)).trans (sat s).1,
      (obs (j+1+s) (by dsimp [L]; omega)).trans (sat s).2⟩
  · intro z hz h0
    exact (copy (M+1) z (by dsimp [L]; omega)).trans
      ((same 0 z h0).trans (copy (j+1) z (by dsimp [L]; omega)).symm)

/-- A finite-left example giving equal next windows must place its
later moving edge strictly outside that window. -/
theorem necessary_depth {y : Row} {lo : Int} (hb : y lo=true)
    (hw : ∀ z, z<lo → y z=false) {i j K : Nat} (order : i<j) (reach : lo≤(j:Int)+1)
    (same : ∀ z : Int, -(K:Int)≤z → z≤0 → evol y (i+1) z=evol y (j+1) z) :
    lo<(j:Int)+1-K := by
  apply Classical.byContradiction
  intro no
  let z := lo-((j+1:Nat):Int)
  have e := same z (by dsimp [z]; omega) (by dsimp [z]; omega)
  have b := Rule30FiniteConfigs.evol_left_edge hb hw (j+1)
  have w := Rule30FiniteConfigs.evol_eq_false_of_lt hw (i+1) z (by dsimp [z]; omega)
  exact Bool.noConfusion (w.symm.trans (e.trans b))

end Ruliology.CellularAutomata.Rule30DelayedPastFork
