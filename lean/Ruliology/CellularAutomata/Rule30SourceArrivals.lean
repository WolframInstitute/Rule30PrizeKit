module

public import Ruliology.CellularAutomata.Rule30Prize

/-! # First arrivals of oriented sources at the singleton center

Over two ticks the nonlinear contributions to the center come from a spatial
10 at either neighboring site and a central 10 one tick later. A left 10 has
no partner among those sources exactly when site 2 is black.

If whites in a periodic center tail are isolated, a phase-selected stream of
single arrivals must be aperiodic. With at least two blacks after each white,
even the net parity of all three arrivals must be aperiodic. In each case an
explicit recurrence would otherwise make the right column periodic as well.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceArrivals
open Rule30Jen

def source (j : Int) (t : Nat) := cell t j && !cell t (j+1)
def exposed (t : Nat) := source (-1) t && cell t 2
def net (t : Nat) := xor (source (-1) t) (xor (source 1 t) (source 0 (t+1)))
def shell (t : Nat) := xor (cell t (-2)) (cell t 2)

/-- On white ticks keep an unpaired left source. On a black-to-black step
keep a delayed central source if it is the sole arrival. -/
def selected (t : Nat) := exposed t || (cell t 0 && cell (t+1) 0 && cell t 2)

theorem partners (t : Nat) (h : source (-1) t = true) :
    source 1 t = (cell t 1 && !cell t 2) ∧
    source 0 (t+1) = (!cell t 1 && !cell t 2) := by
  exact ⟨rfl,(by decide : ∀ l c r u : Bool, (l && !c) = true →
    (rule l c r && !rule c r u) = (!r && !u)) _ _ _ _ h⟩

theorem selected_arrives (t : Nat) (h : selected t = true) : net t = true := by
  exact (by decide : ∀ l c r u : Bool,
    (((l && !c) && u) || (c && rule l c r && u)) = true →
    xor (l && !c) (xor (r && !u) (rule l c r && !rule c r u)) = true) _ _ _ _ h

theorem selected_single (t : Nat) (h : selected t = true) :
    source 1 t = false ∧ source (-1) t ≠ source 0 (t+1) := by
  exact (by decide : ∀ l c r u : Bool,
    (((l && !c) && u) || (c && rule l c r && u)) = true →
    (r && !u) = false ∧ (l && !c) ≠ (rule l c r && !rule c r u)) _ _ _ _ h

theorem two_step (t : Nat) : cell (t+2) 0 = xor (shell t) (net t) := by
  exact (by decide : ∀ a b c d e : Bool,
    rule (rule a b c) (rule b c d) (rule c d e) =
    xor (xor a e) (xor (b && !c) (xor (d && !e) (rule b c d && !rule c d e)))) _ _ _ _ _

private def channel (useNet : Bool) := if useNet then net else selected
private def observe (useNet c n r u : Bool) :=
  let left := !c && xor r n
  if useNet then xor left (xor (r && !u) (n && !rule c r u))
    else (left && u) || (c && n && u)

private theorem observed (useNet : Bool) (t : Nat) : channel useNet t =
    observe useNet (cell t 0) (cell (t+1) 0) (cell t 1) (cell t 2) := by
  cases useNet with
  | true => exact (by decide : ∀ l c r u : Bool,
      xor (l && !c) (xor (r && !u) (rule l c r && !rule c r u)) =
        observe true c (rule l c r) r u) _ _ _ _
  | false => exact (by decide : ∀ l c r u : Bool,
      ((l && !c) && u || (c && rule l c r && u)) =
        observe false c (rule l c r) r u) _ _ _ _

/-- On 0101 a change in the unpaired left source between the two white
ticks changes the total arrival parity, even allowing source replacement. -/
theorem alternating_change_visible (t : Nat) (a : cell t 0=false) (b : cell (t+1) 0=true)
    (c : cell (t+2) 0=false) (d : cell (t+3) 0=true)
    (h : exposed t ≠ exposed (t+2)) : net t ≠ net (t+2) := by
  have e : selected t ≠ selected (t+2) := by simpa [selected,a,c] using h
  change channel false t ≠ channel false (t+2) at e
  change channel true t ≠ channel true (t+2)
  rw [observed,observed] at e ⊢
  rw [a,b,c,d] at e ⊢
  have loc : ∀ r u v w : Bool,
      let r₁ := rule false r u
      let u₁ := rule r u v
      let v₁ := rule u v w
      let r₂ := rule true r₁ u₁
      let u₂ := rule r₁ u₁ v₁
      observe false false true r u ≠ observe false false true r₂ u₂ →
      observe true false true r u ≠ observe true false true r₂ u₂ := by decide
  have steps : cell (t+2) 1 = rule true (rule false (cell t 1) (cell t 2))
      (rule (cell t 1) (cell t 2) (cell t 3)) ∧
      cell (t+2) 2 = rule (rule false (cell t 1) (cell t 2))
      (rule (cell t 1) (cell t 2) (cell t 3)) (rule (cell t 2) (cell t 3) (cell t 4)) := by
    rw [← a,← b]; exact ⟨rfl,rfl⟩
  rw [steps.1,steps.2] at e ⊢
  exact loc _ _ _ _ e

/-- Reconstruct the next right bit. c₀,c₁,c₂ are three consecutive
center bits; r₀,r₁ are the first two right bits; z₀,z₁,z₂ are readings. -/
private def decode (c₀ c₁ c₂ r₀ r₁ z₀ z₁ z₂ : Bool) :=
  if c₂ then (if c₁ then !(r₁ || z₁) else r₁ || z₁)
  else if c₀ then r₀ && (z₀ || !z₂) else !r₀ && !(z₀ || z₂)

private def whiteGap (useNet c n nn : Bool) : Prop :=
  c=false → n=true ∧ (useNet=true → nn=true)

/-- Four scheduled center bits and four right cells cover the entire
dependency cone of this identity. Everything outside it is arbitrary. -/
private theorem decoder_table : ∀ m a b c d r u v w : Bool,
    whiteGap m a b c → whiteGap m b c d → (c=false → d=true) →
    let r₁ := rule a r u
    let u₁ := rule r u v
    let v₁ := rule u v w
    let r₂ := rule b r₁ u₁
    let u₂ := rule r₁ u₁ v₁
    r₂ = decode a b c r r₁ (observe m a b r u) (observe m b c r₁ u₁)
      (observe m c d r₂ u₂) := by
  unfold whiteGap
  intro m a b c d
  cases m <;> cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem decoder (m : Bool) (t : Nat)
    (h₀ : whiteGap m (cell t 0) (cell (t+1) 0) (cell (t+2) 0))
    (h₁ : whiteGap m (cell (t+1) 0) (cell (t+2) 0) (cell (t+3) 0))
    (h₂ : cell (t+2) 0=false → cell (t+3) 0=true) :
    cell (t+2) 1 = decode (cell t 0) (cell (t+1) 0) (cell (t+2) 0)
      (cell t 1) (cell (t+1) 1) (channel m t) (channel m (t+1)) (channel m (t+2)) := by
  rw [observed,observed,observed]
  exact decoder_table m _ _ _ _ (cell t 1) (cell t 2) (cell t 3) (cell t 4) h₀ h₁ h₂

private theorem decoded (m : Bool) (hc : EventuallyPeriodic (fun t => cell t 0))
    (gaps : ∃ W, ∀ t, W≤t → whiteGap m (cell t 0) (cell (t+1) 0) (cell (t+2) 0)) :
    ¬ EventuallyPeriodic (channel m) := by
  intro hz
  obtain ⟨W,hw⟩ := gaps
  obtain ⟨T,p,hp,pc,pz⟩ := common_period hc hz
  let start (i : Nat) := max T W+i*p
  obtain ⟨i,j,hij,_,init⟩ := pigeonhole 2
    (fun i => [cell (start i) 1, cell (start i+1) 1]) (fun _ => rfl)
  let q := (j-i)*p
  have hq : 0<q := Nat.mul_pos (by omega) hp
  have shift : start j=start i+q := by
    dsimp [start,q]; rw [Nat.sub_mul]; have := Nat.mul_le_mul_right p (Nat.le_of_lt hij); omega
  have ht : T≤start i := by dsimp [start]; omega
  have hw' : W≤start i := by dsimp [start]; omega
  have cc (k : Nat) : cell (start i+k) 0=cell (start j+k) 0 := by
    rw [shift,show start i+q+k=start i+k+q by omega]
    exact (periodic_mul (f:=fun t => cell t 0) pc (j-i) _ (by omega)).symm
  have zz (k : Nat) : channel m (start i+k)=channel m (start j+k) := by
    rw [shift,show start i+q+k=start i+k+q by omega]
    exact (periodic_mul pz (j-i) _ (by omega)).symm
  have ruleAt (s : Nat) (hs : W≤s) := decoder m s (hw _ hs) (hw _ (by omega))
    (fun h => (hw (s+2) (by omega) h).1)
  have pair (k : Nat) : cell (start i+k) 1=cell (start j+k) 1 ∧
      cell (start i+k+1) 1=cell (start j+k+1) 1 := by
    induction k with
    | zero => simpa using init
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e := ruleAt (start i+k) (by omega)
      have f := ruleAt (start j+k) (by omega)
      simp only [Nat.add_assoc] at e f ih ⊢
      rw [e,f,cc k,cc (k+1),cc (k+2),zz k,zz (k+1),zz (k+2),ih.1,ih.2]
  apply not_adjacent 0 hc
  refine ⟨start i,q,hq,fun t ht' => ?_⟩
  have e := (pair (t-start i)).1
  rw [shift,show start i+q+(t-start i)=t+q by omega,show start i+(t-start i)=t by omega] at e
  exact e.symm

theorem selected_aperiodic (hc : EventuallyPeriodic (fun t => cell t 0))
    (gaps : ∃ W, ∀ t, W≤t → cell t 0=false → cell (t+1) 0=true) :
    ¬ EventuallyPeriodic selected := by
  obtain ⟨W,h⟩ := gaps
  exact decoded false hc ⟨W,fun t ht eq => ⟨h t ht eq,by simp⟩⟩

theorem net_aperiodic (hc : EventuallyPeriodic (fun t => cell t 0))
    (gaps : ∃ W, ∀ t, W≤t → cell t 0=false → cell (t+1) 0=true ∧ cell (t+2) 0=true) :
    ¬ EventuallyPeriodic net := by
  obtain ⟨W,h⟩ := gaps
  exact decoded true hc ⟨W,fun t ht eq => ⟨(h t ht eq).1,fun _ => (h t ht eq).2⟩⟩

theorem shell_aperiodic (hc : EventuallyPeriodic (fun t => cell t 0))
    (gaps : ∃ W, ∀ t, W≤t → cell t 0=false → cell (t+1) 0=true ∧ cell (t+2) 0=true) :
    ¬ EventuallyPeriodic shell := by
  intro hs
  obtain ⟨T,p,hp,pc,ps⟩ := common_period hc hs
  apply net_aperiodic hc gaps
  refine ⟨T,p,hp,fun t ht => ?_⟩
  have eq : cell (t+p+2) 0 = cell (t+2) 0 := by
    rw [show t+p+2=t+2+p by omega]; exact pc (t+2) (by omega)
  rw [two_step (t+p),two_step t,ps t ht] at eq
  exact (by decide : ∀ a b c : Bool, xor a b=xor a c → b=c) _ _ _ eq

end Ruliology.CellularAutomata.Rule30SourceArrivals
