module
public import Ruliology.CellularAutomata.Rule30MaskedJen
public import Ruliology.CellularAutomata.Rule30SourceObservables

/-!
# A two-site count characterizes the period-three word 011 two cells east

Charge a tick by 1 minus three times the western bit plus six times the
indicator of the spatial word 10. Adding a bounded potential difference makes
the charge nonnegative. Two consecutive zero losses force exactly two black
readings in the eastern column's three-tick window; conversely every such
window forces the first loss to vanish. Thus the cumulative charge is bounded
above exactly for an eventual 011, up to phase. Otherwise it tends to infinity.

This identifies the equality case of a supporting count at the one-third,
zero-source corner of the kit's density polygon. The singleton's moving left
edge gives a deadline for a positive loss on one of two neighboring bonds.
Which bond pays the loss can depend on the interval.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30OneThirdClock
open Rule30Jen
open Rule30SourceObservables (count)

structure Three where
  q : Bool
  r : Bool
  s : Bool

def next (x : Three) (l e : Bool) : Three :=
  ⟨rule l x.q x.r, rule x.q x.r x.s, rule x.r x.s e⟩
def Path (u : Nat → Three) : Prop := ∀ t, ∃ l e, u (t+1) = next (u t) l e
def site (i : Int) (t : Nat) : Three := ⟨cell t i, cell t (i+1), cell t (i+2)⟩
theorem site_path (i : Int) : Path (site i) := by
  intro t
  refine ⟨cell t (i-1),cell t (i+3),?_⟩
  simp [site, next, cell, show i+2-1=i+1 by omega, show i+1+1=i+2 by omega,
    show i+2+1=i+3 by omega]

def charge (x : Three) : Int :=
  1 - 3*(x.q.toNat : Int) + 6*((x.q && !x.r).toNat : Int)
def potential (x : Three) : Int :=
  if x.s then (if x.r then 1 else 2) else (if x.r then 0 else 3)
def loss (x y : Three) : Int := charge x + potential y - potential x
abbrev good (a b c : Bool) : Prop := a.toNat+b.toNat+c.toNat=2

private theorem local_table (x : Three) (l e L E : Bool) :
    let y := next x l e
    let z := next y L E
    0 ≤ loss x y ∧
      (good x.s y.s z.s → loss x y = 0) ∧
      (loss x y = 0 → loss y z = 0 → good x.s y.s z.s) := by
  obtain ⟨a,b,c⟩ := x
  revert a b c l e L E
  decide +kernel

theorem local_loss {u : Nat → Three} (hu : Path u) (t : Nat) :
    0 ≤ loss (u t) (u (t+1)) ∧
    (good (u t).s (u (t+1)).s (u (t+2)).s → loss (u t) (u (t+1)) = 0) ∧
    (loss (u t) (u (t+1)) = 0 → loss (u (t+1)) (u (t+2)) = 0 →
      good (u t).s (u (t+1)).s (u (t+2)).s) := by
  obtain ⟨l,e,y⟩ := hu t
  obtain ⟨L,E,z⟩ := hu (t+1)
  rw [z,y]
  exact local_table _ _ _ _ _

def deficit (u : Nat → Three) : Nat → Int
  | 0 => 0
  | n+1 => deficit u n + charge (u n)
theorem deficit_counts (u : Nat → Three) (n : Nat) :
    deficit u n = (n:Int) - 3*count (fun t => (u t).q) n
      + 6*count (fun t => (u t).q && !(u t).r) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have convert (b : Bool) : Rule30SourceObservables.bit b = (b.toNat : Int) := by cases b <;> rfl
    simp only [deficit,count,ih,charge,Int.natCast_succ,convert]
    omega
private def total (u : Nat → Three) : Nat → Nat
  | 0 => 0
  | n+1 => total u n + (loss (u n) (u (n+1))).toNat

private theorem telescope {u : Nat → Three} (hu : Path u) (n : Nat) :
    (total u n : Int) = deficit u n + potential (u n) - potential (u 0) := by
  induction n with
  | zero => simp [total,deficit]
  | succ n ih =>
    have h := (local_loss hu n).1
    change ((total u n + (loss (u n) (u (n+1))).toNat : Nat) : Int) =
      deficit u n + charge (u n) + potential (u (n+1)) - potential (u 0)
    rw [Int.natCast_add,Int.toNat_of_nonneg h,ih]
    unfold loss
    omega

private theorem rangeH (x : Three) : 0 ≤ potential x ∧ potential x ≤ 3 := by
  obtain ⟨a,b,c⟩ := x
  cases a <;> cases b <;> cases c <;> decide

private theorem grow (u : Nat → Three) {m n : Nat} (mn : m≤n) : total u m≤total u n := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le mn
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    change total u m ≤ total u (m+d) + (loss (u (m+d)) (u (m+d+1))).toNat
    omega

def Tail011 (f : Nat → Bool) : Prop := ∃ T, ∀ n, f (T+n) = decide (n%3≠0)
private def GoodTail (u : Nat → Three) : Prop :=
  ∃ T, ∀ t, T≤t → good (u t).s (u (t+1)).s (u (t+2)).s

private theorem good_tail_iff (u : Nat → Three) : GoodTail u ↔ Tail011 (fun t => (u t).s) := by
  constructor
  · rintro ⟨T,h⟩
    have period (t : Nat) (ht : T≤t) : (u (t+3)).s = (u t).s :=
      (by decide : ∀ a b c d : Bool, good a b c → good b c d → d=a) _ _ _ _ (h t ht) (h (t+1) (by omega))
    have zero := (by decide : ∀ a b c : Bool, good a b c → a=false ∨ b=false ∨ c=false)
      _ _ _ (h T (by omega))
    obtain ⟨S,hs,z⟩ : ∃ S, T≤S ∧ (u S).s=false := by
      rcases zero with a|b|c
      · exact ⟨T,by omega,a⟩
      · exact ⟨T+1,by omega,b⟩
      · exact ⟨T+2,by omega,c⟩
    have on := (by decide : ∀ a b c : Bool, good a b c → a=false → b=true ∧ c=true)
      _ _ _ (h S hs) z
    refine ⟨S,?_⟩
    intro n
    change (u (S+n)).s = decide (n%3≠0)
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn : 3≤n
      · have prev := ih (n-3) (by omega)
        rw [show S+n=S+(n-3)+3 by omega,period _ (by omega),prev]
        rw [show (n-3)%3=n%3 by omega]
      · have casesN : n=0 ∨ n=1 ∨ n=2 := by omega
        rcases casesN with q|q|q <;> subst n
        · exact z
        · exact on.1
        · exact on.2
  · rintro ⟨T,h⟩
    refine ⟨T,?_⟩
    intro t ht
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le ht
    change good (u (T+n)).s (u (T+(n+1))).s (u (T+(n+2))).s
    simp only [h]
    have hn : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases hn with hn|hn|hn
    · rw [hn,show (n+1)%3=1 by omega,show (n+2)%3=2 by omega]; decide
    · rw [hn,show (n+1)%3=2 by omega,show (n+2)%3=0 by omega]; decide
    · rw [hn,show (n+1)%3=0 by omega,show (n+2)%3=1 by omega]; decide

theorem divergence_of_no_clock {u : Nat → Three} (hu : Path u)
    (nc : ¬ Tail011 (fun t => (u t).s)) :
    ∀ K : Nat, ∃ U, ∀ n, U≤n → (K:Int) ≤ deficit u n := by
  have steps (T : Nat) : ∃ t, T≤t ∧ 0<loss (u t) (u (t+1)) := by
    apply Classical.byContradiction
    intro no
    have z t (ht : T≤t) : loss (u t) (u (t+1))=0 := by
      have h := (local_loss hu t).1
      have h' : ¬ 0<loss (u t) (u (t+1)) := fun pos => no ⟨t,ht,pos⟩
      omega
    exact nc ((good_tail_iff u).mp ⟨T,fun t ht =>
      (local_loss hu t).2.2 (z t ht) (z (t+1) (by omega))⟩)
  have big (k : Nat) : ∃ t, k≤total u t := by
    induction k with
    | zero => exact ⟨0,by omega⟩
    | succ k ih =>
      obtain ⟨a,ha⟩ := ih
      obtain ⟨t,ht,hpos⟩ := steps a
      have m := grow u ht
      refine ⟨t+1,?_⟩
      simp only [total]
      omega
  intro K
  obtain ⟨U,hU⟩ := big (K+3)
  refine ⟨U,fun n hn => ?_⟩
  have := telescope hu n
  have := grow u hn
  have := rangeH (u n)
  have := rangeH (u 0)
  omega

theorem bounded_iff_clock {u : Nat → Three} (hu : Path u) :
    (∃ K : Int, ∀ n, deficit u n ≤ K) ↔ Tail011 (fun t => (u t).s) := by
  constructor
  · rintro ⟨K,h⟩
    apply Classical.byContradiction
    intro hc
    obtain ⟨U,g⟩ := divergence_of_no_clock hu hc (K.toNat+1)
    have := g U (by omega)
    have := h U
    omega
  · intro hc
    obtain ⟨T,h⟩ := (good_tail_iff u).mpr hc
    have constant (d : Nat) : total u (T+d) = total u T := by
      induction d with
      | zero => rfl
      | succ d ih =>
        change total u (T+d) + (loss (u (T+d)) (u (T+d+1))).toNat = _
        rw [(local_loss hu (T+d)).2.1 (h _ (by omega)),ih]
        rfl
    refine ⟨(total u T:Int)+3,fun n => ?_⟩
    have le : total u n ≤ total u T := by
      by_cases hn : n≤T
      · exact grow u hn
      · rw [show n=T+(n-T) by omega,constant]
        exact Nat.le_refl _
    have := telescope hu n
    have := rangeH (u n)
    have := rangeH (u 0)
    omega

/-- For the singleton the western bond is (-2,-1) and the tested column is its center. -/
theorem singleton_west_iff :
    (∃ K : Int, ∀ n, deficit (site (-2)) n ≤ K) ↔ Tail011 (fun t => cell t 0) := by
  exact bounded_iff_clock (site_path (-2))

private theorem period_on_window {u : Nat → Three} (hu : Path u) (t : Nat)
    (z : ∀ k, t ≤ k → k≤t+2 → loss (u k) (u (k+1))=0) : (u t).s = (u (t+3)).s := by
  exact (by decide : ∀ a b c d : Bool, good a b c → good b c d → a=d) _ _ _ _
    ((local_loss hu t).2.2 (z t (by omega) (by omega)) (z (t+1) (by omega) (by omega)))
    ((local_loss hu (t+1)).2.2 (z (t+1) (by omega) (by omega)) (z (t+2) (by omega) (by omega)))

def bondLoss (i : Int) (t : Nat) := loss (site i t) (site i (t+1))

/-- The singleton's moving left edge forces a positive loss on at least one of the
bonds (-2,-1) and (-1,0) between U and 2U+5 inclusive. -/
theorem singleton_deadline (U : Nat) :
    ∃ t, U≤t ∧ t≤2*U+5 ∧ (0 < bondLoss (-2) t ∨ 0 < bondLoss (-1) t) := by
  apply Classical.byContradiction
  intro no
  have z (i : Int) (hi : i = -2 ∨ i = -1) (t : Nat) (lo : U≤t) (up : t≤2*U+5) :
      bondLoss i t=0 := by
    have nn := (local_loss (site_path i) t).1
    change 0 ≤ bondLoss i t at nn
    have notPos : ¬ 0<bondLoss i t := by
      intro hp
      rcases hi with h|h <;> subst i
      · exact no ⟨t,lo,up,Or.inl hp⟩
      · exact no ⟨t,lo,up,Or.inr hp⟩
    omega
  have eqn (i : Int) (hi : i = -2 ∨ i = -1) (k : Nat) (hk : k≤U+3) :
      cell (U+k) (i+2) = cell (U+3+k) (i+2) := by
    rw [show U+3+k=U+k+3 by omega]
    exact period_on_window (site_path i) (U+k) (fun t ht h1 => z i hi t (by omega) (by omega))
  have center (k : Nat) (hk : k≤U+3) : cell (U+k) 0=cell (U+3+k) 0 :=
    eqn (-2) (Or.inl rfl) k hk
  apply Rule30MaskedJen.window_jen (t₁:=U) (t₂:=U+3) (by omega) center
  intro k hk
  have east : cell (U+k) 1=cell (U+3+k) 1 := eqn (-1) (Or.inr rfl) k (by omega)
  simp [Rule30MaskedJen.orCol,center k (by omega),east]

end Ruliology.CellularAutomata.Rule30OneThirdClock
