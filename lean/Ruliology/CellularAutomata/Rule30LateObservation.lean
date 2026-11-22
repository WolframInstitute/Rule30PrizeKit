module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# How long one joint pattern can persist beside the singleton center

Start a window at singleton age `31 <= b` and count `n` updates. Read the
center through the final tick and its positive neighbor on white center ticks
before the final tick. If the center alternates and the white-tick readings
are a rotation of the repetition of `10000`, then `35*n < 27*b+2478`.
The theorem covers every rotation, with either starting color.

Left permutivity turns these later readings into a spatial window. A
synchronizing suffix of that window fixes a pair in any predecessor, so
more cells farther left can be recovered at the previous time. A 155-site
reference orbit carries a twenty-step repeatable schedule of such suffixes.
Each tile recovers twenty earlier times and moves the right end left by
155 sites. A sufficiently long burst would recover a black reference cell
in the singleton's earlier white exterior. The general rewind criterion
also distinguishes readings at two genuinely different singleton ages.

Contributed by Troy Lowry with OpenAI Codex.
-/
@[expose] public section
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
namespace Ruliology.CellularAutomata.Rule30LateObservation
open Rule30Jen

abbrev Row := Int → Bool
abbrev Field := Nat → Row
def step (x : Row) (p : Int) := rule (x (p-1)) (x p) (x (p+1))
def History (X : Field) := ∀ t, X (t+1) = step (X t)
def Agree (x y : Row) (l r : Int) := ∀ p, l ≤ p → p ≤ r → x p = y p
abbrev Pair := Bool × Bool
def pair (x : Row) (p : Int) : Pair := (x p, x (p+1))
def pull (y : Row) (r : Int) : Nat → Pair → Pair
  | 0, u => u
  | n+1, u =>
    let v := pull y r n u
    (xor (y (r-n)) (v.1 || v.2), v.1)
def Reset (y : Row) (r : Int) (n : Nat) :=
  ∀ u v, pull y r n u = pull y r n v

private theorem cancel (a b c : Bool) : xor (rule a b c) (b || c) = a := by
  cases a <;> cases b <;> cases c <;> rfl

theorem pull_spec (x : Row) (r : Int) (n : Nat) :
    pull (step x) r n (pair x r) = pair x (r-n) := by
  induction n with
  | zero => simp [pull]
  | succ n ih =>
    rw [pull, ih]
    simp only [pair, step, cancel]
    congr 2 <;> omega

private theorem pull_congr (x y : Row) (r : Int) (n : Nat) (u : Pair)
    (h : Agree x y (r-n+1) r) : pull x r n u = pull y r n u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pull, pull, ih (fun p hl hr => h p (by omega) hr), h (r-n) (by omega) (by omega)]

theorem before_window (x y : Row) (l r : Int) (n : Nat)
    (hn : 0 < n) (fit : l ≤ r-n+1) (reset : Reset (step x) r n)
    (same : Agree (step x) (step y) l r) :
    Agree x y (l-1) (r-n+1) := by
  have top : pair x (r-n) = pair y (r-n) := by
    rw [← pull_spec x, ← pull_spec y, reset (pair x r) (pair y r)]
    exact pull_congr _ _ _ _ _ (fun p hl hr => same p (by omega) hr)
  have extend (d : Nat) (hd : l-1 ≤ r-n-d) :
      pair x (r-n-d) = pair y (r-n-d) := by
    induction d with
    | zero => simpa using top
    | succ d ih =>
      have h := ih (by omega)
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      let j : Int := r-n-d
      change x j = y j at h₁
      change x (j+1) = y (j+1) at h₂
      have out := same j (by dsimp [j]; omega) (by dsimp [j]; omega)
      change rule (x (j-1)) (x j) (x (j+1)) = rule (y (j-1)) (y j) (y (j+1)) at out
      have prev : x (j-1) = y (j-1) := by
        rw [← cancel (x (j-1)) (x j) (x (j+1)), out, h₁, h₂, cancel]
      have idx : r-n-((d+1 : Nat) : Int) = j-1 := by dsimp [j]; omega
      rw [idx]
      exact Prod.ext prev (by simpa [pair] using h₁)
  intro p hl hr
  by_cases h : p = r-n+1
  · exact h ▸ congrArg Prod.snd top
  · let d := (r-n-p).toNat
    have ep : r-n-(d : Int) = p := by dsimp [d]; omega
    exact ep ▸ congrArg Prod.fst (extend d (by omega))

/-- The OR encodes exactly the two time readings needed at the observed edge.
    When the center is black, no measurement of its right neighbor is needed. -/
def Observed (X Y : Field) (b n : Nat) :=
  (∀ i ≤ n, X (b+i) 0 = Y (b+i) 0) ∧
  (∀ i < n, (X (b+i) 0 || X (b+i) 1) = (Y (b+i) 0 || Y (b+i) 1))

private theorem left (X : Field) (hx : History X) (t : Nat) (p : Int) :
    X t (p-1) = xor (X (t+1) p) (X t p || X t (p+1)) := by
  rw [hx t]; exact (cancel _ _ _).symm

theorem observed_row (X Y : Field) (hx : History X) (hy : History Y)
    (b n : Nat) (obs : Observed X Y b n) : Agree (X b) (Y b) (-(n : Int)) 0 := by
  have aux (d : Nat) : ∀ t, t+d ≤ n → X (b+t) (- (d : Int)) = Y (b+t) (- (d : Int)) := by
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro t ht
      cases d with
      | zero => simpa using obs.1 t (by omega)
      | succ k =>
        have hn := ih k (by omega) (t+1) (by omega)
        have here := ih k (by omega) t (by omega)
        have mask : (X (b+t) (-(k : Int)) || X (b+t) (-(k : Int)+1)) =
            (Y (b+t) (-(k : Int)) || Y (b+t) (-(k : Int)+1)) := by
          cases k with
          | zero => simpa using obs.2 t (by omega)
          | succ j =>
            rw [here, show -((j+1 : Nat) : Int)+1 = -(j : Int) by omega,
                ih j (by omega) t (by omega)]
        rw [show -((k+1 : Nat) : Int) = -(k : Int)-1 by omega,
            left X hx, left Y hy, mask]
        simpa [Nat.add_assoc] using congrArg (fun z => xor z (Y (b+t) (-(k : Int)) || Y (b+t) (-(k : Int)+1))) hn
  intro p hl hr
  have eqp : -(((-p).toNat : Nat) : Int) = p := by omega
  have h := aux (-p).toNat 0 (by omega)
  rw [eqp, Nat.add_zero] at h
  exact h

/-- A certificate chooses one synchronizing suffix at each rewind step.
    Its terminal indices give the actual time and spatial interval forced. -/
inductive Cascade (X : Field) (b n : Nat) : Nat → Int → Int → Prop where
  | start : Cascade X b n b (-(n : Int)) 0
  | rewind {t l r} (k : Nat) (prev : Cascade X b n (t+1) l r)
      (positive : 0 < k) (fits : l ≤ r-k+1) (resets : Reset (X (t+1)) r k) :
      Cascade X b n t (l-1) (r-k+1)

theorem late_observation (X Y : Field) (hx : History X) (hy : History Y)
    {b n t l r} (chain : Cascade X b n t l r) (obs : Observed X Y b n) :
    Agree (X t) (Y t) l r := by
  induction chain with
  | start => exact observed_row X Y hx hy _ _ obs
  | @rewind t l r k _ hk fit reset ih =>
    rw [hx t] at reset ih
    rw [hy t] at ih
    exact before_window _ _ _ _ _ hk fit reset ih

def fromAge (a : Nat) : Field := fun t p => cell (a+t) p
theorem singleton_history (a : Nat) : History (fromAge a) := fun _ => rfl

/-- If a rewind of a single observed word covers the more distant of two
    actual singleton edges, the two ages cannot carry that same word. -/
theorem different_observations {a₁ a₂ b n t : Nat} {l r : Int} (ages : a₁ < a₂)
    (chain : Cascade (fromAge a₂) b n t l r)
    (lo : l ≤ -((a₂+t : Nat) : Int)) (hi : -((a₂+t : Nat) : Int) ≤ r) :
    ¬ Observed (fromAge a₂) (fromAge a₁) b n := by
  intro h
  have e := late_observation _ _ (singleton_history _) (singleton_history _) chain h _ lo hi
  change cell (a₂+t) _ = cell (a₁+t) _ at e
  rw [cell_left_edge, cell_eq_false_of_lt _ _ (by omega)] at e
  contradiction


/-- A space-155, time-10 orbit. Bit p is the cell at ordinary position p. -/
def table : Array Nat := #[
  35457757208718011413405315690284315749817696345,
  19001079419067814718822559829098036953246490830,
  30465483876396857963954322099272582410945933683,
  30398957673815549451195930114455634888267701020,
  30640366682132924215088273309238979682048797095,
  30063096850559149356979728948225418398440500920,
  31003362430561402452521414845389209582046241421,
  29331576786089335827282397141406186972798596820,
  34018046463971801262056909463909989507282489943,
  23307593389313449281879823414351458995755311056]
def ring (t : Nat) (p : Int) := table[(t+9)%10]!.testBit (p%155).toNat

private theorem aligned {t s : Nat} {p j : Int} (ht : t%10=s%10) (hp : p%155=j%155) :
    ring t p = ring s j := by
  unfold ring; rw [hp, show (t+9)%10=(s+9)%10 by omega]

private theorem evolution : ∀ t : Fin 10, ∀ j : Fin 155,
    ring (t.val+1) j.val = step (ring t.val) j.val := by decide

theorem ring_history : History ring := by
  intro t
  funext p
  let u : Fin 10 := ⟨t%10, by omega⟩
  let j : Fin 155 := ⟨(p%155).toNat, by omega⟩
  have ht : u.val=t%10 := rfl
  have hp : (j.val : Int)=p%155 := by dsimp [j]; omega
  unfold step
  have e := evolution u j
  unfold step at e
  rw [aligned (t:=t+1) (s:=u.val+1) (j:=(j.val:Int)) (by omega) (by omega),
      aligned (t:=t) (s:=u.val) (p:=p-1) (j:=(j.val:Int)-1) (by omega) (by omega),
      aligned (t:=t) (s:=u.val) (p:=p) (j:=(j.val:Int)) (by omega) (by omega),
      aligned (t:=t) (s:=u.val) (p:=p+1) (j:=(j.val:Int)+1) (by omega) (by omega)]
  exact e

private def collapses (t : Nat) (r : Int) (k : Nat) : Bool :=
  let f := pull (ring t) r k
  let z := f (false,false)
  f (false,true)==z && f (true,false)==z && f (true,true)==z

private theorem reset_of_check {t r k} (ok : collapses t r k = true) : Reset (ring t) r k := by
  simp [collapses] at ok
  rintro ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem translate (t j i : Nat) (r : Int) (n : Nat) (u : Pair) :
    pull (ring (20*j+t)) (r-155*i) n u = pull (ring t) r n u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pull, pull, ih, aligned (t:=20*j+t) (s:=t) (p:=r-155*i-n) (j:=r-n) (by omega) (by omega)]

private theorem one (Y : Field) (hy : History Y) (j i t k : Nat) (l r : Int)
    (ok : collapses (t+1) r k = true) (pos : 0 < k) (fit : l ≤ r-155*i-k+1)
    (same : Agree (ring (20*j+(t+1))) (Y (20*j+(t+1))) l (r-155*i)) :
    Agree (ring (20*j+t)) (Y (20*j+t)) (l-1) (r-155*i-k+1) := by
  have reset : Reset (ring (20*j+(t+1))) (r-155*i) k := by
    intro u v
    rw [translate, translate]; exact reset_of_check ok u v
  rw [← Nat.add_assoc, ring_history (20*j+t)] at reset
  rw [← Nat.add_assoc, ring_history (20*j+t), hy (20*j+t)] at same
  exact before_window _ _ _ _ _ pos fit reset same

private def retreat : List Nat → Nat
  | [] => 0
  | k::ks => k-1 + retreat ks

private def valid (r : Int) : List Nat → Bool
  | [] => true
  | k::ks => decide (0 < k) && collapses (ks.length+1) r k && valid (r-k+1) ks

private theorem schedule (Y : Field) (hy : History Y) (j i : Nat) (ks : List Nat) :
    ∀ (r l : Int), valid r ks = true → l ≤ r-155*i-retreat ks →
    Agree (ring (20*j+ks.length)) (Y (20*j+ks.length)) l (r-155*i) →
    Agree (ring (20*j)) (Y (20*j)) (l-ks.length) (r-155*i-retreat ks) := by
  induction ks with
  | nil => intro r l _ _ h; simpa [retreat] using h
  | cons k ks ih =>
    intro r l ok fit same
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at ok
    rcases ok with ⟨⟨pos, merged⟩, tail⟩
    simp only [retreat] at fit ⊢
    have h := one Y hy j i ks.length k l r merged pos (by omega) same
    have g := ih (r-k+1) (l-1) tail (by omega) (by
      intro p hl hr; exact h p hl (by omega))
    simp only [List.length_cons]
    intro p hl hr; exact g p (by omega) (by omega)

/-- One repeatable tile rewinds 20 updates at a cost of 155 sites on the right. -/
private def widths : List Nat := [6, 12, 8, 9, 5, 7, 9, 8, 7, 14, 11, 5, 10, 7, 13, 5, 5, 15, 14, 5]
private theorem tile (Y : Field) (hy : History Y) (j i : Nat) (l : Int)
    (fit : l ≤ -166-155*i)
    (same : Agree (ring (20*(j+1))) (Y (20*(j+1))) l (-11-155*i)) :
    Agree (ring (20*j)) (Y (20*j)) (l-20) (-166-155*i) := by
  have count : widths.length = 20 := by decide
  have cost : retreat widths = 155 := by decide
  have h := schedule Y hy j i widths (-11) l (by decide) (by rw [cost]; omega) (by
    rw [count, show 20*j+20=20*(j+1) by omega]; exact same)
  rw [count, cost] at h
  intro p hl hr; exact h p hl (by omega)

private theorem tiles (Y : Field) (hy : History Y) (q : Nat) : ∀ (i : Nat) (l : Int),
    l ≤ -31-155*i-135*q →
    Agree (ring (20*q)) (Y (20*q)) l (-11-155*i) →
    Agree (ring 0) (Y 0) (l-20*q) (-11-155*(i+q : Nat)) := by
  induction q with
  | zero => intro i l _ h; simpa using h
  | succ q ih =>
    intro i l fit same
    have first := tile Y hy q i l (by omega) same
    have rest := ih (i+1) (l-20) (by omega) (by
      simpa only [show -11-155*((i+1 : Nat):Int) = -166-155*i by omega] using first)
    simpa only [show l-20-20*(q:Int) = l-20*((q+1 : Nat):Int) by omega,
      show i+1+q=i+(q+1) by omega] using rest

private theorem not_white : ∀ j : Fin 155, ∃ k : Fin 8,
    ring 0 ((j.val:Int)-k.val) = true := by decide

/-- At absolute age a+20q the singleton cannot begin this joint observation
    for n updates if the displayed inequalities hold. -/
theorem excluded_burst (a q n : Nat) (margin : 155*q+31 ≤ a)
    (length : a+8 ≤ n+20*q) :
    ¬ Observed ring (fromAge a) (20*q) n := by
  intro h
  have start := observed_row _ _ ring_history (singleton_history a) _ _ h
  have rewind := tiles _ (singleton_history a) q 0 (-(n:Int)) (by omega) (by
    intro p hl hr; exact start p hl (by omega))
  let p : Int := -(a:Int)-1
  let j : Fin 155 := ⟨(p%155).toNat, by omega⟩
  obtain ⟨k,hk⟩ := not_white j
  have hj : (j.val:Int)=p%155 := by dsimp [j]; omega
  have kval := k.isLt
  have hb : ring 0 (p-k.val) = true := by
    rw [aligned (s:=0) (j:=(j.val:Int)-k.val) (by rfl) (by omega)]; exact hk
  have e := rewind (p-k.val) (by dsimp [p]; omega) (by dsimp [p]; omega)
  change ring 0 (p-k.val) = cell (a+0) (p-k.val) at e
  rw [hb, cell_eq_false_of_lt _ _ (by dsimp [p]; omega)] at e
  contradiction

/-- The center starts white and alternates. Its positive neighbor on white
    ticks is black exactly at elapsed time two modulo ten. -/
def Pattern (b n : Nat) :=
  (∀ i ≤ n, cell (b+i) 0 = decide (i%2=1)) ∧
  (∀ i < n, i%2=0 → cell (b+i) 1 = decide (i%10=2))

private theorem codes : ∀ t : Fin 10,
    (ring t.val 0 = decide (t.val%2=1)) ∧
    (t.val%2=0 → ring t.val 1 = decide (t.val%10=2)) := by decide

theorem burst_bound (b n : Nat) (age : 31 ≤ b)
    (length : b+8 ≤ n+40*((b-31)/175)) : ¬ Pattern b n := by
  intro pat
  let q := (b-31)/175
  let a := b-20*q
  have hq : q=(b-31)/175 := rfl
  have ha : a=b-20*q := rfl
  have add : a+20*q=b := by omega
  apply excluded_burst a q n (by omega) (by omega)
  have c (i : Nat) : ring (20*q+i) 0 = decide (i%2=1) := by
    let u : Fin 10 := ⟨i%10, by omega⟩
    have hu : u.val=i%10 := rfl
    rw [aligned (s:=u.val) (j:=0) (by omega) rfl, (codes u).1,
        show u.val%2=i%2 by omega]
  have k (i : Nat) (he : i%2=0) : ring (20*q+i) 1 = decide (i%10=2) := by
    let u : Fin 10 := ⟨i%10, by omega⟩
    have hu : u.val=i%10 := rfl
    rw [aligned (s:=u.val) (j:=1) (by omega) rfl, (codes u).2 (by omega),
        show u.val%10=i%10 by omega]
  have center (i : Nat) (hi : i ≤ n) : fromAge a (20*q+i) 0 = decide (i%2=1) := by
    unfold fromAge; rw [← Nat.add_assoc, add]; exact pat.1 i hi
  constructor
  · intro i hi; rw [c, center i hi]
  · intro i hi
    rw [c, center i (by omega)]
    by_cases he : i%2=0
    · have right : fromAge a (20*q+i) 1 = decide (i%10=2) := by
        unfold fromAge; rw [← Nat.add_assoc, add]; exact pat.2 i hi he
      rw [k i he, right]
    · simp [show i%2=1 by omega]

/-- A rotated copy of the same ten-tick joint observation. -/
def RotatedPattern (phase b n : Nat) :=
  (∀ i ≤ n, cell (b+i) 0 = decide ((i+phase)%2=1)) ∧
  (∀ i < n, (i+phase)%2=0 → cell (b+i) 1 = decide ((i+phase)%10=2))

/-- Uniform in both the absolute singleton age and the rotation of the word. -/
theorem all_phases (phase b n : Nat) (age : 31 ≤ b) (length : 27*b+2478 ≤ 35*n) :
    ¬ RotatedPattern phase b n := by
  intro pat
  let d := (10-phase%10)%10
  have hd : d=(10-phase%10)%10 := rfl
  have hphase : (d+phase)%10=0 := by omega
  apply burst_bound (b+d) (n-d) (by omega) (by omega)
  constructor
  · intro i hi
    have e := pat.1 (d+i) (by omega)
    rw [← Nat.add_assoc, show (d+i+phase)%2=i%2 by omega] at e
    exact e
  · intro i hi hwhite
    have e := pat.2 (d+i) (by omega) (by omega)
    rw [← Nat.add_assoc, show (d+i+phase)%10=i%10 by omega] at e
    exact e

end Ruliology.CellularAutomata.Rule30LateObservation
