module

public import Ruliology.CellularAutomata.Rule30SourceArrivals

/-! # Return times of a seven-cell word under an alternating center

Read positions −4 through +2 from left to right at white center times. During
five alternating center observations the word 0101001 occurs exactly when the
first two cells to the right read 01. Track seven right cells. Each two-tick
transition accepts either value of the eighth cell on both ticks.

* For a first return after g ticks, g is a multiple of four, six, or ten.
  If g ≥ 12 the next gap is six ticks; if g = 10 the next gap is four ticks,
  provided the center continues alternating through the specified window.
* On an infinite alternating singleton tail the word occurs arbitrarily late
  in each of the two white phases modulo four. Missing one phase would make
  the event stream eventually eight-periodic, contradicting the singleton
  selected-source theorem. The center's nonperiodicity remains open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EventReturns
open Ruliology.CellularAutomata.Rule30Jen

private def pack (a b c d e f g : Bool) : Fin 128 :=
  ⟨(a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat+32*f.toNat+64*g.toNat)%128,by omega⟩

private def tick (l : Bool) (x : Fin 128) (z : Bool) : Fin 128 :=
  let b := x.val.testBit
  pack (rule l (b 0) (b 1)) (rule (b 0) (b 1) (b 2))
    (rule (b 1) (b 2) (b 3)) (rule (b 2) (b 3) (b 4))
    (rule (b 3) (b 4) (b 5)) (rule (b 4) (b 5) (b 6)) (rule (b 5) (b 6) z)

private def strip (t : Nat) := pack (cell t 1) (cell t 2) (cell t 3)
  (cell t 4) (cell t 5) (cell t 6) (cell t 7)
private theorem step (t : Nat) : strip (t+1)=tick (cell t 0) (strip t) (cell t 8) := by
  exact (by decide +kernel : ∀ l a b c d e f g z : Bool,
    pack (rule l a b) (rule a b c) (rule b c d) (rule c d e) (rule d e f) (rule e f g) (rule f g z) =
      tick l (pack a b c d e f g) z) _ _ _ _ _ _ _ _ _

/-- The two right sites read white, black. Sample at white center times. -/
def marker (t : Nat) : Prop := cell t 1=false ∧ cell t 2=true
private def hit (x : Fin 128) := decide (x.val%4=2)
private theorem mark (t : Nat) : hit (strip t)=true ↔ marker t := by
  exact (by decide : ∀ a b c d e f g : Bool, hit (pack a b c d e f g)=true ↔ a=false ∧ b=true)
    _ _ _ _ _ _ _

private def stage (k : Nat) : Fin 7 := ⟨if k<5 then k else 5+(k+1)%2,by split <;> omega⟩
private def advance (s : Fin 7) : Fin 7 := ⟨if s.val=6 then 5 else s.val+1,by split <;> omega⟩
private theorem advance_stage (k : Nat) : advance (stage k)=stage (k+1) := by
  apply Fin.ext; simp only [advance,stage]; split <;> split <;> split <;> omega

private def allowed (s : Fin 7) (x : Fin 128) : Bool :=
  match s.val with
  | 0 => hit x
  | 1 => [0,4,8,16,24,28,32,40,52,56,60,64,68,72,80,88,92,96,100,104,116,120,124].contains x.val
  | 2 => [1,7,13,23,25,39,49,65,71,77,87,89,97,103,119].contains x.val
  | 3 => [4,20,28,32,40,52,68,72,84,92,96,100,104,112,116].contains x.val
  | 4 => [7,25,39,45,89,103,109].contains x.val
  | 5 => [32,60,96,112,124].contains x.val
  | _ => [25,45,89,109].contains x.val

private def landing (x : Fin 128) := [10,74,106].contains x.val
private def ten (x : Fin 128) := [14,30,78,94,126].contains x.val
private def hop (x : Fin 128) (u v : Bool) := tick true (tick false x u) v

private theorem certificate : ∀ s : Fin 7, ∀ x : Fin 128, ∀ u v : Bool,
    allowed s x=true →
    let y := tick true (tick false x u) v
    (hit y=false → allowed (advance s) y=true) ∧
    (hit y=true → s.val≠0 ∧ s.val≠6 ∧ (s.val=5 → landing y=true) ∧
      (s.val=4 → ten y=true)) := by decide +kernel

/-- If successive white-phase markers are 2n ticks apart during alternation,
then their positive separation is divisible by four or is six or ten ticks. -/
private theorem classify (a n : Nat) (pos : 0<n)
    (white : ∀ k, k<n → cell (a+2*k) 0=false)
    (black : ∀ k, k<n → cell (a+2*k+1) 0=true)
    (first : marker a) (last : marker (a+2*n))
    (quiet : ∀ k, 0<k → k<n → ¬marker (a+2*k)) :
    (n%2=0 ∨ n=3 ∨ n=5) ∧ (6≤n → landing (strip (a+2*n))=true) ∧
      (n=5 → ten (strip (a+2*n))=true) := by
  have link (k : Nat) (hk : k<n) : strip (a+2*(k+1)) =
      tick true (tick false (strip (a+2*k)) (cell (a+2*k) 8)) (cell (a+2*k+1) 8) := by
    rw [show a+2*(k+1)=a+2*k+1+1 by omega,step,step (a+2*k),white k hk,black k hk]
  have keep (k : Nat) (hk : k<n) : allowed (stage k) (strip (a+2*k))=true := by
    induction k with
    | zero => simpa [stage,allowed] using (mark a).mpr first
    | succ k ih =>
      have h := (certificate _ _ (cell (a+2*k) 8) (cell (a+2*k+1) 8) (ih (by omega))).1
      rw [← link k (by omega),advance_stage] at h
      apply h
      cases eq : hit (strip (a+2*(k+1))) with
      | false => rfl
      | true => exact False.elim (quiet _ (by omega) hk ((mark _).mp eq))
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have h := (certificate _ _ (cell (a+2*k) 8) (cell (a+2*k+1) 8) (keep k (by omega))).2
  rw [← link k (by omega)] at h
  obtain ⟨h0,h6,hl,ht⟩ := h ((mark _).mpr last)
  refine ⟨?_,fun hn => hl ?_,fun hn => ht ?_⟩
  all_goals simp only [stage] at *
  all_goals split at h0 <;> split at h6 <;> (try split) <;> omega

def wordAt (t : Nat) : Prop :=
  ([-4,-3,-2,-1,0,1,2] : List Int).map (cell t)=[false,true,false,true,false,false,true]

private def r2 (a b c d e : Bool) := rule (rule a b c) (rule b c d) (rule c d e)
private def r3 (a b c d e f g : Bool) := rule (r2 a b c d e) (r2 b c d e f) (r2 c d e f g)
private def r4 (a b c d e f g h i : Bool) :=
  rule (r3 a b c d e f g) (r3 b c d e f g h) (r3 c d e f g h i)

theorem word_iff_marker (t : Nat) (c0 : cell t 0=false) (c1 : cell (t+1) 0=true)
    (c2 : cell (t+2) 0=false) (c3 : cell (t+3) 0=true) (c4 : cell (t+4) 0=false) :
    wordAt t ↔ marker t := by
  exact (by decide +kernel : ∀ a b c d e f g h i : Bool, e=false → rule d e f=true →
    r2 c d e f g=false → r3 b c d e f g h=true → r4 a b c d e f g h i=false →
    ([a,b,c,d,e,f,g]=[false,true,false,true,false,false,true] ↔ f=false ∧ g=true))
    (cell t (-4)) (cell t (-3)) (cell t (-2)) (cell t (-1)) (cell t 0)
    (cell t 1) (cell t 2) (cell t 3) (cell t 4) c0 c1 c2 c3 c4

private theorem echo (t : Nat) (white : ∀ k, k<3 → cell (t+2*k) 0=false)
    (black : ∀ k, k<3 → cell (t+2*k+1) 0=true) :
    (landing (strip t)=true → ¬marker (t+2) ∧ ¬marker (t+4) ∧ marker (t+6)) ∧
    (ten (strip t)=true → ¬marker (t+2) ∧ marker (t+4)) := by
  let u (k : Nat) := cell (t+2*k) 8
  let v (k : Nat) := cell (t+2*k+1) 8
  have h (k : Nat) (hk : k<3) : strip (t+2*(k+1))=hop (strip (t+2*k)) (u k) (v k) := by
    unfold hop
    rw [show t+2*(k+1)=t+2*k+1+1 by omega,step,step (t+2*k),white k hk,black k hk]
  have h1 : strip (t+2)=hop (strip t) (u 0) (v 0) := by simpa using h 0 (by decide)
  have h2 := h 1 (by decide)
  have h3 := h 2 (by decide)
  change strip (t+4)=hop (strip (t+2)) _ _ at h2
  change strip (t+6)=hop (strip (t+4)) _ _ at h3
  rw [← mark,← mark,← mark,h3,h2,h1]
  have L : ∀ x : Fin 128, landing x=true → ∀ a b c d e f : Bool,
    let y := hop x a b; let z := hop y c d
    hit y≠true ∧ hit z≠true ∧ hit (hop z e f)=true := by decide +kernel
  have S : ∀ x : Fin 128, ten x=true → ∀ a b c d : Bool,
    let y := hop x a b
    hit y≠true ∧ hit (hop y c d)=true := by decide +kernel
  exact ⟨fun hL => L _ hL _ _ _ _ _ _,fun hS => S _ hS _ _ _ _⟩

/-- For successive copies of the word starting 2n ticks apart in an alternating
window, every gap of at least 12 forces a next gap of six. A gap of ten forces
a next gap of four. The window includes the four ticks used to recognize words. -/
theorem word_returns (a n : Nat) (pos : 0<n)
    (white : ∀ k, k≤n+5 → cell (a+2*k) 0=false)
    (black : ∀ k, k<n+5 → cell (a+2*k+1) 0=true)
    (first : wordAt a) (last : wordAt (a+2*n))
    (quiet : ∀ k, 0<k → k<n → ¬wordAt (a+2*k)) :
    (n%2=0 ∨ n=3 ∨ n=5) ∧
    (6≤n → ¬wordAt (a+2*n+2) ∧ ¬wordAt (a+2*n+4) ∧ wordAt (a+2*n+6)) ∧
    (n=5 → ¬wordAt (a+2*n+2) ∧ wordAt (a+2*n+4)) := by
  have eq (k : Nat) (hk : k≤n+3) : wordAt (a+2*k) ↔ marker (a+2*k) :=
    word_iff_marker _ (white _ (by omega)) (black _ (by omega))
      (by rw [show a+2*k+2=a+2*(k+1) by omega]; exact white _ (by omega))
      (by rw [show a+2*k+3=a+2*(k+1)+1 by omega]; exact black _ (by omega))
      (by rw [show a+2*k+4=a+2*(k+2) by omega]; exact white _ (by omega))
  obtain ⟨hp,hl,ht⟩ := classify a n pos (fun k hk => white k (by omega))
    (fun k hk => black k (by omega)) (by simpa using (eq 0 (by omega)).mp (by simpa using first))
    ((eq n (by omega)).mp last) (fun k h1 h2 hm => quiet k h1 h2 ((eq k (by omega)).mpr hm))
  have e := echo (a+2*n)
    (fun k hk => by rw [show a+2*n+2*k=a+2*(n+k) by omega]; exact white _ (by omega))
    (fun k hk => by rw [show a+2*n+2*k+1=a+2*(n+k)+1 by omega]; exact black _ (by omega))
  have q (j : Nat) (hj : j≤3) : wordAt (a+2*n+2*j) ↔ marker (a+2*n+2*j) := by
    rw [show a+2*n+2*j=a+2*(n+j) by omega]; exact eq _ (by omega)
  rw [q 1 (by decide),q 2 (by decide),q 3 (by decide)]
  exact ⟨hp,fun h => e.1 (hl h),fun h => e.2 (ht h)⟩

/-! The rank certificate compares observations eight ticks apart. Let H(x) be
the four possible outputs of one two-tick hop, allowing repetitions. Draw
x → z if four hops lead to z without a marker after hop one or three.
Give an edge cost one when its endpoint readings differ and zero otherwise.
The stored rank is the maximum sum of costs on a path from x. Its values
range from zero to three. It can be generated by starting at zero everywhere
and updating each entry to the maximum of zero and edge cost plus successor
rank until unchanged. The proof only needs the checked inequalities.

For intermediate hops, bound stores the maximum of final rank plus the
discrepancy from the initial bit over the remaining legal hops (zero for
empty successor sets). The three integers are bit planes, with state x at
bit x.val. The four one-hop checks include both external input bits. -/
private def planes (a b c : Nat) (x : Fin 128) := (a.testBit x.val).toNat +
  2*(b.testBit x.val).toNat + 4*(c.testBit x.val).toNat
private def rank (x : Fin 128) := planes 45692276391980151239253901015024952106 87751115300365884876433061138131058944 0 x
private def bound (phase : Nat) (h : Bool) (x : Fin 128) : Nat :=
  match phase,h with
  | 3, false => planes 208120813204377923559695151405624434389 10719674377645876187350712961922899604 0 x
  | 2, false => planes 132156330994172623247558001994826015530 127773362620624289145177125736805835050 0 x
  | 1, false => planes 10724866754952379755021999663184551573 15961369005138069854480970577198124741 0 x
  | 3, true => planes 132161553716560539903679456026143777066 16047036951536540786684963265855953105 5070609673357302914365180478980 x
  | 2, true => planes 5332595437497927970061533065611772997 130452608398911837710430431900792005418 18446744073709551616 x
  | 1, true => planes 200080414950101009062941400085162917952 10719664315646229506274452699968904341 4835703279584416605929984 x
  | _,_ => rank x + (hit x != h).toNat

private theorem bound0 : ∀ x : Fin 128, ∀ a b : Bool,
    let y := hop x a b
    hit y=false → bound 1 (hit x) y≤rank x := by decide +kernel
private theorem bound1 : ∀ x : Fin 128, ∀ h a b : Bool,
    bound 2 h (hop x a b)≤bound 1 h x := by decide +kernel
private theorem bound2 : ∀ x : Fin 128, ∀ h a b : Bool,
    let y := hop x a b
    hit y=false → bound 3 h y≤bound 2 h x := by decide +kernel
private theorem bound3 : ∀ x : Fin 128, ∀ h a b : Bool,
    bound 4 h (hop x a b)≤bound 3 h x := by decide +kernel

private theorem cost (t : Nat) (white : ∀ k, k<4 → cell (t+2*k) 0=false)
    (black : ∀ k, k<4 → cell (t+2*k+1) 0=true)
    (z1 : ¬marker (t+2)) (z3 : ¬marker (t+6)) :
    rank (strip (t+8)) + (hit (strip (t+8)) != hit (strip t)).toNat ≤ rank (strip t) := by
  let u (k : Nat) := cell (t+2*k) 8
  let v (k : Nat) := cell (t+2*k+1) 8
  have step2 (k : Nat) (hk : k<4) : strip (t+2*(k+1))=hop (strip (t+2*k)) (u k) (v k) := by
    unfold hop
    rw [show t+2*(k+1)=t+2*k+1+1 by omega,step,step (t+2*k),white k hk,black k hk]
  have h0 := bound0 (strip t) (u 0) (v 0)
  have h1 := bound1 (strip (t+2)) (hit (strip t)) (u 1) (v 1)
  have h2 := bound2 (strip (t+4)) (hit (strip t)) (u 2) (v 2)
  have h3 := bound3 (strip (t+6)) (hit (strip t)) (u 3) (v 3)
  have s0 : strip (t+2)=hop (strip t) (u 0) (v 0) := by simpa using step2 0 (by decide)
  rw [← s0] at h0
  rw [← step2 1 (by decide)] at h1
  rw [← step2 2 (by decide)] at h2
  rw [← step2 3 (by decide)] at h3
  have off (s : Nat) (hn : ¬marker s) : hit (strip s)=false := by
    cases he : hit (strip s) with
    | true => exact False.elim (hn ((mark s).mp he))
    | false => rfl
  exact Nat.le_trans h3 (Nat.le_trans (h2 (off _ z3)) (Nat.le_trans h1 (h0 (off _ z1))))

private theorem stable (v : Nat → Nat) (f : Nat → Bool)
    (h : ∀ n, v (n+1)+(f (n+1) != f n).toNat ≤ v n) :
    ∃ N, ∀ n, N≤n → f (n+1)=f n := by
  have minim (m : Nat) : ∀ j, v j=m → ∃ N, ∀ n, v N≤v n := by
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro j hj
      by_cases ex : ∃ i, v i<m
      · obtain ⟨i,hi⟩ := ex; exact ih _ hi i rfl
      · exact ⟨j,fun n => by have h : ¬v n<m := fun h => ex ⟨n,h⟩; omega⟩
  obtain ⟨N,low⟩ := minim (v 0) 0 rfl
  have le (k : Nat) : v (N+k)≤v N := by
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih => change v (N+k+1)≤v N; have := h (N+k); omega
  refine ⟨N,fun n hn => ?_⟩
  have a := le (n-N)
  rw [show N+(n-N)=n by omega] at a
  have b := low (n+1)
  have c := h n
  cases x : f (n+1) <;> cases y : f n <;> simp [x,y] at c ⊢ <;> omega

open Ruliology.CellularAutomata.Rule30SourceArrivals

private theorem white_read (t : Nat) (c : cell t 0=false) (d : cell (t+1) 0=true) :
    selected t = hit (strip t) := by
  have eq : selected t=true ↔ marker t :=
    (by decide : ∀ l c r u : Bool, c=false → rule l c r=true →
      ((((l && !c) && u) || (c && rule l c r && u))=true ↔ r=false ∧ u=true))
      _ _ _ _ c d
  have both := eq.trans (mark t).symm
  cases x : selected t <;> cases y : hit (strip t) <;> simp_all

private theorem phase_hit (a : Nat) (white : ∀ k, cell (a+2*k) 0=false)
    (black : ∀ k, cell (a+2*k+1) 0=true) : ∃ k, marker (a+4*k+2) := by
  apply Classical.byContradiction
  intro hn
  have off (k : Nat) : ¬marker (a+4*k+2) := fun h => hn ⟨k,h⟩
  let time (p j : Nat) := a+4*p+8*j
  have S (p : Nat) : ∃ N, ∀ j, N≤j → hit (strip (time p (j+1)))=hit (strip (time p j)) := by
    apply stable (fun j => rank (strip (time p j))) (fun j => hit (strip (time p j)))
    intro j
    have e := cost (time p j)
      (fun k _ => by rw [show time p j+2*k=a+2*(2*p+4*j+k) by dsimp [time]; omega]; apply white)
      (fun k _ => by rw [show time p j+2*k+1=a+2*(2*p+4*j+k)+1 by dsimp [time]; omega]; apply black)
      (by rw [show time p j+2=a+4*(p+2*j)+2 by dsimp [time]; omega]; apply off)
      (by rw [show time p j+6=a+4*(p+2*j+1)+2 by dsimp [time]; omega]; apply off)
    rw [show time p (j+1)=time p j+8 by dsimp [time]; omega]
    exact e
  obtain ⟨N,hN⟩ := S 0
  obtain ⟨M,hM⟩ := S 1
  have splitPhase (t : Nat) (ht : a≤t) : ∃ k, t=a+2*k ∨ t=a+2*k+1 := by
    exact ⟨(t-a)/2,by omega⟩
  have cp : EventuallyPeriodic (fun t => cell t 0) := by
    refine ⟨a,2,by decide,fun t ht => ?_⟩
    change cell (t+2) 0=cell t 0
    obtain ⟨k,rfl|rfl⟩ := splitPhase t ht
    · rw [show a+2*k+2=a+2*(k+1) by omega,white,white]
    · rw [show a+2*k+1+2=a+2*(k+1)+1 by omega,black,black]
  apply selected_aperiodic cp ⟨a,fun t ht h => by
    obtain ⟨k,rfl|rfl⟩ := splitPhase t ht
    · apply black
    · rw [black] at h; contradiction⟩
  have readBlack (k : Nat) : selected (a+2*k+1)=false := by
    have next : cell (a+2*k+1+1) 0=false := by rw [show a+2*k+1+1=a+2*(k+1) by omega,white]
    simp [selected,exposed,source,black,next]
  have readWhite (k : Nat) := white_read (a+2*k) (white k) (black k)
  refine ⟨a+8*(N+M+1),8,by decide,fun t ht => ?_⟩
  obtain ⟨k,rfl|rfl⟩ := splitPhase t (by omega)
  · rw [show a+2*k+8=a+2*(k+4) by omega,readWhite,readWhite]
    let j := k/4
    rcases (by dsimp [j]; omega : k=4*j ∨ k=4*j+2 ∨ k=2*(k/2)+1) with h|h|h
    · rw [show a+2*(k+4)=time 0 (j+1) by dsimp [time]; omega,
          show a+2*k=time 0 j by dsimp [time]; omega]
      exact hN j (by dsimp [j]; omega)
    · rw [show a+2*(k+4)=time 1 (j+1) by dsimp [time]; omega,
          show a+2*k=time 1 j by dsimp [time]; omega]
      exact hM j (by dsimp [j]; omega)
    · have zero (s : Nat) : hit (strip (a+4*s+2))=false := by
        cases e : hit (strip (a+4*s+2)) with
        | true => exact False.elim (off _ ((mark _).mp e))
        | false => rfl
      rw [show a+2*(k+4)=a+4*(k/2+2)+2 by omega,show a+2*k=a+4*(k/2)+2 by omega,zero,zero]
  · rw [show a+2*k+1+8=a+2*(k+4)+1 by omega,readBlack,readBlack]

/-- Under an alternating singleton center the seven-cell word occurs after
every cutoff in each of the two white time classes modulo four. -/
theorem both_white_phases (a : Nat) (white : ∀ k, cell (a+2*k) 0=false)
    (black : ∀ k, cell (a+2*k+1) 0=true) (N : Nat) (p : Fin 2) :
    ∃ k, N≤k ∧ wordAt (a+4*k+2*p.val) := by
  let b := a+4*N+2+2*p.val
  obtain ⟨k,hm⟩ := phase_hit b
    (fun i => by rw [show b+2*i=a+2*(2*N+1+p.val+i) by dsimp [b]; omega]; apply white)
    (fun i => by rw [show b+2*i+1=a+2*(2*N+1+p.val+i)+1 by dsimp [b]; omega]; apply black)
  let j := 2*(N+k+1)+p.val
  have eq : b+4*k+2=a+2*j := by dsimp [b,j]; omega
  rw [eq] at hm
  refine ⟨N+k+1,by omega,?_⟩
  rw [show a+4*(N+k+1)+2*p.val=a+2*j by dsimp [j]; omega]
  exact (word_iff_marker _ (white j) (black j)
    (by rw [show a+2*j+2=a+2*(j+1) by omega]; apply white)
    (by rw [show a+2*j+3=a+2*(j+1)+1 by omega]; apply black)
    (by rw [show a+2*j+4=a+2*(j+2) by omega]; apply white)).mpr hm

end Ruliology.CellularAutomata.Rule30EventReturns
