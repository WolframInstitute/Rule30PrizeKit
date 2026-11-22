module

public import Ruliology.CellularAutomata.Rule30LateObservation
public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30LightCone

/-!
# Recovering a previous white-center reading from two singleton ages

For every proposed center period P, there are two late white-center ages
with opposite previous right readings, equal ensuing left windows of any
prescribed width, and the same future center forever. Their times can
agree modulo any auxiliary clock. A finite reader recovering the earlier
right bit from these observations on the singleton would prove Problem 1.
For arbitrary finite seeds, even supplying a two-sided window fails.

At a white center tick call the bit at site +1 the reading. Under eventual
alternation, arbitrarily far into the actual singleton trajectory there must
be two opposite readings followed by the same arbitrarily long word of
readings. At the two initial white ticks sites −1 and −2 are interchanged.
Starting at site −3 the rows must already agree for an arbitrarily prescribed
distance to the left. Both moving edge words can simultaneously agree to
any prescribed depth and then continue to agree after every common shift.

This necessary condition concerns the row interior. Its time bound is
exponential in the number of common future readings.

Contributed by Troy Lowry with OpenAI Codex.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30PastSwap

open Rule30Jen
abbrev Alt (T : Nat) := ∀ k, cell (T+2*k) 0 = true ∧ cell (T+2*k+1) 0 = false
def white (T i : Nat) := T+2*i+1
def reading (T i : Nat) := cell (white T i) 1

private def block (u : Nat → Bool) (i k : Nat) :=
  (List.range k).map (fun a => u (i+a))

private theorem block_agree {u : Nat → Bool} {i j k : Nat}
    (eqb : block u i k = block u j k) (a : Nat) (ha : a < k) : u (i+a) = u (j+a) := by
  have h := congrArg (fun l : List Bool => l[a]?) eqb
  simpa [block, List.getElem?_map, List.getElem?_range, ha] using h

private theorem branch_of_clock (word : Nat → Bool) (M K Q L : Nat) (phase : 0 < Q)
    (clock : ∀ d, 0 < d → Q ∣ d → d ≤ Q*2^K →
      (∀ s, M ≤ s → s < M+L → word s=word (s+d)) → False) :
    ∃ i j, M ≤ i ∧ i < j ∧ Q ∣ j-i ∧ j ≤ M+L+Q*2^K ∧ word i ≠ word j ∧
      ∀ a < K, word (i+1+a) = word (j+1+a) := by
  classical
  let B := M+L
  have hB : B=M+L := rfl
  obtain ⟨u,v,uv,cap,same⟩ := pigeonhole K
    (fun h => block (word) (B+Q*h+1) K) (by intro h; simp [block])
  let m := Q*u
  let n := Q*v
  have lt : m<n := Nat.mul_lt_mul_of_pos_left uv phase
  have small : n ≤ Q*2^K := Nat.mul_le_mul_left Q cap
  let d := n-m
  have hd : d=n-m := rfl
  have pos : 0 < d := by omega
  have divides : Q ∣ d := ⟨v-u, (Nat.mul_sub _ _ _).symm⟩
  have start : ∀ a < K, word (B+m+1+a) = word (B+m+1+d+a) := by
    rw [show B+m+1+d=B+n+1 by omega]; exact block_agree same
  apply Classical.byContradiction
  intro no
  have pred (s : Nat) (lower : M ≤ s) (upper : s ≤ B+m)
      (h : ∀ a < K, word (s+1+a)=word (s+1+d+a)) :
      word s = word (s+d) := by
    apply Classical.byContradiction; intro neq
    apply no
    refine ⟨s,s+d,lower,by omega,by simpa using divides,by omega,neq,?_⟩
    intro a ha; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h a ha
  have back (z : Nat) (hz : z ≤ B+m+1-M) :
      ∀ a < K, word (B+m+1-z+a) = word (B+m+1-z+d+a) := by
    induction z with
    | zero => simpa using start
    | succ z ih =>
      let s := B+m+1-(z+1)
      have es : s=B+m+1-(z+1) := rfl
      have ei : B+m+1-z=s+1 := by omega
      have h := ih (by omega)
      rw [ei] at h
      intro a ha
      cases a with
      | zero => simpa [s] using pred s (by omega) (by omega) h
      | succ a =>
        have e := h a (by omega)
        simpa only [← es, show s+(a+1)=s+1+a by omega,
          show s+d+(a+1)=s+1+d+a by omega] using e
  apply clock d pos divides (by omega)
  intro k hk stop
  apply pred k hk (by omega)
  have b := back (B+m-k) (by omega)
  rwa [show B+m+1-(B+m-k)=k+1 by omega] at b

/-- A future return exists with opposite previous readings. The cutoff and
    the length of common future are arbitrary. The upper bound counts white ticks. -/
theorem branching_return {T : Nat} (alt : Alt T) (M K Q : Nat) (phase : 0 < Q) :
    ∃ i j, M ≤ i ∧ i < j ∧ Q ∣ j-i ∧ j ≤ 2*M+T+3*(Q*2^K)+2 ∧ reading T i ≠ reading T j ∧
      ∀ a < K, reading T (i+1+a) = reading T (j+1+a) := by
  let L := M+T+2*(Q*2^K)+2
  have hL : L=M+T+2*(Q*2^K)+2 := rfl
  have result := branch_of_clock (reading T) M K Q L phase (by
    intro d pos _ small periodic
    have impossible := Rule30ZeroBoundary.alternating_right_col1_clock alt
      (k₀:=M) (ℓ:=L) (p:=d) pos (by
        intro k hk stop
        exact (periodic k hk (by omega)).symm)
    omega)
  rwa [show M+L+Q*2^K = 2*M+T+3*(Q*2^K)+2 by omega] at result

private theorem colors {T : Nat} (h : Alt T) (i : Nat) :
    cell (white T i) 0 = false ∧ cell (white T i+1) 0 = true := by
  exact ⟨(h i).2, by rw [show white T i+1=T+2*(i+1) by unfold white; omega]; exact (h _).1⟩

private theorem next_white (T i : Nat) : white T i+2 = white T (i+1) := by unfold white; omega

private theorem left1 {T : Nat} (h : Alt T) (i : Nat) :
    cell (white T i) (-1) = !reading T i := by
  have e := cell_left (white T i) 0
  change cell (white T i) (-1) = xor (cell (white T i+1) 0)
    (cell (white T i) 0 || reading T i) at e
  rw [(colors h i).1,(colors h i).2] at e
  simpa using e

private theorem black_left1 {T : Nat} (h : Alt T) (i : Nat) :
    cell (white T i+1) (-1) = true := by
  have e := cell_left (white T i+1) 0
  simpa [next_white,(colors h i).2,(colors h (i+1)).1,
    show white T i+1+1=white T (i+1) from next_white T i] using e

private theorem shallow {T : Nat} (h : Alt T) (i : Nat) :
    cell (white T i) (-2) = reading T i ∧
    cell (white T i) (-3) = !reading T (i+1) := by
  let w := white T i
  have e₂ := cell_left w (-1)
  change cell w (-2) = xor (cell (w+1) (-1)) (cell w (-1) || cell w 0) at e₂
  rw [black_left1 h i,left1 h i,(colors h i).1] at e₂
  have x₂ : cell w (-2) = reading T i := by simpa using e₂
  have f₂ := cell_left (w+1) (-1)
  change cell (w+1) (-2) = xor (cell (w+2) (-1)) (cell (w+1) (-1) || cell (w+1) 0) at f₂
  rw [show w+2=white T (i+1) from next_white T i, left1 h (i+1),black_left1 h i] at f₂
  have y₂ : cell (w+1) (-2) = reading T (i+1) := by simpa using f₂
  have e₃ := cell_left w (-2)
  change cell w (-3) = xor (cell (w+1) (-2)) (cell w (-2) || cell w (-1)) at e₃
  rw [y₂,x₂,left1 h i] at e₃
  exact ⟨x₂, by simpa using e₃⟩

private theorem isolated {T : Nat} (h : Alt T) (i : Nat) (kick : reading T i=true) :
    reading T (i+1)=false := by
  let w := white T i
  have one : cell (w+1) 1 = true := by
    change rule (cell w 0) (reading T i) (cell w 2) = true
    simp [rule,kick,(colors h i).1,w]
  rw [reading, ← next_white]
  change rule (cell (w+1) 0) (cell (w+1) 1) (cell (w+1) 2) = false
  simp [rule,one,(colors h i).2,w]

private theorem common_black_row {T : Nat} (h : Alt T) (i j K : Nat)
    (same : ∀ a<K, reading T (i+1+a)=reading T (j+1+a)) :
    Rule30LateObservation.Agree (cell (white T i+1)) (cell (white T j+1)) (-(2*K : Nat)) 0 := by
  let time (i : Nat) := white T i+1
  have black (i a : Nat) : cell (time i+2*a) 0 = true := by
    rw [show time i+2*a=T+2*(i+1+a) by dsimp [time,white]; omega]; exact (h _).1
  have odd (i a : Nat) : time i+(2*a+1) = white T (i+1+a) := by dsimp [time,white]; omega
  have obs : Rule30LateObservation.Observed (Rule30LateObservation.fromAge (time i))
      (Rule30LateObservation.fromAge (time j)) 0 (2*K) := by
    constructor
    · intro s _
      simp only [Nat.zero_add]
      change cell (time i+s) 0 = cell (time j+s) 0
      obtain ⟨a, rfl | rfl⟩ : ∃ a, s=2*a ∨ s=2*a+1 := ⟨s/2,by omega⟩
      · rw [black,black]
      · rw [odd,odd,(colors h _).1,(colors h _).1]
    · intro s hs
      simp only [Nat.zero_add]
      change (cell (time i+s) 0 || cell (time i+s) 1) = (cell (time j+s) 0 || cell (time j+s) 1)
      obtain ⟨a, rfl | rfl⟩ : ∃ a, s=2*a ∨ s=2*a+1 := ⟨s/2,by omega⟩
      · simp [black]
      · rw [odd,odd,(colors h _).1,(colors h _).1]
        exact congrArg (fun b => false || b) (same a (by omega))
  exact Rule30LateObservation.observed_row _ _ (Rule30LateObservation.singleton_history (time i))
    (Rule30LateObservation.singleton_history (time j)) 0 (2*K) obs

/-- The two five-cell words from position −3 through +1 are 10100 and 11001
    in some order. Their left contexts match up to and including −(2K+1). -/
def Swap (T K i j : Nat) : Prop :=
      reading T i ≠ reading T j ∧
      (∀ a<K, reading T (i+1+a)=reading T (j+1+a)) ∧
      (∀ k, k=i ∨ k=j → cell (white T k) (-3)=true ∧
        cell (white T k) (-2)=reading T k ∧ cell (white T k) (-1)= !reading T k ∧
        cell (white T k) 0=false) ∧
      Rule30LateObservation.Agree (cell (white T i)) (cell (white T j)) (-(2*K+1 : Nat)) (-3)

theorem singleton_swap {T : Nat} (alt : Alt T) (M K Q : Nat) (size : 2 ≤ K) (phase : 0 < Q) :
    ∃ i j, M ≤ i ∧ i < j ∧ Q ∣ j-i ∧ j ≤ 2*M+T+3*(Q*2^K)+2 ∧ Swap T K i j := by
  obtain ⟨i,j,mi,lt,divides,bound,diff,same⟩ := branching_return alt M K Q phase
  have nextEq := same 0 (by omega)
  simp only [Nat.add_zero] at nextEq
  have zero : reading T (i+1)=false := by
    cases ei : reading T i
    · have ej : reading T j=true := by cases u : reading T j <;> simp_all
      exact nextEq.trans (isolated alt j ej)
    · exact isolated alt i ei
  have zi := (shallow alt i).2
  have zj := (shallow alt j).2
  rw [zero] at zi
  rw [← nextEq,zero] at zj
  refine ⟨i,j,mi,lt,divides,bound,diff,same,?_,?_⟩
  · intro k hk
    rcases hk with rfl | rfl
    · exact ⟨zi,(shallow alt _).1,left1 alt _,(colors alt _).1⟩
    · exact ⟨zj,(shallow alt _).1,left1 alt _,(colors alt _).1⟩
  · have out := common_black_row alt i j K same
    have three : cell (white T i) (-3) = cell (white T j) (-3) := zi.trans zj.symm
    have four : cell (white T i) (-4) = cell (white T j) (-4) := by
      change cell (white T i) ((-3)-1) = cell (white T j) ((-3)-1)
      rw [cell_left,cell_left (white T j),out (-3) (by omega) (by decide),zi,zj]; rfl
    have pair (s : Nat) (hs : (s:Int)+4 ≤ 2*(K:Int)+1) :
        cell (white T i) (-3-s) = cell (white T j) (-3-s) ∧
        cell (white T i) (-4-s) = cell (white T j) (-4-s) := by
      induction s with
      | zero => simpa using And.intro three four
      | succ s ih =>
        obtain ⟨a,b⟩ := ih (by omega)
        rw [show -3-((s+1:Nat):Int) = -4-s by omega]
        refine ⟨b,?_⟩
        rw [show -4-((s+1:Nat):Int) = (-4-s)-1 by omega,cell_left,cell_left (white T j),
          out (-4-s) (by omega) (by omega),b,show (-4-(s:Int))+1 = -3-s by omega,a]
    intro p hl hr
    by_cases e : p = -3
    · simpa [e] using three
    · let s := (-4-p).toNat
      have es : -4-(s:Int)=p := by dsimp [s]; omega
      simpa only [es] using (pair s (by omega)).2

private theorem settled (W : Nat) :
    ∃ N, ∀ k ≤ W, ∀ t ≥ N, Rule30Diagonals.D k (t+2^k) = Rule30Diagonals.D k t := by
  induction W with
  | zero =>
    obtain ⟨N,h⟩ := Rule30Diagonals.D_periodic 0
    refine ⟨N,?_⟩
    intro k hk
    obtain rfl : k=0 := by omega
    exact h
  | succ W ih =>
    obtain ⟨N,h⟩ := ih
    obtain ⟨N',h'⟩ := Rule30Diagonals.D_periodic (W+1)
    refine ⟨max N N',?_⟩
    intro k hk t ht
    by_cases small : k≤W
    · exact h k small t (by omega)
    · obtain rfl : k=W+1 := by omega
      exact h' t (by omega)

private theorem phase_eq (f : Nat → Bool) (N P i j : Nat)
    (period : ∀ t ≥ N, f (t+P)=f t) (late : N≤i) (order : i≤j) (delta : P ∣ j-i) :
    f i = f j := by
  obtain ⟨m,hm⟩ := delta
  have loop (k : Nat) : f (i+P*k)=f i := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ,← Nat.add_assoc,period _ (by omega),ih]
  rw [show j=i+P*m by omega,loop]

/-- Simultaneously with the interior swap, the rows have the same singleton
    edge words through any prescribed inward depth, at both moving edges.
    The diagonal equalities also persist after every common time shift. -/
theorem same_edges_swap {T : Nat} (alt : Alt T) (M K W : Nat) (size : 2 ≤ K) :
    ∃ i j, M ≤ i ∧ i < j ∧ Swap T K i j ∧ ∀ k ≤ W, ∀ s : Nat,
      Rule30Diagonals.D k (white T i+s) = Rule30Diagonals.D k (white T j+s) ∧
      Rule30Diagonals.R k (white T i+s) = Rule30Diagonals.R k (white T j+s) := by
  obtain ⟨N,h⟩ := settled W
  obtain ⟨i,j,mi,lt,phase,_,swap⟩ := singleton_swap alt (max M N) K (2^W) size (Nat.two_pow_pos W)
  refine ⟨i,j,by omega,lt,swap,?_⟩
  intro k hk s
  have divs : 2^k ∣ j-i := Nat.dvd_trans (Nat.pow_dvd_pow 2 hk) phase
  have dw : white T j+s-(white T i+s)= (j-i)*2 := by unfold white; omega
  have timediv : 2^k ∣ white T j+s-(white T i+s) := by
    rw [dw]; exact Nat.dvd_trans divs (Nat.dvd_mul_right _ _)
  have ordered : white T i+s ≤ white T j+s := by unfold white; omega
  exact ⟨phase_eq _ N _ _ _ (h k hk) (by unfold white; omega) ordered timediv,
    phase_eq _ 0 _ _ _ (fun t _ => Rule30Diagonals.R_periodic k t)
      (Nat.zero_le _) ordered timediv⟩

def mask (t : Nat) := cell t 0 || cell t 1

/-- At the two white times the earlier right readings and both earlier
    left neighbors differ. At their next times the left windows coincide. -/
def PastFork (K i j : Nat) : Prop :=
  cell i 0 = false ∧ cell j 0 = false ∧ cell i 1 ≠ cell j 1 ∧
  cell i (-1) ≠ cell j (-1) ∧ cell i (-2) ≠ cell j (-2) ∧
  (∀ a < K, mask (i+1+a)=mask (j+1+a)) ∧
  Rule30LateObservation.Agree (cell (i+1)) (cell (j+1)) (-(K:Int)) 0

/-- Every proposed center period forces arbitrarily wide forks on the
    genuine singleton, including for observation times in the same phase
    of any auxiliary clock Q. The second time has an explicit finite bound. -/
theorem periodic_fork {T P : Nat} (pos : 0 < P)
    (per : ∀ t ≥ T, cell (t+P) 0 = cell t 0)
    (M K Q : Nat) (late : T ≤ M) (width : 1 ≤ K) (clock : 0 < Q) :
    ∃ i j, M ≤ i ∧ i < j ∧ P*Q ∣ j-i ∧ j ≤ 2*M+2*((P*Q)*2^K) ∧
      (∀ s, cell (i+s) 0 = cell (j+s) 0) ∧ PastFork K i j := by
  let S := P*Q
  let L := M+S*2^K
  have hL : L=M+S*2^K := rfl
  have hP : P ∣ S := Nat.dvd_mul_right P Q
  have cent (i j : Nat) (hi : M ≤ i) (hij : i ≤ j) (hd : S ∣ j-i) (s : Nat) :
      cell (i+s) 0 = cell (j+s) 0 := by
    apply phase_eq (fun t => cell t 0) T P _ _ per (by omega) (by omega)
    rw [show j+s-(i+s)=j-i by omega]; exact Nat.dvd_trans hP hd
  obtain ⟨i,j,mi,lt,divides,bound,diff,future⟩ :=
    branch_of_clock mask M K S L (Nat.mul_pos pos clock) (by
      intro d hd ds small same
      have ages : M < M+d := by omega
      have obs : Rule30LateObservation.Observed (Rule30LateObservation.fromAge M)
          (Rule30LateObservation.fromAge (M+d)) 0 (M+d) := by
        constructor
        · intro a _; simp only [Nat.zero_add]
          exact cent M (M+d) (by omega) (by omega) (by simpa using ds) a
        · intro a ha
          simp only [Nat.zero_add]
          change mask (M+a) = mask (M+d+a)
          rw [show M+d+a=M+a+d by omega]; exact same _ (by omega) (by omega)
      have e := Rule30LateObservation.observed_row _ _
        (Rule30LateObservation.singleton_history M) (Rule30LateObservation.singleton_history (M+d))
        0 (M+d) obs (-((M+d:Nat):Int)) (by omega) (by omega)
      change cell M _ = cell (M+d) _ at e
      rw [cell_left_edge,cell_eq_false_of_lt _ _ (by omega)] at e
      contradiction)
  have ce := cent i j mi (by omega) divides
  have c0 : cell i 0=cell j 0 := by simpa using ce 0
  have wi : cell i 0=false := by
    cases e : cell i 0
    · rfl
    · exact False.elim (diff (by simp [mask,e,← c0]))
  have wj := c0.symm.trans wi
  have dr : cell i 1 ≠ cell j 1 := by simpa [mask,wi,wj] using diff
  have obs : Rule30LateObservation.Observed (Rule30LateObservation.fromAge (i+1))
      (Rule30LateObservation.fromAge (j+1)) 0 K := by
    constructor
    · intro a _; simp only [Nat.zero_add,Rule30LateObservation.fromAge,Nat.add_assoc]; exact ce (1+a)
    · intro a ha; simp only [Nat.zero_add]; exact future a ha
  have out := Rule30LateObservation.observed_row _ _
    (Rule30LateObservation.singleton_history (i+1)) (Rule30LateObservation.singleton_history (j+1)) 0 K obs
  change Rule30LateObservation.Agree (cell (i+1)) (cell (j+1)) (-(K:Int)) 0 at out
  have d₁ : cell i (-1) ≠ cell j (-1) := by
    change cell i ((0:Int)-1) ≠ cell j ((0:Int)-1)
    rw [cell_left,cell_left j,ce 1,wi,wj]
    cases cell (j+1) 0 <;> simpa using dr
  have d₂ : cell i (-2) ≠ cell j (-2) := by
    change cell i ((-1:Int)-1) ≠ cell j ((-1:Int)-1)
    rw [cell_left,cell_left j,out (-1) (by omega) (by decide)]
    change xor (cell (j+1) (-1)) (cell i (-1) || cell i 0) ≠
      xor (cell (j+1) (-1)) (cell j (-1) || cell j 0)
    rw [wi,wj]; cases cell (j+1) (-1) <;> simpa using d₁
  exact ⟨i,j,mi,lt,divides,by change j ≤ 2*M+2*(S*2^K); omega,ce,wi,wj,dr,d₁,d₂,future,out⟩

/-- A finite reader of the previous white-tick bit on the singleton's tail
    would prove Problem 1. It may use the time phase, any fixed forward
    center segment, and a left spatial window at the next tick. -/
theorem problem1_of_past_reader (M K Q H : Nat) (width : 1 ≤ K) (clock : 0 < Q)
    (reader : ∀ i j, M ≤ i → i<j → Q ∣ j-i → cell i 0=false → cell j 0=false →
      (∀ s ≤ H, cell (i+s) 0=cell (j+s) 0) →
      Rule30LateObservation.Agree (cell (i+1)) (cell (j+1)) (-(K:Int)) 0 →
      cell i 1=cell j 1) : Rule30Prize.Problem1 := by
  rintro ⟨T,P,pos,per⟩
  obtain ⟨i,j,mi,lt,divides,_,same,wi,wj,dr,_,_,_,out⟩ :=
    periodic_fork pos per (max T M) K Q (by omega) width clock
  exact dr (reader i j (by omega) lt (Nat.dvd_trans (Nat.dvd_mul_left Q P) divides)
    wi wj (fun s _ => same s) out)

/-- In the packed zero-boundary dynamics the two low-bit patterns give
    exactly the same next row, for every finite continuation farther left.
    Bit zero denotes the cell one site left of the wall. -/
theorem packed_swap (z : Nat) :
    Rule30ZeroBoundary.IntegerForm.F (8*z+5) = Rule30ZeroBoundary.IntegerForm.F (8*z+6) := by
  apply Nat.eq_of_testBit_eq
  intro k
  change (Rule30ZeroBoundary.IntegerForm.F (2^3*z+5)).testBit k =
    (Rule30ZeroBoundary.IntegerForm.F (2^3*z+6)).testBit k
  simp only [Rule30ZeroBoundary.IntegerForm.F,Nat.testBit_xor,Nat.testBit_or,
    Nat.testBit_shiftLeft,Nat.testBit_shiftRight,
    Nat.testBit_two_pow_mul_add z (i:=3) (b:=5) (by decide),
    Nat.testBit_two_pow_mul_add z (i:=3) (b:=6) (by decide)]
  by_cases small : k < 4
  · obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    all_goals simp <;> try rfl
  · simp [show ¬1+k<3 by omega,show ¬k<3 by omega,show ¬k-1<3 by omega]

section FiniteControl
open Rule30Realization (evol)
open Rule30ZeroBoundaryBarriers (evol_restart evol_shift_all)

def ring (w : Nat) (p : Int) := w.testBit (p%4).toNat

private theorem ring_check (u v n : Nat)
    (h : ∀ k : Fin 4, evol (ring u) n k.val=ring v k.val) : evol (ring u) n=ring v := by
  funext p
  let k : Fin 4 := ⟨(p%4).toNat, by omega⟩
  have ek : (k.val:Int)=p%4 := by dsimp [k]; omega
  let d := p-k.val
  have shift (s : Int) : ring u (s+d)=ring u s := by
    unfold ring; rw [show (s+d)%4=s%4 by dsimp [d]; omega]
  have e := evol_shift_all shift n (k.val:Int)
  rw [show (k.val:Int)+d=p by dsimp [d]; omega,h k] at e
  exact e.trans (by unfold ring; rw [show (k.val:Int)%4=p%4 by omega])

private theorem ring_after : evol (ring 12) 1=ring 7 := ring_check _ _ _ (by decide)
private theorem ring_seven : evol (ring 7) 7=ring 2 := ring_check _ _ _ (by decide)
private theorem ring_cycle : evol (ring 7) 8=ring 7 := ring_check _ _ _ (by decide)

private theorem add_time (x : Int → Bool) (a b : Nat) :
    evol x (a+b) = evol (evol x a) b := funext fun p => (evol_restart x a b p).symm

private theorem cycle_loop (q : Nat) : evol (ring 7) (8*q)=ring 7 := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ,add_time,ih,ring_cycle]

/-- On a single genuine Rule 30 orbit of spatial period four, the rows
    at times zero and a positive multiple of eight give different earlier
    right bits at white centers. Their entire next rows coincide. -/
theorem cyclic_parents (q : Nat) (pos : 0<q) :
    evol (ring 12) (8*q)=ring 2 ∧ evol (ring 12) (8*q+1)=evol (ring 12) 1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
  constructor
  · rw [show 8*(k+1)=1+8*k+7 by omega,add_time,add_time (ring 12) 1,ring_after,cycle_loop,ring_seven]
  · rw [show 8*(k+1)+1=1+8*(k+1) by omega,add_time,ring_after,cycle_loop]

private theorem late_window (y : Int → Bool) (M R : Nat) :
    ∃ (x : Int → Bool) (t B : Nat), M≤t ∧
      (∀ p : Int, p < -(B:Int) ∨ (B:Int)<p → x p=false) ∧
      Rule30LateObservation.Agree (evol x t) y (-(R:Int)) R := by
  let b := M+2*R+1
  let target : Int → Bool := fun p => y (p-R)
  obtain ⟨seed,supp,out⟩ := Rule30LightCone.root_block_leftmost_leaf_surjective b 1
    (fun _ => false) (Rule30LightCone.block b target 0) (Rule30LightCone.length_block _ _ _)
  let x := fun (p : Int) => seed (p+R)
  refine ⟨x,b,b+R,by dsimp [b]; omega,?_,?_⟩
  · intro p hp
    apply supp
    change p+(R:Int) < -(1:Int)*b ∨ (-(1:Int)+1)*b ≤ p+R
    rw [Int.neg_one_mul, show (-(1:Int)+1)=0 by decide,Int.zero_mul]; omega
  · intro p lo hi
    let i := (p+R).toNat
    have ei : (i:Int)=p+R := by dsimp [i]; omega
    have lt : i<b := by dsimp [b]; omega
    have e := congrArg (fun l : List Bool => l.getD i false) out
    simp only [Rule30LightCone.getD_block _ _ _ lt,Nat.one_mul,Int.zero_mul,Int.zero_add] at e
    have shift := evol_shift_all (x:=x) (x':=seed) (d:=(R:Int)) (fun _ => rfl) b p
    rw [← shift,← ei,e]
    unfold target; rw [ei]; congr 1; omega

/-- For ANY fixed cutoff, modulus, window width and finite forecast, a
    single finite seed realizes a counterexample to a seed-independent
    previous-bit reader. Even a two-sided next-row window can be supplied. -/
theorem finite_control (M K Q H : Nat) (pos : 0<Q) :
    ∃ (x : Int → Bool) (B i j : Nat),
      (∀ p : Int, p < -(B:Int) ∨ (B:Int)<p → x p=false) ∧
      M≤i ∧ i<j ∧ Q ∣ j-i ∧ evol x i 0=false ∧ evol x j 0=false ∧
      evol x i 1 ≠ evol x j 1 ∧ (∀ s ≤ H, evol x (i+s) 0=evol x (j+s) 0) ∧
      Rule30LateObservation.Agree (evol x (i+1)) (evol x (j+1)) (-(K:Int)) K := by
  let d := 8*Q
  let R := d+H+K+2
  obtain ⟨x,i,B,late,supp,win⟩ := late_window (ring 12) M R
  have copy (s : Nat) (p : Int) (lo : -(R:Int) ≤ p-s) (hi : p+s ≤ R) :
      evol x (i+s) p = evol (ring 12) s p := by
    rw [add_time]
    apply Rule30LightCone.evol_window
    intro j hj hj'; apply win <;> omega
  have at_zero (p : Int) (lo : -(R:Int)≤p) (hi : p≤R) : evol x i p=ring 12 p := by
    exact win p lo hi
  obtain ⟨second,next⟩ := cyclic_parents Q pos
  change evol (ring 12) d = ring 2 at second
  change evol (ring 12) (d+1) = evol (ring 12) 1 at next
  refine ⟨x,B,i,i+d,supp,late,by dsimp [d]; omega,by simp [d,Nat.dvd_mul_left],?_,?_,?_,?_,?_⟩
  · rw [at_zero 0 (by omega) (by omega)]; decide
  · rw [copy d 0 (by dsimp [R]; omega) (by dsimp [R]; omega),second]; decide
  · rw [at_zero 1 (by omega) (by dsimp [R]; omega),
        copy d 1 (by dsimp [R]; omega) (by dsimp [R]; omega),second]; decide
  · intro s hs
    rw [Nat.add_assoc,copy s 0 (by dsimp [R]; omega) (by dsimp [R]; omega),
        copy (d+s) 0 (by dsimp [R]; omega) (by dsimp [R]; omega)]
    cases s with
    | zero => rw [Nat.add_zero,second]; decide
    | succ k =>
      rw [show k+1=1+k by omega,show d+(1+k)=(d+1)+k by omega,
        add_time (ring 12) 1 k,add_time (ring 12) (d+1) k,next]
  · intro p lo hi
    rw [Nat.add_assoc,copy 1 p (by dsimp [R]; omega) (by dsimp [R]; omega),
        copy (d+1) p (by dsimp [R]; omega) (by dsimp [R]; omega),next]

end FiniteControl
end Ruliology.CellularAutomata.Rule30PastSwap
