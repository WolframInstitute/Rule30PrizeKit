module
public import Ruliology.CellularAutomata.Rule30SourceDensityRegion

/-! The number of ticks when two neighbours are both black equals the number of black-to-white
steps of the right column. Summing the one-step identities expresses the middle inequality's
slack in terms of colour repetitions and an endpoint correction. Bounded slack is equivalent
to eventual alternation, and on the single seed this is equivalent to eventual period two. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceDensityRegion
open Rule30Jen (rule cell)
open Rule30SourceObservables (source bit count)
private theorem eqs : ∀ a b c : Bool,
    bit a - bit (source a b) = bit (b && !rule a b c) ∧
    1-2*(bit a-bit (source a b))=bit (b==rule a b c)+bit (rule a b c)-bit b := by decide

def flats (u : History) (i : Int) (s n : Nat) :=
  count (fun t=>u (s+t) i == u (s+t+1) i) n
def falls (u : History) (i : Int) (s n : Nat) :=
  count (fun t=>u (s+t) i && !u (s+t+1) i) n

private theorem local_id {u} (hu : Evolution u) (j : Int) (t : Nat) :
    bit (u t j)-bit (source (u t j) (u t (j+1)))=bit (u t (j+1) && !u (t+1) (j+1)) ∧
    1-2*(bit (u t j)-bit (source (u t j) (u t (j+1))))=
       bit (u t (j+1)==u (t+1) (j+1))+bit (u (t+1) (j+1))-bit (u t (j+1)) := by
  rw [hu]
  simpa only [show j+1-1=j by omega,show j+1+1=j+2 by omega] using eqs (u t j) (u t (j+1)) (u t (j+2))

/-- The count of horizontal 11s is exactly the number of 1-to-0 transitions
through the right column. -/
theorem fall_count {u} (hu : Evolution u) (j : Int) (s n : Nat) :
    black u j s n-ends u j s n=falls u (j+1) s n := by
  induction n with
  | zero => simp [black,ends,falls,count]
  | succ n ih =>
    have h:=(local_id hu j (s+n)).1
    simp only [black,ends,falls,count] at ih ⊢
    omega

theorem middle_identity {u} (hu : Evolution u) (j : Int) (s n : Nat) :
    (n:Int)-2*(black u j s n-ends u j s n)=
      flats u (j+1) s n + bit (u (s+n) (j+1))-bit (u s (j+1)) := by
  induction n with
  | zero => simp [black,ends,flats,count]
  | succ n ih =>
    have h:=(local_id hu j (s+n)).2
    simp only [black,ends,flats,count,Int.natCast_succ,
      show s+(n+1)=s+n+1 by omega] at ih ⊢
    omega

private theorem bit01 (v : Bool) : 0 ≤ bit v ∧ bit v ≤ 1 := by cases v <;> decide
private theorem flat_monotone (u : History) (j : Int) {a b : Nat} (le : a≤b) :
    flats u j 0 a ≤ flats u j 0 b := by
  induction b with
  | zero => have : a=0 := by omega
            rw [this];omega
  | succ b ih =>
    by_cases eq : a=b+1
    · rw [eq];omega
    · have h:=ih (by omega)
      have inc:=bit01 (u b j==u (b+1) j)
      simp only [flats,count,Nat.zero_add] at h ⊢
      omega

def Alternates (f : Nat→Bool) : Prop := ∃ T, ∀ t,T≤t → f (t+1)=!f t

private theorem bool_flat (x y : Bool) : ¬y=(!x) ↔ x=y := by cases x <;> cases y <;> decide

theorem bounded_iff_alternates {u} (hu : Evolution u) (j : Int) :
    (∃ K : Int, ∀ n : Nat, (n:Int)-2*(black u j 0 n-ends u j 0 n) ≤ K) ↔
      Alternates (fun t=>u t (j+1)) := by
  constructor
  · rintro ⟨K,bounded⟩
    apply Classical.byContradiction
    intro deny
    have later (a : Nat) : ∃ t, a≤t ∧ u t (j+1)=u (t+1) (j+1) := by
      apply Classical.byContradiction
      intro no
      apply deny;refine ⟨a,fun t ht=>?_⟩
      apply Classical.byContradiction
      intro ne;exact no ⟨t,ht,(bool_flat _ _).mp ne⟩
    have many (k : Nat) : ∃ n, (k:Int)≤flats u (j+1) 0 n := by
      induction k with
      | zero => exact ⟨0,by simp [flats,count]⟩
      | succ k ih =>
        obtain ⟨a,ha⟩:=ih
        obtain ⟨t,ht,flat⟩:=later a
        have m:=flat_monotone u (j+1) ht
        refine ⟨t+1,?_⟩
        simp only [flats,count,Nat.zero_add] at m ha ⊢
        simp only [flat,beq_self_eq_true,bit,ite_true]
        omega
    obtain ⟨n,hn⟩:=many (K.toNat+3)
    have identity:=middle_identity hu j 0 n
    have lo:=bit01 (u n (j+1));have hi:=bit01 (u 0 (j+1))
    have b:=bounded n;simp only [Nat.zero_add] at identity;omega
  · rintro ⟨T,alt⟩
    have bound (n : Nat) : flats u (j+1) 0 n ≤ flats u (j+1) 0 T := by
      induction n with
      | zero => exact flat_monotone u _ (Nat.zero_le _)
      | succ n ih =>
        by_cases early : n+1≤T
        · exact flat_monotone u _ early
        · have e:=alt n (by omega)
          change u (n+1) (j+1)=!u n (j+1) at e
          have z : bit (u n (j+1)==u (n+1) (j+1))=0 := by rw [e];cases u n (j+1) <;> decide
          simpa only [flats,count,Nat.zero_add,z,Int.add_zero] using ih
    refine ⟨flats u (j+1) 0 T+1,fun n=>?_⟩
    have h:=middle_identity hu j 0 n;have b:=bound n
    have lo:=bit01 (u 0 (j+1));have hi:=bit01 (u n (j+1))
    simp only [Nat.zero_add] at h;omega

theorem singleton_middle_bounded_iff_period_two (j : Int) :
    (∃ K : Int, ∀ n : Nat, (n:Int)-2*(black cell j 0 n-ends cell j 0 n)≤K) ↔
    (∃ T, ∀ t, T≤t → cell (t+2) (j+1)=cell t (j+1)) := by
  rw [bounded_iff_alternates (u:=cell) (fun _ _=>rfl)]
  constructor
  · rintro ⟨T,h⟩;refine ⟨T,fun t ht=>?_⟩
    have a:=h t ht;have b:=h (t+1) (by omega)
    change cell (t+1) (j+1)=!cell t (j+1) at a
    change cell (t+2) (j+1)=!cell (t+1) (j+1) at b
    simp only [a,Bool.not_not] at b;exact b
  · rintro ⟨T,per⟩;refine ⟨T,fun t ht=>?_⟩
    apply Classical.byContradiction
    intro ne
    have eq:=(bool_flat _ _).mp ne
    have pair (k : Nat) : cell (t+k) (j+1)=cell t (j+1) ∧ cell (t+k+1) (j+1)=cell t (j+1) := by
      induction k with
      | zero => simp only [Nat.add_zero];exact ⟨trivial,eq.symm⟩
      | succ k ih =>
        have h:=per (t+k) (by omega)
        simpa only [show t+(k+1)=t+k+1 by omega,show t+k+1+1=t+k+2 by omega] using And.intro ih.2 (h.trans ih.1)
    apply Rule30Prize.no_column_eventually_constant (j+1)
    exact ⟨t,cell t (j+1),fun s hs=>by simpa only [show t+(s-t)=s by omega] using (pair (s-t)).1⟩

end Ruliology.CellularAutomata.Rule30SourceDensityRegion
