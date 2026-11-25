module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30MaskedJen
public import Ruliology.CellularAutomata.Rule30Realization

/-! Temporal segments, the single-seed horizontal language, and the phase-counting argument shared by both certificates. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity

def segment (f : Nat → Bool) (t : Nat) : Nat → List Bool
  | 0 => []
  | n+1 => f t :: segment f (t+1) n

end Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity

namespace Ruliology.CellularAutomata.Rule30HorizontalDiversity
open Ruliology.CellularAutomata Rule30Jen Rule30MaskedJen Rule30Realization Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity

/-- The singleton row on sites 0 through -w, in order from the center outward. -/
def row (w t : Nat) : List Bool :=
  (List.range (w+1)).map (fun k : Nat => cell t (-(k:Int)))

/-- All length-n binary words, once each. -/
def binaryWords : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (binaryWords n).map (false :: ·) ++ (binaryWords n).map (true :: ·)

private theorem mem_binary (xs : List Bool) : xs ∈ binaryWords xs.length := by
  induction xs with
  | nil => simp [binaryWords]
  | cons b bs ih => cases b <;> simp [binaryWords,ih]

private theorem binary_nodup (n : Nat) : (binaryWords n).Nodup := by
  induction n with
  | zero => simp [binaryWords]
  | succ n ih =>
    rw [binaryWords,List.nodup_append]
    constructor
    · apply List.pairwise_map.mpr
      exact ih.imp (fun h eq => h (List.cons.inj eq).2)
    constructor
    · apply List.pairwise_map.mpr
      exact ih.imp (fun h eq => h (List.cons.inj eq).2)
    · intro a ha b hb eq
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
      cases eq

/-- The horizontal language of the singleton on [-w,0]. -/
noncomputable def language (w : Nat) : List (List Bool) := by
  classical
  exact (binaryWords (w+1)).filter (fun v => decide (∃ t, row w t = v))

/-- The exact number of distinct horizontal words seen at any singleton age. -/
noncomputable def H (w : Nat) : Nat := (language w).length

theorem mem_language {v : List Bool} {w : Nat} :
    v ∈ language w ↔ ∃ t, row w t = v := by
  classical
  simp only [language,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
  rintro ⟨t,rfl⟩
  have h := mem_binary (row w t)
  simpa only [row,List.length_map,List.length_range] using h

private theorem language_nodup (w : Nat) : (language w).Nodup := by
  classical
  exact List.Pairwise.filter _ (binary_nodup _)

/-- Any list covering all observed rows bounds their exact number. -/
theorem count_le_cover {w : Nat} {L : List (List Bool)}
    (covers : ∀ t, row w t ∈ L) : H w ≤ L.length := by
  apply (language_nodup w).length_le_of_subset
  intro v hv
  obtain ⟨t,rfl⟩ := mem_language.mp hv
  exact covers t

private def clock (w t : Nat) := segment (fun k => cell k 0) t w
private def mask (w t : Nat) := segment (orCol 0) t w

private theorem segment_length (f : Nat → Bool) (t n : Nat) : (segment f t n).length = n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity.segment, ih]

private theorem segment_eq {f : Nat → Bool} {a b n : Nat}
    (h : ∀ k, k<n → f (a+k) = f (b+k)) : segment f a n = segment f b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity.segment,List.cons.injEq]
    refine ⟨by simpa using h 0 (by omega),ih ?_⟩
    intro k hk
    simpa only [show a+1+k=a+(k+1) by omega,show b+1+k=b+(k+1) by omega] using h (k+1) (by omega)

private theorem segment_at {f : Nat → Bool} {a b n : Nat} (h : segment f a n = segment f b n)
    (k : Nat) (hk : k<n) : f (a+k) = f (b+k) := by
  induction n generalizing a b k with
  | zero => omega
  | succ n ih =>
    have hh := List.cons.inj h
    cases k with
    | zero => simpa using hh.1
    | succ k =>
      simpa only [show a+(k+1)=a+1+k by omega,show b+(k+1)=b+1+k by omega] using
        ih hh.2 k (by omega)

private theorem rows_eq {w t u : Nat} (hc : clock (w+1) t = clock (w+1) u)
    (hm : mask w t = mask w u) : row w t = row w u := by
  apply List.map_congr_left
  intro k hk
  have h := (determine (i:=0) w (fun a ha => segment_at hc a (by omega))
    (fun a ha => segment_at hm a ha) k 0 (by have := List.mem_range.mp hk; omega)).1
  simpa using h

/-- Pick one singleton age for each nonempty observation class. -/
private noncomputable def decode (w : Nat) (c m : List Bool) : List Bool :=
  row w (Classical.epsilon (fun t => clock (w+1) t = c ∧ mask w t = m))

private theorem decode_row (w t : Nat) : decode w (clock (w+1) t) (mask w t) = row w t := by
  have h : ∃ s, clock (w+1) s = clock (w+1) t ∧ mask w s = mask w t := ⟨t,rfl,rfl⟩
  have spec := Classical.epsilon_spec h
  exact rows_eq spec.1 spec.2

def Covers (cand : List Bool → List (List Bool)) : Prop :=
  ∀ (x : Int → Bool) (t n : Nat),
    segment (fun k => evol x k 0 || evol x k 1) t n ∈
      cand (segment (fun k => evol x k 0) t n)

private noncomputable def phaseCover (cand : List Bool → List (List Bool)) (w b : Nat) :=
  (cand (clock w b)).map (decode w (clock (w+1) b))

private theorem phase_size (cand : List Bool → List (List Bool)) {budget : Nat → Nat}
    (bound : ∀ c, (cand c).length ≤ budget c.length) (w b : Nat) :
    (phaseCover cand w b).length ≤ budget w := by
  simpa only [phaseCover,List.length_map,clock,segment_length] using bound (clock w b)

private theorem phase_mem (cand : List Bool → List (List Bool))
    (covers : Covers cand) {T P : Nat} (per : ∀ t, T≤t → cell (t+P) 0=cell t 0)
    (w b k : Nat) (hb : T≤b) : row w (b+k*P) ∈ phaseCover cand w b := by
  have same (n : Nat) : clock n (b+k*P) = clock n b := by
    apply segment_eq
    intro a _
    rw [show b+k*P+a=b+a+k*P by omega]
    exact periodic_mul (f:=fun t => cell t 0) per k (b+a) (by omega)
  have hm := covers seed (b+k*P) w
  simp only [evol_seed] at hm
  change mask w (b+k*P) ∈ cand (clock w (b+k*P)) at hm
  rw [same] at hm
  refine List.mem_map.mpr ⟨_,hm,?_⟩
  rw [← same (w+1)]
  exact decode_row _ _

private theorem total_size (cand : List Bool → List (List Bool)) {budget : Nat → Nat}
    (bound : ∀ c, (cand c).length ≤ budget c.length) (T w m : Nat) :
    ((List.range m).flatMap (fun r => phaseCover cand w (T+r))).length ≤ m * budget w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,List.length_append,Nat.succ_mul]
    exact Nat.add_le_add ih (phase_size cand bound w (T+m))

theorem cover_of_channel (cand : List Bool → List (List Bool)) {budget : Nat → Nat}
    (bound : ∀ c, (cand c).length ≤ budget c.length) (covers : Covers cand) {T P : Nat} (hp : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0) (w : Nat) :
    ∃ L : List (List Bool), L.length ≤ T + P*(budget w) ∧ ∀ t, row w t ∈ L := by
  let front := (List.range T).map (row w)
  let phases := (List.range P).flatMap (fun r => phaseCover cand w (T+r))
  refine ⟨front ++ phases,?_,?_⟩
  · simp only [front,List.length_append,List.length_map,List.length_range]
    exact Nat.add_le_add_left (total_size cand bound T w P) T
  · intro t
    by_cases small : t<T
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨t,List.mem_range.mpr small,rfl⟩)
    · apply List.mem_append_right
      let r := (t-T)%P
      let k := (t-T)/P
      have split : T+r+k*P=t := by
        have e := Nat.mod_add_div (t-T) P
        dsimp [r,k]
        rw [Nat.mul_comm _ P]
        omega
      exact List.mem_flatMap.mpr ⟨r,List.mem_range.mpr (Nat.mod_lt _ hp),split ▸ phase_mem cand covers per w (T+r) k (by omega)⟩


/-- Growth can be witnessed entirely by finite lists of ages with pairwise distinct rows. -/
theorem growth_iff_samples (numerator denominator : Nat) :
    (∀ A : Nat, ∃ w, A*numerator^w < H w*denominator^w) ↔
    ∀ A : Nat, ∃ (w : Nat) (ages : List Nat),
      (ages.map (row w)).Nodup ∧ A*numerator^w < ages.length*denominator^w := by
  classical
  constructor
  · intro growth A
    obtain ⟨w,large⟩ := growth A
    let age := fun v : List Bool => Classical.epsilon (fun t => row w t = v)
    let ages := (language w).map age
    have recovers : ages.map (row w) = language w := by
      rw [show ages.map (row w) = (language w).map (fun v => row w (age v)) by simp [ages,List.map_map,Function.comp_def]]
      calc
        _ = (language w).map id := List.map_congr_left (fun v hv => Classical.epsilon_spec (mem_language.mp hv))
        _ = _ := List.map_id _
    refine ⟨w,ages,recovers ▸ language_nodup w,?_⟩
    simpa [ages,H] using large
  · intro samples A
    obtain ⟨w,ages,distinct,large⟩ := samples A
    have sub : ages.map (row w) ⊆ language w := by
      intro v hv
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hv
      exact mem_language.mpr ⟨t,rfl⟩
    have bound : ages.length ≤ H w := by
      simpa only [List.length_map,H] using distinct.length_le_of_subset sub
    exact ⟨w,Nat.lt_of_lt_of_le large (Nat.mul_le_mul_right _ bound)⟩

/-- Exact horizontal vocabulary is bounded by the phase cover including all transient ages. -/
theorem horizontal_count_of_channel (cand : List Bool → List (List Bool)) {budget : Nat → Nat}
    (bound : ∀ c, (cand c).length ≤ budget c.length) (covers : Covers cand) {T P : Nat} (hp : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0) (w : Nat) :
    H w ≤ T + P*(budget w) := by
  obtain ⟨L,cap,covers⟩ := cover_of_channel cand bound covers hp per w
  exact Nat.le_trans (count_le_cover covers) cap


end Ruliology.CellularAutomata.Rule30HorizontalDiversity
