module

public import Ruliology.CellularAutomata.Rule30HorizontalWords
public import Mathlib.Tactic

/-!
# Exact strips beside a prescribed wall

A strip of d + 1 cells east of the wall, with the next cell free at every tick, reads exactly the physical OR words of length at
most d + 1, for every prescribed wall and every continuation of it (`exact_at_width`, `realize_word`).

Contributed by Gareth Herbert with Claude (Anthropic) and GPT (OpenAI).
-/

@[expose] public section

namespace Rule30Equivalents.ExactHearingStrip
open Ruliology.CellularAutomata Rule30Realization
local notation "segment" => Rule30Certificates.HorizontalDiversity.segment

-- The parameter d gives width d+1, so there is always an eastern neighbour.
abbrev Strip (d : ℕ) := Fin (d + 1) → Bool
def view (d : ℕ) (r : ℤ → Bool) : Strip d := fun i => r ((i : ℤ) + 1)

/-- A strip tick with the wall fixed and the one outer eastern input free. -/
def Tick {d : ℕ} (b : Bool) (s v : Strip d) : Prop :=
  ∃ r : ℤ → Bool, r 0 = b ∧ view d r = s ∧ view d (evol r 1) = v

def child {d : ℕ} (S : Set (Strip d)) (b o : Bool) : Set (Strip d) :=
  {v | ∃ s ∈ S, (b || s 0) = o ∧ Tick b s v}

noncomputable def words {d : ℕ} (S : Set (Strip d)) : List Bool → List (List Bool)
  | [] => by classical exact if S.Nonempty then [[]] else []
  | b :: bs => (words (child S b false) bs).map (false :: ·) ++
               (words (child S b true) bs).map (true :: ·)

def Path {d : ℕ} (s : Strip d) : List Bool → List Bool → Prop
  | [], [] => True
  | b :: bs, o :: os => (b || s 0) = o ∧ ∃ v, Tick b s v ∧ Path v bs os
  | _, _ => False

theorem mem_words {d : ℕ} (bs os : List Bool) (S : Set (Strip d)) :
    os ∈ words S bs ↔ ∃ s ∈ S, Path s bs os := by
  classical
  induction bs generalizing S os with
  | nil =>
    cases os <;> by_cases h : S.Nonempty <;> simp_all [words, Path, Set.nonempty_def]
  | cons b bs ih =>
    cases os with
    | nil => simp [words, Path]
    | cons o os =>
      cases o <;> simp [words, Path, ih, child] <;> grind

theorem words_nodup {d : ℕ} (bs : List Bool) (S : Set (Strip d)) : (words S bs).Nodup := by
  classical
  induction bs generalizing S with
  | nil => by_cases h : S.Nonempty <;> simp [words,h]
  | cons b bs ih =>
    unfold words
    rw [List.nodup_append]
    exact ⟨(ih _).map (fun _ _ h => (List.cons.inj h).2),
           (ih _).map (fun _ _ h => (List.cons.inj h).2), by simp⟩

def actualMask (x : ℤ → Bool) (t n : ℕ) :=
  segment (fun k => evol x k 0 || evol x k 1) t n

def actualWall (x : ℤ → Bool) (t n : ℕ) := segment (fun k => evol x k 0) t n

theorem segment_length (c : ℕ → Bool) (t n : ℕ) : (segment c t n).length = n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih (t+1))

theorem physical_path (d : ℕ) (x : ℤ → Bool) (t n : ℕ) :
    Path (view d (evol x t)) (actualWall x t n) (actualMask x t n) := by
  induction n generalizing t with
  | zero => trivial
  | succ n ih =>
    exact ⟨rfl, view d (evol x (t+1)), ⟨evol x t, rfl, rfl, by funext i; rfl⟩, ih (t+1)⟩

theorem physical_mem (d : ℕ) (x : ℤ → Bool) (t n : ℕ) :
    actualMask x t n ∈ words (Set.univ : Set (Strip d)) (actualWall x t n) :=
  (mem_words _ _ _).2 ⟨_, Set.mem_univ _, physical_path d x t n⟩

-- One layer of the eastern light cone disappears each tick.
private theorem agree_tick {d : ℕ} {s v : Strip d} {b : Bool} (ht : Tick b s v)
    (r : ℤ → Bool) (h0 : r 0 = b) (k : ℕ)
    (h : ∀ i : Fin (d+1), i.val < k+1 → view d r i = s i) (hk : k+1 ≤ d+1) :
    ∀ i : Fin (d+1), i.val < k → view d (evol r 1) i = v i := by
  obtain ⟨z,hz,hs,rfl⟩ := ht
  intro i hi
  have eqAt (j : ℕ) (hj : j < k+1) : r ((j : ℤ)+1) = z ((j : ℤ)+1) := by
    let a : Fin (d+1) := ⟨j, by omega⟩
    exact (h a hj).trans (congrFun hs a).symm
  have left : r (i : ℤ) = z (i : ℤ) := by
    cases e : i.val with
    | zero => simpa [e] using h0.trans hz.symm
    | succ j => simpa [e] using eqAt j (by omega)
  change Rule30Jen.rule (r _) (r _) (r _) = Rule30Jen.rule (z _) (z _) (z _)
  congr 1
  · simpa using left
  · exact eqAt i (by omega)
  · simpa [Nat.cast_add, add_assoc] using eqAt (i.val+1) (by omega)

private theorem follow {d : ℕ} (x : ℤ → Bool) (t : ℕ) (bs os : List Bool) (s : Strip d)
    (hp : Path s bs os) (hw : actualWall x t bs.length = bs) (hk : bs.length ≤ d+1)
    (h : ∀ i : Fin (d+1), i.val < bs.length → view d (evol x t) i = s i) :
    actualMask x t bs.length = os := by
  induction bs generalizing os s t with
  | nil => cases os <;> simp_all [Path, actualMask, Rule30Certificates.HorizontalDiversity.segment]
  | cons b bs ih =>
    cases os with
    | nil => exact False.elim hp
    | cons o os =>
      obtain ⟨ho,v,ht,tail⟩ := hp
      obtain ⟨hb,hs⟩ := List.cons.inj hw
      have hh := h 0 (by simp)
      change evol x t 1 = s 0 at hh
      have hn := agree_tick ht (evol x t) hb bs.length h hk
      exact congrArg₂ List.cons (by simpa [hb,hh] using ho) (ih (t+1) os v tail hs (by simp at hk; omega) hn)

/-- Every surviving word of length at most the width comes from a whole row, even with
an arbitrary prescribed continuation of the wall. -/
theorem realize_word {d n : ℕ} (c : ℕ → Bool) (hk : n ≤ d+1) {os : List Bool}
    (hm : os ∈ words (Set.univ : Set (Strip d)) (segment c 0 n)) :
    ∃ x : ℤ → Bool, (∀ t, evol x t 0 = c t) ∧ actualMask x 0 n = os := by
  obtain ⟨s,_,hs⟩ := (mem_words _ _ _).1 hm
  let R : ℤ → Bool := fun p => if h : p.toNat-1 < d+1 then s ⟨p.toNat-1,h⟩ else false
  obtain ⟨x,hR,hc,_⟩ := column_realizable_unique R c
  have len := segment_length c 0 n
  refine ⟨x,hc,?_⟩
  have hw : actualWall x 0 n = segment c 0 n := by simp [actualWall,funext hc]
  have hh : ∀ i : Fin (d+1), view d (evol x 0) i = s i := by
    intro i
    change x ((i : ℤ)+1) = s i
    rw [hR _ (by omega)]
    have hi : i.val ≤ d := by omega
    simp [R,hi]
  have ht := follow x 0 _ os s hs (by simpa [len] using hw) (by simpa [len] using hk) (fun i _ => hh i)
  simpa [len] using ht

theorem exact_at_width {d n : ℕ} (c : ℕ → Bool) (hk : n ≤ d+1) (os : List Bool) :
    os ∈ words (Set.univ : Set (Strip d)) (segment c 0 n) ↔
    ∃ x : ℤ → Bool, (∀ t, evol x t 0 = c t) ∧ actualMask x 0 n = os := by
  refine ⟨realize_word c hk, ?_⟩
  rintro ⟨x,hc,rfl⟩
  simpa [actualWall,funext hc] using physical_mem d x 0 n

end Rule30Equivalents.ExactHearingStrip
