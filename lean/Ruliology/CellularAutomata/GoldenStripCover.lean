module

public import Ruliology.CellularAutomata.GoldenQuadratic

/-! Finite certificate for the six golden lags. At each intermediate integer height
the recorded integer separates the lattice points below the strip from those above it. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Golden
open Q5 Lean.Grind

def phys (p : Q5) : Q5 := ⟨-p.a, p.b⟩

def families : List Q5 := [⟨-3,1⟩, ⟨-4,2⟩, ⟨-7,3⟩, ⟨-11,5⟩, ⟨-18,8⟩, ⟨-29,13⟩]

def below (p r : Q5) : Bool :=
  let t := r - p
  decide (0 ≤ 1000000*t.a + 2236067*t.b ∧ 0 ≤ 1000000*t.a + 2236069*t.b)

private theorem sound {p r : Q5} (h : below p r = true) : p ≤ r := by
  have hh := _root_.of_decide_eq_true h
  have h' := Q5.below_sound _ _ hh.1 hh.2
  change (0 : Q5) ≤ r-p at h'
  grind

def low (e : Q5) : Q5 := if below 0 (-e) then 0 else -e
def high (e : Q5) : Q5 := if below 0 (-e) then -e else 0
def crosses (e s p : Q5) : Prop := low e ≤ s+p ∧ s+p < high e

def consecutive (e p r s : Q5) : Prop :=
  p.b < r.b ∧ crosses e s p ∧ crosses e s r ∧
    ∀ v : Q5, p.b < v.b → v.b < r.b → ¬crosses e s v

private structure Gap where
  e : Q5
  p : Q5
  r : Q5
  skips : List Int

private def skipsOK (l h lo hi : Q5) (stop b : Int) : List Int → Bool
  | [] => b == stop
  | k :: ks => below (h + ⟨k-1,b⟩) lo && below hi (l + ⟨k,b⟩) &&
      skipsOK l h lo hi stop (b+1) ks

private theorem skips_sound {s l h lo hi : Q5} (hs : l ≤ s ∧ s < h)
    (stop b : Int) (ks : List Int) (ok : skipsOK l h lo hi stop b ks = true)
    (v : Q5) (hb : b ≤ v.b ∧ v.b < stop) :
    ¬ (lo ≤ s+v ∧ s+v < hi) := by
  induction ks generalizing b with
  | nil => simp [skipsOK] at ok; omega
  | cons k ks ih =>
    simp only [skipsOK, Bool.and_eq_true] at ok
    by_cases he : b = v.b
    · subst b
      by_cases hk : k ≤ v.a
      · have hh := sound ok.1.2
        have hc : (⟨k,v.b⟩ : Q5) ≤ v := ⟨0, by simp [it]; omega⟩
        grind
      · have hh := sound ok.1.1
        have hc : v ≤ (⟨k-1,v.b⟩ : Q5) := ⟨0, by simp [it]; omega⟩
        grind
    · exact ih (b+1) ok.2 ⟨by omega,hb.2⟩

private def inside (l h lo hi p : Q5) := below lo (l+p) && below (h+p) hi
private def gapOK (l h : Q5) (g : Gap) : Bool :=
  decide (g.e ∈ families ∧ g.p.b < g.r.b ∧ g.r.b ≤ 100) &&
    inside l h (low g.e) (high g.e) g.p && inside l h (low g.e) (high g.e) g.r &&
    skipsOK l h (low g.e) (high g.e) g.r.b (g.p.b+1) g.skips

private theorem gap_sound {l h s : Q5} {g : Gap} (hs : l ≤ s ∧ s < h)
    (ok : gapOK l h g = true) : g.e ∈ families ∧ g.r.b ≤ 100 ∧ consecutive g.e g.p g.r s := by
  simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨hm,hb,hrb⟩,hp⟩,hr⟩,hk⟩ := ok
  have mem (p : Q5) (hin : inside l h (low g.e) (high g.e) p = true) : crosses g.e s p := by
    simp only [inside,Bool.and_eq_true] at hin
    have := sound hin.1; have := sound hin.2; unfold crosses; grind
  exact ⟨hm,hrb,hb,mem _ hp,mem _ hr,fun v a b =>
    skips_sound hs _ _ _ hk v ⟨by omega,b⟩⟩

private def lower (g : Gap) := 11*phys g.e - 10*phys g.r
private def upper (g : Gap) := 10*(phys g.r - 2*phys g.p) - 11*phys g.e
def Witness (s z : Q5) : Prop :=
  ∃ e ∈ families, ∃ p r, r.b ≤ 100 ∧ consecutive e p r s ∧
    11*phys e ≤ 10*(z+phys r) ∧ 11*phys e ≤ 10*(phys r-2*phys p-z)

private def chain (l h start : Q5) : List Gap → Bool
  | [] => below 50 start
  | g :: gs => gapOK l h g && below (lower g) start && chain l h (upper g) gs

private theorem chain_sound {s z l h : Q5} (hs : l ≤ s ∧ s < h) (start : Q5) (gs : List Gap)
    (ok : chain l h start gs = true) (hz : start < 10*z ∧ 10*z ≤ 50) : Witness s z := by
  induction gs generalizing start with
  | nil => have := sound ok; grind
  | cons g gs ih =>
    simp only [chain,Bool.and_eq_true] at ok
    by_cases ha : 10*z ≤ upper g
    · obtain ⟨hm,hb,hg⟩ := gap_sound hs ok.1.1
      have hf := sound ok.1.2
      unfold upper at ha; unfold lower at hf
      exact ⟨g.e,hm,g.p,g.r,hb,hg,by grind,by grind⟩
    · exact ih _ ok.2 ⟨by grind,hz.2⟩

private structure Row where
  stop : Q5
  gaps : List Gap
private def cover (l : Q5) : List Row → Bool
  | [] => below 1 l
  | row :: rs => chain l row.stop (-10) row.gaps && cover row.stop rs

private theorem cover_sound {s z : Q5} (hs : s < 1) (hz : -1 < z ∧ z ≤ 5) (l : Q5) (rs : List Row)
    (hl : l ≤ s) (ok : cover l rs = true) : Witness s z := by
  induction rs generalizing l with
  | nil => have := sound ok; grind
  | cons r rs ih =>
    simp only [cover,Bool.and_eq_true] at ok
    by_cases h : s < r.stop
    · exact chain_sound ⟨hl,h⟩ _ _ ok.1 (by grind)
    · exact ih _ (by grind) ok.2

private def rows : List Row := [
  ⟨⟨47, -21⟩, [⟨⟨-18, 8⟩, ⟨0, 0⟩, ⟨-29, 13⟩, [-2, -4, -6, -8, -11, -13, -15, -17, -20, -22, -24, -26]⟩]⟩,
  ⟨⟨9, -4⟩, [⟨⟨-18, 8⟩, ⟨0, 0⟩, ⟨-38, 17⟩, [-2, -4, -6, -8, -11, -13, -15, -17, -20, -22, -24, -26, -29, -31, -33, -35]⟩]⟩,
  ⟨⟨18, -8⟩, [⟨⟨-11, 5⟩, ⟨2, -1⟩, ⟨-18, 8⟩, [0, -2, -4, -6, -9, -11, -13, -15]⟩]⟩,
  ⟨⟨27, -12⟩, [⟨⟨-7, 3⟩, ⟨0, 0⟩, ⟨-9, 4⟩, [-2, -4, -6]⟩,
      ⟨⟨-4, 2⟩, ⟨2, -1⟩, ⟨-5, 2⟩, [0, -2]⟩]⟩,
  ⟨⟨36, -16⟩, [⟨⟨-29, 13⟩, ⟨2, -1⟩, ⟨-36, 16⟩, [0, -2, -4, -6, -9, -11, -13, -15, -18, -20, -22, -24, -27, -29, -31, -33]⟩]⟩,
  ⟨⟨-2, 1⟩, [⟨⟨-18, 8⟩, ⟨11, -5⟩, ⟨-27, 12⟩, [9, 7, 5, 3, 0, -2, -4, -6, -9, -11, -13, -15, -18, -20, -22, -24]⟩]⟩,
  ⟨⟨45, -20⟩, [⟨⟨-18, 8⟩, ⟨2, -1⟩, ⟨-27, 12⟩, [0, -2, -4, -6, -9, -11, -13, -15, -18, -20, -22, -24]⟩]⟩,
  ⟨⟨7, -3⟩, [⟨⟨-18, 8⟩, ⟨2, -1⟩, ⟨-36, 16⟩, [0, -2, -4, -6, -9, -11, -13, -15, -18, -20, -22, -24, -27, -29, -31, -33]⟩]⟩,
  ⟨⟨16, -7⟩, [⟨⟨-11, 5⟩, ⟨4, -2⟩, ⟨-16, 7⟩, [2, 0, -2, -4, -7, -9, -11, -13]⟩]⟩,
  ⟨⟨25, -11⟩, [⟨⟨-11, 5⟩, ⟨-5, 2⟩, ⟨-25, 11⟩, [-7, -9, -11, -13, -16, -18, -20, -22]⟩]⟩,
  ⟨⟨34, -15⟩, [⟨⟨-29, 13⟩, ⟨4, -2⟩, ⟨-34, 15⟩, [2, 0, -2, -4, -7, -9, -11, -13, -16, -18, -20, -22, -25, -27, -29, -31]⟩]⟩,
  ⟨⟨-4, 2⟩, [⟨⟨-18, 8⟩, ⟨13, -6⟩, ⟨-25, 11⟩, [11, 9, 7, 5, 2, 0, -2, -4, -7, -9, -11, -13, -16, -18, -20, -22]⟩]⟩,
  ⟨⟨43, -19⟩, [⟨⟨-18, 8⟩, ⟨4, -2⟩, ⟨-25, 11⟩, [2, 0, -2, -4, -7, -9, -11, -13, -16, -18, -20, -22]⟩]⟩,
  ⟨⟨5, -2⟩, [⟨⟨-18, 8⟩, ⟨4, -2⟩, ⟨-34, 15⟩, [2, 0, -2, -4, -7, -9, -11, -13, -16, -18, -20, -22, -25, -27, -29, -31]⟩]⟩,
  ⟨⟨14, -6⟩, [⟨⟨-11, 5⟩, ⟨6, -3⟩, ⟨-14, 6⟩, [4, 2, 0, -2, -5, -7, -9, -11]⟩]⟩,
  ⟨⟨23, -10⟩, [⟨⟨-11, 5⟩, ⟨-3, 1⟩, ⟨-23, 10⟩, [-5, -7, -9, -11, -14, -16, -18, -20]⟩]⟩,
  ⟨⟨32, -14⟩, [⟨⟨-3, 1⟩, ⟨0, 0⟩, ⟨-5, 2⟩, [-2]⟩,
      ⟨⟨-29, 13⟩, ⟨6, -3⟩, ⟨-32, 14⟩, [4, 2, 0, -2, -5, -7, -9, -11, -14, -16, -18, -20, -23, -25, -27, -29]⟩]⟩,
  ⟨⟨-6, 3⟩, [⟨⟨-18, 8⟩, ⟨15, -7⟩, ⟨-23, 10⟩, [13, 11, 9, 7, 4, 2, 0, -2, -5, -7, -9, -11, -14, -16, -18, -20]⟩]⟩,
  ⟨⟨41, -18⟩, [⟨⟨-18, 8⟩, ⟨6, -3⟩, ⟨-23, 10⟩, [4, 2, 0, -2, -5, -7, -9, -11, -14, -16, -18, -20]⟩]⟩,
  ⟨⟨3, -1⟩, [⟨⟨-18, 8⟩, ⟨6, -3⟩, ⟨-32, 14⟩, [4, 2, 0, -2, -5, -7, -9, -11, -14, -16, -18, -20, -23, -25, -27, -29]⟩]⟩,
  ⟨⟨50, -22⟩, [⟨⟨-18, 8⟩, ⟨-3, 1⟩, ⟨-32, 14⟩, [-5, -7, -9, -11, -14, -16, -18, -20, -23, -25, -27, -29]⟩]⟩,
  ⟨⟨12, -5⟩, [⟨⟨-18, 8⟩, ⟨-3, 1⟩, ⟨-41, 18⟩, [-5, -7, -9, -11, -14, -16, -18, -20, -23, -25, -27, -29, -32, -34, -36, -38]⟩]⟩,
  ⟨⟨21, -9⟩, [⟨⟨-11, 5⟩, ⟨-1, 0⟩, ⟨-21, 9⟩, [-3, -5, -7, -9, -12, -14, -16, -18]⟩]⟩,
  ⟨⟨30, -13⟩, [⟨⟨-4, 2⟩, ⟨-1, 0⟩, ⟨-8, 3⟩, [-3, -5]⟩,
      ⟨⟨-3, 1⟩, ⟨2, -1⟩, ⟨-3, 1⟩, [0]⟩]⟩,
  ⟨⟨-8, 4⟩, [⟨⟨-18, 8⟩, ⟨17, -8⟩, ⟨-21, 9⟩, [15, 13, 11, 9, 6, 4, 2, 0, -3, -5, -7, -9, -12, -14, -16, -18]⟩]⟩,
  ⟨⟨39, -17⟩, [⟨⟨-18, 8⟩, ⟨8, -4⟩, ⟨-21, 9⟩, [6, 4, 2, 0, -3, -5, -7, -9, -12, -14, -16, -18]⟩]⟩,
  ⟨⟨1, 0⟩, [⟨⟨-18, 8⟩, ⟨8, -4⟩, ⟨-30, 13⟩, [6, 4, 2, 0, -3, -5, -7, -9, -12, -14, -16, -18, -21, -23, -25, -27]⟩]⟩]

private theorem rows_pass : cover 0 rows = true := by decide

theorem golden_strip_cover (s z : Q5) (hs : 0 ≤ s ∧ s < 1) (hz : -1 < z ∧ z ≤ 5) :
    Witness s z := cover_sound hs.2 hz 0 rows hs.1 rows_pass

end Ruliology.CellularAutomata.Golden
