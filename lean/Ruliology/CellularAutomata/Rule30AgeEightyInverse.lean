module

public import Ruliology.CellularAutomata.Rule30Certificates.AgeEightyCover
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Four inverse ticks at a fixed white wall

Starting at age 80, every four-tick preimage of a nonzero finite orbit has its true
edge four cells inside the image edge. The 54 transitions below start at the kit's
age-26 cycle. A word denotes an outer prefix, with its least significant bit
facing the wall. Shortening a prefix forgets interior cells and enlarges the cover.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30AgeEightyInverse

open Rule30ZeroBoundary Rule30ZeroBoundary.IntegerForm Rule30LateTwins
open Rule30AgeTwentyFourInverse Rule30Certificates.AgeEightyCover

set_option maxHeartbeats 0
set_option maxRecDepth 8192

private def rowCovered (ps : List Nat) (Y : Nat) : Prop :=
  ∃ q p, 1 ≤ q ∧ p ∈ ps ∧ Y >>> q = p

private theorem extend_cover {ps : List Nat} {Y u q : Nat}
    (hq : 1 ≤ q) (hu : Y >>> q = u) (hc : covered ps u = true) : rowCovered ps Y := by
  obtain ⟨p, hp, h⟩ := List.any_eq_true.mp hc
  refine ⟨q + (u.log2 - p.log2), p, by omega, hp, ?_⟩
  rw [Nat.shiftRight_add, hu]
  exact beq_iff_eq.mp h

private theorem move_cover {ps ns : List Nat} {Y : Nat}
    (h : links ps ns = true) (hy : rowCovered ps Y) : rowCovered ns (F Y) := by
  obtain ⟨q, p, hq, hp, cut⟩ := hy
  obtain ⟨k, rfl⟩ : ∃ k, q = k+1 := ⟨q-1, by omega⟩
  have hc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h p hp)
  have hd : (Y >>> k) / 2 = p := by
    rw [Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (Y >>> k) 1] at cut
    exact cut
  have alt : Y >>> k = 2*p ∨ Y >>> k = 2*p+1 := by omega
  apply extend_cover (Y := F Y) (q := k+1) (u := R (Y >>> k)) (by omega) (F_shiftRight Y k)
  rcases alt with h0 | h1
  · simpa only [h0] using hc.1
  · simpa only [h1] using hc.2

private theorem walk_sound (ps : List Nat) (rest : List (List Nat)) (Y : Nat)
    (h : walk ps rest = true) (hy : rowCovered ps Y) :
    rowCovered (rest.getLastD ps) (iter F rest.length Y) := by
  induction rest generalizing ps Y with
  | nil => exact hy
  | cons ns rest ih =>
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
    have hh := ih ns (F Y) h2 (move_cover h1 hy)
    rw [List.length_cons, show rest.length + 1 = 1 + rest.length by omega, iter_add]
    cases rest <;> exact hh

private theorem aged_cover (Y t : Nat) (hY : Y ≠ 0) (ht : 80 ≤ t) :
    rowCovered lastBands (iter F t Y) := by
  let a := t - 54
  let q := Y.log2 + a - 19
  let Z := iter F a Y
  have ha : 26 ≤ a := by dsimp [a]; omega
  have hq : 1 ≤ q := by dsimp [q]; omega
  have base := band_from_age_twenty_six hY ha
  change inC20 (Z >>> q) = true at base
  have small : covered firstBands (Z >>> q) = true := by
    simp only [inC20, Bool.or_eq_true, beq_iff_eq] at base
    rcases base with ((h | h) | h) | h <;> rw [h] <;> decide +kernel
  have hh := walk_sound firstBands stages Z cover_certificate (extend_cover hq rfl small)
  change rowCovered lastBands (iter F 54 Z) at hh
  rwa [show t = a + 54 by dsimp [a]; omega, iter_add]

private def pack (a b c d e f g h : Bool) : Nat :=
  a.toNat*2 + b.toNat + c.toNat*8 + d.toNat*4 +
  e.toNat*32 + f.toNat*16 + g.toNat*128 + h.toNat*64

private theorem pack_lt (a b c d e f g h : Bool) : pack a b c d e f g h < 256 := by
  revert a b c d e f g h
  decide +kernel

private theorem advance_pack (x a b c d e f g h : Bool) :
    advance x (pack a b c d e f g h) =
      pack b (xor x (b || a)) d (xor b (d || c))
           f (xor d (f || e)) h (xor f (h || g)) := by
  revert x a b c d e f g h
  decide +kernel

private def register (L : Nat → Bool) (i : Nat) : Nat :=
  pack (zrow L 3 i) (zrow L 3 (i+1)) (zrow L 2 i) (zrow L 2 (i+1))
       (zrow L 1 i) (zrow L 1 (i+1)) (zrow L 0 i) (zrow L 0 (i+1))

private theorem register_step (L : Nat → Bool) (i : Nat) :
    advance (zrow L 4 (i+1)) (register L i) = register L (i+1) := by
  unfold register
  rw [advance_pack, zrow_inv L 3 i, zrow_inv L 2 i, zrow_inv L 1 i, zrow_inv L 0 i]

private theorem scan_row (L : Nat → Bool) (Z : Nat)
    (hz : ∀ k, 1 ≤ k → zrow L 4 k = rowOfNat Z k) (q n : Nat) :
    scan n (Z >>> q) (register L q) = register L (q+n) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [scan, ← Nat.shiftRight_add, Nat.testBit_shiftRight, Nat.add_zero]
    rw [show Z.testBit q = zrow L 4 (q+1) from (hz (q+1) (by omega)).symm,
      register_step, ih]
    congr 1 <;> omega

private theorem oldest_white (a b c d e f g h : Bool)
    (hz : pack a b c d e f g h = 0) : g = false := by
  revert a b c d e f g h
  decide +kernel

private theorem finite_of_cover {L : Nat → Bool} {Z : Nat}
    (hc : rowCovered lastBands Z)
    (hz : ∀ k, 1 ≤ k → zrow L 4 k = rowOfNat Z k) : FinSupp L := by
  obtain ⟨q, p, hq, hp, cut⟩ := hc
  let n := p.log2+1
  have h := chk_sound _ 8 0 (List.all_eq_true.mp reset_certificate p hp)
    (register L q) (pack_lt ..)
  have zero : register L (q+n) = 0 := by
    rw [← scan_row L Z hz, cut]
    simpa only [Nat.zero_add] using (beq_iff_eq.mp h)
  have outside : Z >>> (q+n) = 0 := by
    rw [Nat.shiftRight_add, cut, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.lt_log2_self)
  have tail (d : Nat) : register L ((q+n)+d) = 0 := by
    rw [← scan_row L Z hz, outside, zero]
    induction d with
    | zero => rfl
    | succ d ih => exact ih
  refine ⟨q+n, fun k hk => ?_⟩
  obtain ⟨d,rfl⟩ : ∃ d, k = (q+n)+d := ⟨k-(q+n), by omega⟩
  rw [← zrow_zero_of_pos L (by omega)]
  exact oldest_white _ _ _ _ _ _ _ _ (tail d)

/-- Every four-tick predecessor, initially allowed infinite support, agrees at all
positive depths with a finite row whose high bit is exactly four sites inside the
ending edge. The fixed wall discards the initial value at depth zero. -/
theorem aged_four_step_predecessor (Y t : Nat) (hY : Y ≠ 0) (ht : 80 ≤ t)
    (L : Nat → Bool) (hL : ∀ k, 1 ≤ k → zrow L 4 k = rowOfNat (iter F t Y) k) :
    ∃ A : Nat, (∀ k, 1 ≤ k → rowOfNat A k = L k) ∧
      iter F 4 A = iter F t Y ∧ Top A (Y.log2 + t - 4) := by
  obtain ⟨W, hW⟩ := finite_of_cover (aged_cover Y t hY ht) hL
  let A := natOfRow L W
  have ha : ∀ k, 1 ≤ k → rowOfNat A k = L k := rowOfNat_natOfRow hW
  have him : iter F 4 A = iter F t Y := by
    apply rowOfNat_ext
    intro k
    rw [← zrow_rowOfNat, zrow_congr ha, hL _ (by omega)]
  have hedge := Top_iter (top_log2 hY) t
  have hn : A ≠ 0 := by
    intro h
    rw [← him, h] at hedge
    have hz : iter F 4 0 = 0 := by decide
    simp [hz, Top] at hedge
  have htop := Top_iter (top_log2 hn) 4
  rw [him] at htop
  have he := Top_unique htop hedge
  exact ⟨A, ha, him, by rw [show Y.log2 + t - 4 = A.log2 by omega]; exact top_log2 hn⟩

private theorem forward_back (b : Bool) (y : Nat → Bool) (hy : y 0 = false) :
    zrow (back b y) 1 = y := by
  funext k
  cases k with
  | zero => exact (zrow_wall _ _).trans hy.symm
  | succ k => exact zrow_back _ _ _ (by omega)

private theorem next_time (L y : Nat → Bool) (n : Nat) (h : zrow L n = y) :
    zrow L (n+1) = zrow y 1 := by
  funext k
  rw [zrow_shift, h]

/-- Each of the sixteen assignments of the wall-adjacent cells at times 0,1,2,3
is attained by a finite four-tick predecessor of the stated exact width. -/
theorem all_four_tick_histories (Y t : Nat) (hY : Y ≠ 0) (ht : 80 ≤ t)
    (b₀ b₁ b₂ b₃ : Bool) :
    ∃ A : Nat, iter F 4 A = iter F t Y ∧ Top A (Y.log2 + t - 4) ∧
      rowOfNat A 1 = b₀ ∧ rowOfNat (iter F 1 A) 1 = b₁ ∧
      rowOfNat (iter F 2 A) 1 = b₂ ∧ rowOfNat (iter F 3 A) 1 = b₃ := by
  let E := rowOfNat (iter F t Y)
  let X₃ := back b₃ E
  let X₂ := back b₂ X₃
  let X₁ := back b₁ X₂
  let L := back b₀ X₁
  have s₁ : zrow L 1 = X₁ := forward_back _ _ rfl
  have s₂ : zrow L 2 = X₂ := (next_time _ _ 1 s₁).trans (forward_back _ _ rfl)
  have s₃ : zrow L 3 = X₃ := (next_time _ _ 2 s₂).trans (forward_back _ _ rfl)
  have s₄ : zrow L 4 = E := (next_time _ _ 3 s₃).trans (forward_back _ _ rfl)
  obtain ⟨A, ha, him, hedge⟩ := aged_four_step_predecessor Y t hY ht L
    (fun k _ => congrFun s₄ k)
  have clock (i : Nat) : rowOfNat (iter F i A) 1 = zrow L i 1 :=
    (zrow_rowOfNat A i 1).symm.trans (zrow_congr ha i 1)
  exact ⟨A, him, hedge, ha 1 (by decide), (clock 1).trans (congrFun s₁ 1),
    (clock 2).trans (congrFun s₂ 1), (clock 3).trans (congrFun s₃ 1)⟩

end Ruliology.CellularAutomata.Rule30AgeEightyInverse
