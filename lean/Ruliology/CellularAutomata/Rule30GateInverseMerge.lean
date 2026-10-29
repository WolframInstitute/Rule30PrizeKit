module
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! A short legal boundary window forces the two inverse heads to coalesce.
This does not prove that either inverse has finite support. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GateInverseMerge
open Rule30ZeroBoundary

def words : List Nat := [8,9,16,18,33,36,66,72,132,144]

def phase (w t : Nat) : Bool :=
  if t % 2 = 0 then true else !(Nat.testBit w (t / 2))

def template (w : Nat) : Nat → Bool := lam (phase w)

/-- Eight forced black readings and the interleaved complementary gate word. -/
def LocalWindow (y : Nat → Bool) : Prop :=
  ∃ w, w ∈ words ∧ ∀ t, t < 16 → zrow y t 1 = phase w t

theorem back_congr_pair (b : Bool) (y z : Nat → Bool) (n : Nat)
    (h : ∀ k, 1 ≤ k → k ≤ n → y k = z k) :
    back b y n = back b z n ∧ back b y (n+1) = back b z (n+1) := by
  induction n with
  | zero => constructor <;> rfl
  | succ n ih =>
      obtain ⟨h0,h1⟩ := ih (fun k hk hn => h k hk (by omega))
      constructor
      · exact h1
      · change xor (y (n+1)) (back b y (n+1) || back b y n) =
          xor (z (n+1)) (back b z (n+1) || back b z n)
        rw [h (n+1) (by omega) (by omega), h0, h1]

theorem back_tail_of_pair (y : Nat → Bool) (b c : Bool) (n : Nat)
    (h0 : back b y n = back c y n)
    (h1 : back b y (n+1) = back c y (n+1)) :
    ∀ k, n ≤ k → back b y k = back c y k := by
  have key : ∀ j, back b y (n+j) = back c y (n+j) ∧
      back b y (n+j+1) = back c y (n+j+1) := by
    intro j
    induction j with
    | zero => simpa using And.intro h0 h1
    | succ j ih =>
        constructor
        · simpa only [Nat.add_assoc] using ih.2
        · change xor (y (n+j+1)) (back b y (n+j+1) || back b y (n+j)) =
            xor (y (n+j+1)) (back c y (n+j+1) || back c y (n+j))
          rw [ih.1, ih.2]
  intro k hk
  simpa only [Nat.add_sub_of_le hk] using (key (k-n)).1

theorem row_eq_template (y : Nat → Bool) (w : Nat)
    (h : ∀ t, t < 16 → zrow y t 1 = phase w t)
    (k : Nat) (hk : 1 ≤ k) (hbound : k ≤ 16) : y k = template w k := by
  change y k = recon (phase w) k 0
  calc
    y k = recon (fun t => zrow y t 1) k 0 :=
      (zrow_zero_of_pos y hk).symm.trans (history_eq_recon y k 0)
    _ = recon (phase w) k 0 := by
      apply recon_local
      intro j hj
      simpa only [Nat.zero_add] using h j (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem merge_certificate (w : Nat) (hw : w ∈ words) :
    back false (template w) 11 = back true (template w) 11 ∧
    back false (template w) 12 = back true (template w) 12 := by
  simp [words] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem heads_agree_after_eleven (y : Nat → Bool) (h : LocalWindow y) :
    ∀ k, 11 ≤ k → back false y k = back true y k := by
  obtain ⟨w,hw,hy⟩ := h
  have same (b : Bool) : back b y 11 = back b (template w) 11 ∧
      back b y 12 = back b (template w) 12 :=
    back_congr_pair b y (template w) 11
      (fun k hk hn => row_eq_template y w hy k hk (by omega))
  obtain ⟨hc0,hc1⟩ := merge_certificate w hw
  apply back_tail_of_pair y false true 11
  · exact (same false).1.trans (hc0.trans (same true).1.symm)
  · exact (same false).2.trans (hc1.trans (same true).2.symm)

theorem finite_head_independent (y : Nat → Bool) (h : LocalWindow y) :
    FinSupp (back false y) ↔ FinSupp (back true y) := by
  have he := heads_agree_after_eleven y h
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 11, fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 11, fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)

theorem finite_preimage_iff_head_true (y : Nat → Bool) (h : LocalWindow y) :
    (∃ b : Bool, FinSupp (back b y)) ↔ FinSupp (back true y) := by
  constructor
  · rintro ⟨b,hb⟩
    cases b with
    | false => exact (finite_head_independent y h).1 hb
    | true => exact hb
  · intro ht
    exact ⟨true,ht⟩

theorem back_trace (b : Bool) (L : Nat → Bool) (t k : Nat) :
    zrow (back b L) (t+1) k = zrow L t k := by
  calc
    zrow (back b L) (t+1) k = zrow (zrow (back b L) 1) t k := by
      simpa only [Nat.add_comm] using zrow_shift (back b L) 1 t k
    _ = zrow L t k := zrow_congr (zrow_back b L) t k

/-- The first eight even readings encode a legal gate, and the odd readings are black. -/
def OddGateWindow (L : Nat → Bool) : Prop :=
  ∃ w, w ∈ words ∧
    (∀ r, r < 8 → zrow L (2*r+1) 1 = true) ∧
    (∀ r, r < 8 → zrow L (2*r) 1 = !(Nat.testBit w r))

theorem first_inverse_window (L : Nat → Bool) (h : OddGateWindow L) :
    LocalWindow (back true L) := by
  obtain ⟨w,hw,ho,he⟩ := h
  refine ⟨w,hw,fun t ht => ?_⟩
  by_cases hz : t = 0
  · subst t
    rfl
  · have hp : 1 ≤ t := by omega
    have hb := back_trace true L (t-1) 1
    rw [show t-1+1=t by omega] at hb
    rw [hb]
    unfold phase
    by_cases hm : t % 2 = 0
    · rw [ite_eq_left hm]
      have hr : 1 ≤ t/2 := by omega
      have hx : t-1 = 2*(t/2-1)+1 := by omega
      rw [hx]
      exact ho (t/2-1) (by omega)
    · rw [ite_eq_right hm]
      have hx : t-1 = 2*(t/2) := by omega
      rw [hx]
      exact he (t/2) (by omega)

theorem second_inverse_heads_agree (L : Nat → Bool) (h : OddGateWindow L) :
    ∀ k, 11 ≤ k → back false (back true L) k = back true (back true L) k :=
  heads_agree_after_eleven (back true L) (first_inverse_window L h)

theorem second_inverse_finite_head_independent (L : Nat → Bool) (h : OddGateWindow L) :
    FinSupp (back false (back true L)) ↔ FinSupp (back true (back true L)) :=
  finite_head_independent (back true L) (first_inverse_window L h)

def oddPhase (w t : Nat) : Bool :=
  if t % 2 = 0 then !(Nat.testBit w (t/2)) else true

def oddTemplate (w : Nat) : Nat → Bool := lam (oddPhase w)

theorem odd_window_match (L : Nat → Bool) (w : Nat)
    (ho : ∀ r, r < 8 → zrow L (2*r+1) 1 = true)
    (he : ∀ r, r < 8 → zrow L (2*r) 1 = !(Nat.testBit w r)) :
    ∀ t, t < 16 → zrow L t 1 = oddPhase w t := by
  intro t ht
  unfold oddPhase
  by_cases hm : t%2=0
  · rw [ite_eq_left hm]
    have hx : t=2*(t/2) := by omega
    exact (congrArg (fun s => zrow L s 1) hx).trans (he (t/2) (by omega))
  · rw [ite_eq_right hm]
    have hx : t=2*(t/2)+1 := by omega
    rw [hx]
    exact ho (t/2) (by omega)

theorem row_eq_odd_template (L : Nat → Bool) (w : Nat)
    (h : ∀ t, t < 16 → zrow L t 1 = oddPhase w t)
    (k : Nat) (hk : 1 ≤ k) (hbound : k ≤ 16) : L k = oddTemplate w k := by
  change L k = recon (oddPhase w) k 0
  calc
    L k = recon (fun t => zrow L t 1) k 0 :=
      (zrow_zero_of_pos L hk).symm.trans (history_eq_recon L k 0)
    _ = recon (oddPhase w) k 0 := by
      apply recon_local
      intro j hj
      simpa only [Nat.zero_add] using h j (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem first_merge_certificate (w : Nat) (hw : w ∈ words) :
    back false (oddTemplate w) 7 = back true (oddTemplate w) 7 ∧
    back false (oddTemplate w) 8 = back true (oddTemplate w) 8 := by
  simp [words] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem first_inverse_heads_agree (L : Nat → Bool) (h : OddGateWindow L) :
    ∀ k, 7 ≤ k → back false L k = back true L k := by
  obtain ⟨w,hw,ho,he⟩ := h
  have hh := odd_window_match L w ho he
  have same (b : Bool) : back b L 7 = back b (oddTemplate w) 7 ∧
      back b L 8 = back b (oddTemplate w) 8 :=
    back_congr_pair b L (oddTemplate w) 7
      (fun k hk hn => row_eq_odd_template L w hh k hk (by omega))
  obtain ⟨hc0,hc1⟩ := first_merge_certificate w hw
  apply back_tail_of_pair L false true 7
  · exact (same false).1.trans (hc0.trans (same true).1.symm)
  · exact (same false).2.trans (hc1.trans (same true).2.symm)

theorem first_inverse_finite_head_independent (L : Nat → Bool) (h : OddGateWindow L) :
    FinSupp (back false L) ↔ FinSupp (back true L) := by
  have he := first_inverse_heads_agree L h
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 7, fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 7, fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)

theorem first_preimage_exists_iff_prescribed (L : Nat → Bool) (h : OddGateWindow L) :
    (∃ b : Bool, FinSupp (back b L)) ↔ FinSupp (back true L) := by
  constructor
  · rintro ⟨b,hb⟩
    cases b with
    | false => exact (first_inverse_finite_head_independent L h).1 hb
    | true => exact hb
  · intro ht
    exact ⟨true,ht⟩



/-! ### All four two-step histories, using a checked finite triangular table -/

structure HistoryCertificate where
  gate : Nat
  columns : List Nat
  preimages : List Nat
  deriving DecidableEq

def historyCertificates : List HistoryCertificate :=
  [⟨33, [0, 1047550, 1537, 261375, 128, 64703, 736, 16271, 40, 4027, 102, 972, 8, 200, 44, 58, 3, 10, 6, 1, 1], [916136, 916166, 412336, 412334, 412788, 412290]⟩,
   ⟨36, [0, 1047535, 1560, 261363, 130, 64690, 747, 16270, 40, 4026, 103, 972, 9, 201, 45, 59, 2, 10, 7, 0, 1], [1480556, 1480554, 2286120, 2283846, 2286124, 2286122]⟩,
   ⟨66, [0, 1044475, 6150, 259068, 512, 62204, 2946, 15935, 160, 3823, 408, 819, 34, 34, 51, 42, 14, 9, 3, 2, 0], [223996, 223994, 3812424, 3812134, 3812428, 3812426]⟩,
   ⟨72, [0, 1044415, 6240, 259023, 520, 62155, 2990, 15928, 162, 3819, 414, 816, 38, 37, 53, 47, 8, 11, 6, 0, 0], [3881900, 3881898, 1166504, 1166534, 1166508, 1166506]⟩,
   ⟨132, [0, 1032175, 24600, 249843, 2050, 52210, 11787, 14590, 640, 3006, 1633, 207, 136, 139, 78, 40, 26, 7, 4, 1, 1], [771948, 771946, 2916904, 2783558, 2916908, 2916906]⟩,
   ⟨144, [0, 1031935, 24960, 249663, 2080, 52015, 11960, 14563, 650, 2990, 1657, 195, 154, 150, 85, 61, 3, 14, 0, 2, 1], [2131628, 2131626, 4129448, 4129478, 4129452, 4129450]⟩,
   ⟨264, [0, 982975, 98400, 212943, 8200, 12235, 14382, 9208, 2562, 3835, 390, 828, 32, 44, 58, 35, 10, 14, 1, 3, 0], [457644, 457642, 3427496, 3427526, 3427500, 3427498]⟩,
   ⟨265, [0, 982974, 98401, 212943, 8200, 12235, 14382, 9208, 2562, 3835, 390, 828, 32, 44, 58, 35, 10, 14, 1, 3, 0], [457640, 457670, 3427504, 3427502, 3426932, 3427458]⟩,
   ⟨289, [0, 982014, 99841, 212223, 8320, 11455, 15072, 9103, 2600, 3771, 486, 780, 104, 88, 84, 54, 13, 9, 1, 1, 1], [653992, 654022, 3033776, 3033774, 3034228, 3033730]⟩,
   ⟨528, [0, 786175, 393600, 65343, 32800, 48943, 24760, 4067, 2058, 3054, 1561, 243, 130, 178, 107, 14, 8, 10, 7, 0, 1], [1541804, 1541802, 1639080, 1639110, 1639084, 1639082]⟩,
   ⟨530, [0, 786171, 393606, 65340, 32800, 48940, 24762, 4067, 2058, 3054, 1561, 243, 130, 178, 107, 14, 8, 10, 7, 0, 1], [1541884, 1541882, 1373256, 1639206, 1373260, 1373258]⟩,
   ⟨578, [0, 782331, 399366, 62460, 33280, 45820, 27522, 3647, 2208, 2799, 1944, 51, 418, 98, 83, 26, 22, 5, 5, 3, 0], [3369724, 3369722, 1715272, 1714982, 1715276, 1715274]⟩]


def tab (c : HistoryCertificate) (k t : Nat) : Bool :=
  Nat.testBit (c.columns[k]!) t

def tabRow (c : HistoryCertificate) (k : Nat) : Bool := tab c k 0

def parent (c : HistoryCertificate) (b : Bool) (k : Nat) : Bool :=
  Nat.testBit (c.preimages[if b then 1 else 0]!) k

def child (c : HistoryCertificate) (b₀ b₁ : Bool) (k : Nat) : Bool :=
  Nat.testBit (c.preimages[2 + 2*(if b₀ then 1 else 0) + (if b₁ then 1 else 0)]!) k

def TriangleValid (c : HistoryCertificate) : Prop :=
  (∀ t : Fin 21, tab c 0 t = false) ∧
  (∀ t : Fin 20, tab c 1 t = oddPhase c.gate t) ∧
  (∀ k : Fin 19, ∀ t : Fin 21, k.val+t.val+2 ≤ 20 →
    tab c (k.val+2) t = xor (tab c (k.val+1) (t.val+1))
      (tab c (k.val+1) t || tab c k t))

def BackValid (y : Nat → Bool) (b : Bool) (q : Nat → Bool) (n : Nat) : Prop :=
  q 0 = false ∧ q 1 = b ∧ ∀ k : Fin n,
    q (k.val+2) = xor (y (k.val+1)) (q (k.val+1) || q k)

def HistoryValid (c : HistoryCertificate) : Prop :=
  TriangleValid c ∧
  (∀ b : Bool, BackValid (tabRow c) b (parent c b) 19) ∧
  (∀ b₀ b₁ : Bool, BackValid (parent c b₀) b₁ (child c b₀ b₁) 20) ∧
  (parent c false 7 = parent c true 7 ∧ parent c false 8 = parent c true 8) ∧
  (∀ b₀ b₁ : Bool, child c b₀ b₁ 20 = child c true true 20 ∧
    child c b₀ b₁ 21 = child c true true 21)

instance historyValidDecidable : DecidablePred HistoryValid := fun c => by
    unfold HistoryValid TriangleValid BackValid
    infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem history_certificates_valid : ∀ c ∈ historyCertificates, HistoryValid c := by
  decide +kernel

theorem triangle_sound (c : HistoryCertificate) (hc : TriangleValid c) :
    ∀ k t, k+t ≤ 20 → tab c k t = recon (oddPhase c.gate) k t := by
  obtain ⟨h0,h1,hs⟩ := hc
  have key : ∀ k,
      (∀ t, k+t ≤ 20 → tab c k t = recon (oddPhase c.gate) k t) ∧
      (∀ t, k+1+t ≤ 20 → tab c (k+1) t = recon (oddPhase c.gate) (k+1) t) := by
    intro k
    induction k with
    | zero =>
        constructor
        · intro t ht
          exact h0 ⟨t,by omega⟩
        · intro t ht
          exact h1 ⟨t,by omega⟩
    | succ k ih =>
        constructor
        · simpa only [Nat.add_assoc] using ih.2
        · intro t ht
          rw [hs ⟨k,by omega⟩ ⟨t,by omega⟩ (by change k+t+2 ≤ 20; omega)]
          rw [ih.2 (t+1) (by omega), ih.2 t (by omega), ih.1 t (by omega)]
          rfl
  intro k t ht
  exact (key k).1 t ht

theorem back_valid_sound (y : Nat → Bool) (b : Bool) (q : Nat → Bool) (n : Nat)
    (h : BackValid y b q n) : ∀ k, k ≤ n+1 → q k = back b y k := by
  obtain ⟨h0,h1,hs⟩ := h
  have key : ∀ j, j ≤ n → q j = back b y j ∧ q (j+1) = back b y (j+1) := by
    intro j
    induction j with
    | zero => intro hj; exact ⟨h0,h1⟩
    | succ j ih =>
        intro hj
        obtain ⟨ha,hb⟩ := ih (by omega)
        constructor
        · exact hb
        · change q (j+2) = xor (y (j+1)) (back b y (j+1) || back b y j)
          rw [hs ⟨j,by omega⟩, ha, hb]
  intro k hk
  by_cases hn : k ≤ n
  · exact (key k hn).1
  · have hx : k=n+1 := by omega
    rw [hx]
    exact (key n (by omega)).2

/-- Exactly the legal length-ten gate prefixes, read during twenty boundary ticks. -/
def LegalHistory20 (L : Nat → Bool) : Prop :=
  ∃ c, c ∈ historyCertificates ∧ ∀ t, t < 20 → zrow L t 1 = oddPhase c.gate t

theorem history_row_matches (L : Nat → Bool) (c : HistoryCertificate)
    (hc : TriangleValid c)
    (h : ∀ t, t < 20 → zrow L t 1 = oddPhase c.gate t) :
    ∀ k, 1 ≤ k → k ≤ 20 → L k = tabRow c k := by
  intro k hk hbound
  calc
    L k = recon (fun t => zrow L t 1) k 0 :=
      (zrow_zero_of_pos L hk).symm.trans (history_eq_recon L k 0)
    _ = recon (oddPhase c.gate) k 0 := by
      apply recon_local
      intro j hj
      simpa only [Nat.zero_add] using h j (by omega)
    _ = tabRow c k := (triangle_sound c hc k 0 (by omega)).symm

theorem back_tails_of_equal_targets (y z : Nat → Bool) (b d : Bool) (n : Nat)
    (hy : ∀ k, n ≤ k → y k = z k)
    (h0 : back b y n = back d z n)
    (h1 : back b y (n+1) = back d z (n+1)) :
    ∀ k, n ≤ k → back b y k = back d z k := by
  have key : ∀ j, back b y (n+j) = back d z (n+j) ∧
      back b y (n+j+1) = back d z (n+j+1) := by
    intro j
    induction j with
    | zero => simpa using And.intro h0 h1
    | succ j ih =>
        constructor
        · simpa only [Nat.add_assoc] using ih.2
        · change xor (y (n+j+1)) (back b y (n+j+1) || back b y (n+j)) =
            xor (z (n+j+1)) (back d z (n+j+1) || back d z (n+j))
          rw [hy (n+j+1) (by omega), ih.1, ih.2]
  intro k hk
  simpa only [Nat.add_sub_of_le hk] using (key (k-n)).1

theorem all_two_step_heads_agree (L : Nat → Bool) (h : LegalHistory20 L) :
    ∀ b₀ b₁ : Bool, ∀ k, 20 ≤ k →
      back b₁ (back b₀ L) k = back true (back true L) k := by
  obtain ⟨c,hc,hh⟩ := h
  obtain ⟨ht,hp,hq,hm,hcmerge⟩ := history_certificates_valid c hc
  have rowmatch := history_row_matches L c ht hh
  have pmatch (b : Bool) : ∀ k, k ≤ 20 → parent c b k = back b L k := by
    intro k hk
    calc
      parent c b k = back b (tabRow c) k := back_valid_sound _ _ _ 19 (hp b) k (by omega)
      _ = back b L k :=
        (back_congr_pair b (tabRow c) L k
          (fun i hi hn => (rowmatch i hi (by omega)).symm)).1
  have qmatch (b₀ b₁ : Bool) : ∀ k, k ≤ 21 →
      child c b₀ b₁ k = back b₁ (back b₀ L) k := by
    intro k hk
    calc
      child c b₀ b₁ k = back b₁ (parent c b₀) k :=
        back_valid_sound _ _ _ 20 (hq b₀ b₁) k (by omega)
      _ = back b₁ (back b₀ L) k := by
        cases k with
        | zero => rfl
        | succ k =>
            exact (back_congr_pair b₁ (parent c b₀) (back b₀ L) k
              (fun i hi hn => pmatch b₀ i (by omega))).2
  have ptail : ∀ b : Bool, ∀ k, 7 ≤ k → back b L k = back true L k := by
    intro b
    cases b with
    | true => intro k hk; rfl
    | false =>
        apply back_tail_of_pair L false true 7
        · exact (pmatch false 7 (by omega)).symm.trans
            (hm.1.trans (pmatch true 7 (by omega)))
        · exact (pmatch false 8 (by omega)).symm.trans
            (hm.2.trans (pmatch true 8 (by omega)))
  intro b₀ b₁
  apply back_tails_of_equal_targets (back b₀ L) (back true L) b₁ true 20
  · intro k hk
    exact ptail b₀ k (by omega)
  · exact (qmatch b₀ b₁ 20 (by omega)).symm.trans
      ((hcmerge b₀ b₁).1.trans (qmatch true true 20 (by omega)))
  · exact (qmatch b₀ b₁ 21 (by omega)).symm.trans
      ((hcmerge b₀ b₁).2.trans (qmatch true true 21 (by omega)))

theorem two_step_finiteness_independent (L : Nat → Bool) (h : LegalHistory20 L)
    (b₀ b₁ : Bool) : FinSupp (back b₁ (back b₀ L)) ↔ FinSupp (back true (back true L)) := by
  have he := all_two_step_heads_agree L h b₀ b₁
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 20, fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 20, fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)

theorem any_two_step_preimage_iff_canonical (L : Nat → Bool) (h : LegalHistory20 L) :
    (∃ b₀ b₁ : Bool, FinSupp (back b₁ (back b₀ L))) ↔ FinSupp (back true (back true L)) := by
  constructor
  · rintro ⟨b₀,b₁,hb⟩
    exact (two_step_finiteness_independent L h b₀ b₁).1 hb
  · intro ht
    exact ⟨true,true,ht⟩


/-! The numeric certificate list covers every legal ten-bit gate prefix. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem gate_prefix_coverage : ∀ w : Fin 1024,
    (∀ i : Fin 3, ((w.val >>> i.val) &&& 255) ∈ words) ↔
      w.val ∈ historyCertificates.map (fun c => c.gate) := by
  decide +kernel

def AdmissibleHistory20 (L : Nat → Bool) : Prop :=
  ∃ w, w < 1024 ∧
    (∀ i : Fin 3, ((w >>> i.val) &&& 255) ∈ words) ∧
    (∀ t, t < 20 → zrow L t 1 = oddPhase w t)

theorem admissible_history_legal (L : Nat → Bool) (h : AdmissibleHistory20 L) :
    LegalHistory20 L := by
  obtain ⟨w,hw,hlegal,htrace⟩ := h
  have hm := (gate_prefix_coverage ⟨w,hw⟩).1 hlegal
  obtain ⟨c,hc,hcw⟩ := List.mem_map.mp hm
  refine ⟨c,hc,?_⟩
  simpa only [hcw] using htrace

theorem first_actual_preimage_iff_prescribed (L : Nat → Bool) (h : OddGateWindow L) :
    (∃ P : Nat → Bool, P 0 = false ∧ FinSupp P ∧
      ∀ k, 1 ≤ k → zrow P 1 k = L k) ↔ FinSupp (back true L) := by
  constructor
  · rintro ⟨P,h0,hfin,him⟩
    have hp : P = back (P 1) L := by
      funext k
      exact (congrFun (zrow_zero_self h0) k).symm.trans (eq_back him k)
    apply (first_preimage_exists_iff_prescribed L h).1
    refine ⟨P 1,?_⟩
    rw [← hp]
    exact hfin
  · intro hf
    exact ⟨back true L,rfl,hf,zrow_back true L⟩

theorem actual_two_step_iff_heads (L : Nat → Bool) :
    (∃ Q : Nat → Bool, Q 0 = false ∧ FinSupp Q ∧
      ∀ k, 1 ≤ k → zrow Q 2 k = L k) ↔
    (∃ b₀ b₁ : Bool, FinSupp (back b₁ (back b₀ L))) := by
  constructor
  · rintro ⟨Q,h0,hfin,him⟩
    let P := zrow Q 1
    have hPim : ∀ k, 1 ≤ k → zrow P 1 k = L k := by
      intro k hk
      exact (zrow_shift Q 1 1 k).symm.trans (him k hk)
    have hp : P = back (P 1) L := by
      funext k
      exact (congrFun (zrow_zero_self (zrow_wall Q 1)) k).symm.trans (eq_back hPim k)
    have hq : Q = back (Q 1) P := by
      funext k
      exact (congrFun (zrow_zero_self h0) k).symm.trans
        (eq_back (fun j hj => rfl) k)
    have hboth : Q = back (Q 1) (back (P 1) L) :=
      hq.trans (congrArg (back (Q 1)) hp)
    refine ⟨P 1,Q 1,?_⟩
    rw [← hboth]
    exact hfin
  · rintro ⟨b₀,b₁,hfin⟩
    refine ⟨back b₁ (back b₀ L),rfl,hfin,?_⟩
    intro k hk
    calc
      zrow (back b₁ (back b₀ L)) 2 k =
          zrow (zrow (back b₁ (back b₀ L)) 1) 1 k :=
        zrow_shift (back b₁ (back b₀ L)) 1 1 k
      _ = zrow (back b₀ L) 1 k := zrow_congr (zrow_back b₁ (back b₀ L)) 1 k
      _ = L k := zrow_back b₀ L k hk

theorem any_actual_two_step_preimage_iff_canonical (L : Nat → Bool)
    (h : AdmissibleHistory20 L) :
    (∃ Q : Nat → Bool, Q 0 = false ∧ FinSupp Q ∧
      ∀ k, 1 ≤ k → zrow Q 2 k = L k) ↔ FinSupp (back true (back true L)) := by
  rw [actual_two_step_iff_heads L]
  exact any_two_step_preimage_iff_canonical L (admissible_history_legal L h)


/-! ### The near-wall cell of an actual predecessor may also be black -/
def wallBack (w b : Bool) (y : Nat → Bool) : Nat → Bool
  | 0 => w
  | 1 => b
  | k+2 => xor (y (k+1)) (wallBack w b y (k+1) || wallBack w b y k)

theorem wall_back_congr_pair (w b : Bool) (y z : Nat → Bool) (n : Nat)
    (h : ∀ k, 1 ≤ k → k ≤ n → y k = z k) :
    wallBack w b y n = wallBack w b z n ∧
      wallBack w b y (n+1) = wallBack w b z (n+1) := by
  induction n with
  | zero => constructor <;> rfl
  | succ n ih =>
      obtain ⟨h0,h1⟩ := ih (fun k hk hn => h k hk (by omega))
      constructor
      · exact h1
      · change xor (y (n+1)) (wallBack w b y (n+1) || wallBack w b y n) =
          xor (z (n+1)) (wallBack w b z (n+1) || wallBack w b z n)
        rw [h (n+1) (by omega) (by omega), h0, h1]

def WallMergeValid (c : HistoryCertificate) : Prop :=
  ∀ w b : Bool,
    wallBack w b (tabRow c) 12 = back true (tabRow c) 12 ∧
    wallBack w b (tabRow c) 13 = back true (tabRow c) 13

instance wallMergeDecidable : DecidablePred WallMergeValid := fun c => by
  unfold WallMergeValid
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem wall_merge_certificate : ∀ c ∈ historyCertificates, WallMergeValid c := by
  decide +kernel

theorem recurrence_tail (y P Q : Nat → Bool)
    (hP : ∀ k, P (k+2) = xor (y (k+1)) (P (k+1) || P k))
    (hQ : ∀ k, Q (k+2) = xor (y (k+1)) (Q (k+1) || Q k))
    (n : Nat) (h0 : P n = Q n) (h1 : P (n+1) = Q (n+1)) :
    ∀ k, n ≤ k → P k = Q k := by
  have key : ∀ j, P (n+j) = Q (n+j) ∧ P (n+j+1) = Q (n+j+1) := by
    intro j
    induction j with
    | zero => simpa using And.intro h0 h1
    | succ j ih =>
        constructor
        · simpa only [Nat.add_assoc] using ih.2
        · rw [show n+(j+1)+1=(n+j)+2 by omega, hP, hQ, ih.1, ih.2]
  intro k hk
  simpa only [Nat.add_sub_of_le hk] using (key (k-n)).1

theorem wall_and_head_agree (L : Nat → Bool) (h : LegalHistory20 L) :
    ∀ w b : Bool, ∀ k, 12 ≤ k → wallBack w b L k = back true L k := by
  obtain ⟨c,hc,hh⟩ := h
  have rowmatch := history_row_matches L c (history_certificates_valid c hc).1 hh
  intro w b
  have hw := wall_back_congr_pair w b L (tabRow c) 12
    (fun k hk hn => rowmatch k hk (by omega))
  have hb := back_congr_pair true L (tabRow c) 12
    (fun k hk hn => rowmatch k hk (by omega))
  have hm := wall_merge_certificate c hc w b
  apply recurrence_tail L (wallBack w b L) (back true L)
    (fun k => rfl) (fun k => rfl) 12
  · exact hw.1.trans (hm.1.trans hb.1.symm)
  · exact hw.2.trans (hm.2.trans hb.2.symm)

theorem actual_image_representation (L P : Nat → Bool)
    (h : ∀ k, L (k+1) = xor (P (k+2)) (P (k+1) || P k)) :
    P = wallBack (P 0) (P 1) L := by
  have key : ∀ n, P n = wallBack (P 0) (P 1) L n ∧
      P (n+1) = wallBack (P 0) (P 1) L (n+1) := by
    intro n
    induction n with
    | zero => constructor <;> rfl
    | succ n ih =>
        constructor
        · exact ih.2
        · have hn : P (n+2) = xor (L (n+1)) (P (n+1) || P n) := by
            rw [h n]
            cases P (n+2) <;> cases (P (n+1) || P n) <;> rfl
          change P (n+2) = xor (L (n+1))
            (wallBack (P 0) (P 1) L (n+1) || wallBack (P 0) (P 1) L n)
          rw [hn, ih.1, ih.2]
  funext n
  exact (key n).1

theorem finite_actual_image_transfer (L : Nat → Bool) (h : AdmissibleHistory20 L)
    (P : Nat → Bool) (hfin : FinSupp P)
    (him : ∀ k, L (k+1) = xor (P (k+2)) (P (k+1) || P k)) :
    FinSupp (back true L) := by
  have he := wall_and_head_agree L (admissible_history_legal L h) (P 0) (P 1)
  have hp := actual_image_representation L P him
  obtain ⟨W,hW⟩ := hfin
  refine ⟨max W 12,fun k hk => ?_⟩
  rw [← he k (by omega), ← hp]
  exact hW k (by omega)

theorem single_seed_left_inverse_finite (t : Nat)
    (h : AdmissibleHistory20 (fun k => Rule30Jen.cell (t+1) (-(k : Int)))) :
    FinSupp (back true (fun k => Rule30Jen.cell (t+1) (-(k : Int)))) := by
  apply finite_actual_image_transfer _ h (fun k => Rule30Jen.cell t (-(k : Int)))
  · exact ⟨t,fun k hk => Rule30Jen.cell_eq_false_of_lt t _ (by omega)⟩
  · intro k
    change Rule30Jen.cell (t+1) (-((k+1 : Nat) : Int)) =
      xor (Rule30Jen.cell t (-((k+2 : Nat) : Int)))
        (Rule30Jen.cell t (-((k+1 : Nat) : Int)) || Rule30Jen.cell t (-(k : Int)))
    rw [Rule30Jen.cell]
    change xor (Rule30Jen.cell t (-((k+1 : Nat) : Int)-1))
      (Rule30Jen.cell t (-((k+1 : Nat) : Int)) || Rule30Jen.cell t (-((k+1 : Nat) : Int)+1)) = _
    rw [show -((k+1 : Nat) : Int)-1 = -((k+2 : Nat) : Int) by omega,
      show -((k+1 : Nat) : Int)+1 = -(k : Int) by omega]

end Ruliology.CellularAutomata.Rule30GateInverseMerge
