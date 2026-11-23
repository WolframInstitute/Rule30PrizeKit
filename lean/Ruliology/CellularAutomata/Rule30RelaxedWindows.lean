module

public import Ruliology.CellularAutomata.Rule30ResetCompactness

/-! Windows that catch every tick, and the relaxed doubling lemma, on pointed recurrent
strips. The open reset hypothesis is confined to a first clock loss and exactly the two
white intervals starting there. -/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30RelaxedWindows

open Ruliology.CellularAutomata
open Rule30AgedLeftDiagonals Rule30EveryKStatement
open Ruliology.CellularAutomata.Rule30RecurrentStrip (Clock Reset dyadic_prefix_clock)
open Ruliology.CellularAutomata.Rule30RootedWhiteReturns (Column first_clock_loss unbounded_anchors)
open Ruliology.CellularAutomata.Rule30ResetCompactness (LInfinity cap_of_unbounded_resets)

abbrev PrefixClocks (d : Nat → Column) := ∀ m, ∃ p, 0 < p ∧ Clock d m p
def White (d : Nat → Column) (a : Nat) := ∀ t, d a t = false

/-- The least prefix clock is p = 2^e through a. The next column flips at p,
so a + 1 is the first wheel at which that clock fails. -/
structure FirstLoss (d : Nat → Column) (a e : Nat) : Prop where
  clock : Clock d a (2^e)
  least : ∀ q, 0 < q → Clock d a q → 2^e ≤ q
  white : White d a
  flip : ∀ t, d (a+1) (t+2^e) = !(d (a+1) t)

def NextWhite (d : Nat → Column) (a b : Nat) :=
  a < b ∧ White d b ∧ ∀ i, a < i → i < b → ¬ White d i

/-- Both ends of the closed run belong to the window at the same tick s. -/
def Catch (d : Nat → Column) (a c s : Nat) :=
  ∃ j n, a ≤ j ∧ j+1+n ≤ c ∧ Reset (fun i => d i s) j n

/-- A white middle wheel cannot be strictly inside the black run. Thus a
catch in the combined window occurs wholly in one of its two stretches. -/
theorem catch_split {d : Nat → Column} {a b c s : Nat} (hab : a ≤ b) (hbc : b ≤ c)
    (white : d b s = false) : Catch d a c s ↔ Catch d a b s ∨ Catch d b c s := by
  constructor
  · rintro ⟨j, n, ha, hc, reset⟩
    by_cases left : j+1+n ≤ b
    · exact Or.inl ⟨j, n, ha, left, reset⟩
    by_cases right : b ≤ j
    · exact Or.inr ⟨j, n, right, hc, reset⟩
    have black := reset.2.2.1 (b-(j+1)) (by omega)
    rw [show j+1+(b-(j+1)) = b by omega] at black
    exact absurd (white.symm.trans black) (by decide)
  · rintro (⟨j, n, ha, hb, reset⟩ | ⟨j, n, hb, hc, reset⟩)
    · exact ⟨j, n, ha, Nat.le_trans hb hbc, reset⟩
    · exact ⟨j, n, Nat.le_trans hab hb, hc, reset⟩

/-- The first relaxation of the doubling lemma, in its rooted strip form. -/
def DLMinusOne : Prop := ∀ (d : Nat → Column), Recurrence d → d 0 0 = true →
  PrefixClocks d → ∀ a e b c, FirstLoss d a e → NextWhite d a b →
    NextWhite d b c → ∀ s, Catch d a c s

theorem unbounded_first_losses {d : Nat → Column} (hd : Recurrence d)
    (h0 : d 0 0 = true) (clocks : PrefixClocks d) (lo : Nat) :
    ∃ a e, lo ≤ a ∧ FirstLoss d a e := by
  have recurrent : ∀ i, ∃ p, 0 < p ∧ PeriodFrom (d i) 0 p := by
    intro i
    obtain ⟨p, hp, hclock⟩ := clocks i
    exact ⟨p, hp, hclock i (by omega)⟩
  obtain ⟨e, clock, least⟩ := dyadic_prefix_clock hd h0 recurrent (lo+1)
  obtain ⟨a, ha, _, clockA, white, flip⟩ :=
    first_clock_loss hd h0 recurrent (Nat.two_pow_pos e) (by omega : 1 ≤ lo+1) clock
  exact ⟨a, e, by omega, clockA,
    fun q hq hclock => least q hq (fun i hi => hclock i (by omega)), white, flip⟩

theorem exists_next_white {d : Nat → Column} (hd : Recurrence d)
    (h0 : d 0 0 = true) (clocks : PrefixClocks d) (a : Nat) :
    ∃ b, NextWhite d a b := by
  obtain ⟨b, hab, white, black⟩ := unbounded_anchors hd h0 clocks (a+1)
  clear black
  change White d b at white
  classical
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases earlier : ∃ i, a < i ∧ i < b ∧ White d i
    · obtain ⟨i, hai, hib, hi⟩ := earlier
      exact ih i hib hai hi
    · exact ⟨b, hab, white, fun i hai hib hi => earlier ⟨i, hai, hib, hi⟩⟩

/-- The window argument only uses unbounded starts and a catch in the
prescribed phase. Window choices can depend on the strip and the cutoff. -/
theorem lInfinity_of_windows
    (windows : ∀ (d : Nat → Column), Recurrence d → d 0 0 = true → PrefixClocks d →
      ∀ lo, ∃ a c, lo ≤ a ∧ ∀ s, Catch d a c s) : LInfinity := by
  intro d hd h0 clocks s lo
  obtain ⟨a, c, ha, catches⟩ := windows d hd h0 clocks lo
  obtain ⟨j, n, hj, _, reset⟩ := catches s
  exact ⟨j, n, Nat.le_trans ha hj, reset⟩

theorem lInfinity_of_dlMinusOne (h : DLMinusOne) : LInfinity := by
  apply lInfinity_of_windows
  intro d hd h0 clocks lo
  obtain ⟨a, e, ha, loss⟩ := unbounded_first_losses hd h0 clocks lo
  obtain ⟨b, hab⟩ := exists_next_white hd h0 clocks a
  obtain ⟨c, hbc⟩ := exists_next_white hd h0 clocks b
  exact ⟨a, c, ha, h d hd h0 clocks a e b c loss hab hbc⟩

/-- The kit's explicit settling-age witness for the physical every-k target. -/
theorem everyK_of_dlMinusOne (h : DLMinusOne) :
    EveryK (fun k => settlingBound (widthFor (cap_of_unbounded_resets
      (lInfinity_of_dlMinusOne h)) k)) :=
  Rule30EveryKInverse.conditional_every_k _


def DL : Prop := ∀ (d : Nat → Column), Recurrence d → d 0 0 = true →
  PrefixClocks d → ∀ a e b, FirstLoss d a e → NextWhite d a b → ∀ s, Catch d a b s

theorem dlMinusOne_of_dl (h : DL) : DLMinusOne := by
  intro d hd h0 clocks a e b c loss hab hbc s
  exact (catch_split (Nat.le_of_lt hab.1) (Nat.le_of_lt hbc.1) (hab.2.1 s)).mpr
    (Or.inl (h d hd h0 clocks a e b loss hab s))

theorem firstLoss_cascade_and_immediate_catch {d : Nat → Column} (hd : Recurrence d)
    (clocks : PrefixClocks d) {a e b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) :
    (∀ t, d (a + 2) t = true) ∧ (∀ t, d (a + 3) (t + 1) = !(d (a + 1) t)) ∧ a + 4 ≤ b ∧
    (∀ t, d (a + 1) t = true → d (a + 1) (t + 1) = false → Catch d a b (t + 1)) ∧
    (∃ s, 1 ≤ s ∧ s ≤ 2 ^ (e + 1) ∧ Catch d a b s) ∧
    (∀ t, d (a + 1) t = true → d (a + 4) (t + 2) = !(d (a + 4) (t + 1))) := by
  have hex_t : ∃ t1, d (a + 1) t1 = true := by
    cases h0 : d (a + 1) 0 with
    | true => exact ⟨0, h0⟩
    | false => exact ⟨2 ^ e, by have hf := loss.flip 0; simp [h0] at hf; exact hf⟩
  have hex_f : ∃ t0, d (a + 1) t0 = false := by
    cases h0 : d (a + 1) 0 with
    | false => exact ⟨0, h0⟩
    | true => exact ⟨2 ^ e, by have hf := loss.flip 0; simp [h0] at hf; exact hf⟩
  have hcol2 : ∀ t, d (a + 2) t = true := by
    obtain ⟨t1, ht1⟩ := hex_t
    have hstep : ∀ s, d (a + 2) (s + 1) = (d (a + 1) s || d (a + 2) s) := fun s => by
      rw [hd.2.2 a s, loss.white s]; cases d (a + 1) s || d (a + 2) s <;> rfl
    have hstay : ∀ k, d (a + 2) (t1 + 1 + k) = true := by
      intro k; induction k with
      | zero => simp [hstep t1, ht1]
      | succ k ih => rw [show t1 + 1 + (k + 1) = (t1 + 1 + k) + 1 by omega, hstep, ih, Bool.or_true]
    obtain ⟨p, hp, hcp⟩ := clocks (a + 2)
    intro t
    have hm := period_mul (hcp (a + 2) (Nat.le_refl _)) (t1 + 1) t (Nat.zero_le t)
    have hp1 : t1 + 1 ≤ (t1 + 1) * p := by simpa using Nat.mul_le_mul_left (t1 + 1) hp
    have htr := hstay (t + (t1 + 1) * p - (t1 + 1))
    rw [show t1 + 1 + (t + (t1 + 1) * p - (t1 + 1)) = t + (t1 + 1) * p by omega] at htr
    exact hm.symm.trans htr
  have hcol3 : ∀ t, d (a + 3) (t + 1) = !(d (a + 1) t) := fun t => by
    rw [show a + 3 = (a + 1) + 2 by omega, hd.2.2 (a + 1) t, hcol2 t, Bool.true_or]
    cases d (a + 1) t <;> rfl
  have hb4 : a + 4 ≤ b := by
    have hlt := hab.1; have hbw := hab.2.1
    have h1 : b ≠ a + 1 := fun h => by
      subst h; obtain ⟨t1, ht1⟩ := hex_t; exact absurd ((hbw t1).symm.trans ht1) (by decide)
    have h2 : b ≠ a + 2 := fun h => by
      subst h; exact absurd ((hbw 0).symm.trans (hcol2 0)) (by decide)
    have h3 : b ≠ a + 3 := fun h => by
      subst h; obtain ⟨t0, ht0⟩ := hex_f; have hc := hcol3 t0; rw [ht0] at hc
      exact absurd ((hbw (t0 + 1)).symm.trans hc) (by decide)
    omega
  have hc10 : ∀ t, d (a + 1) t = true → d (a + 1) (t + 1) = false → Catch d a b (t + 1) := by
    intro t ht0 ht1
    refine ⟨a + 1, 1, by omega, by omega, ⟨by decide, ht1, ?_, ?_⟩⟩
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      dsimp only
      rw [show a + 1 + 1 + 0 = a + 2 by omega]
      exact hcol2 (t + 1)
    · dsimp only
      rw [show a + 1 + 1 + 1 = a + 3 by omega, hcol3 t, ht0]
      rfl
  have hex_tr : ∀ m u, 0 < m → d (a + 1) u = true → d (a + 1) (u + m) = false →
      ∃ t, u ≤ t ∧ t < u + m ∧ d (a + 1) t = true ∧ d (a + 1) (t + 1) = false := by
    intro m; induction m with
    | zero => intro _ hm; omega
    | succ m ih =>
      intro u _ hu hum
      cases hn : d (a + 1) (u + 1) with
      | false => exact ⟨u, by omega, by omega, hu, hn⟩
      | true =>
        cases m with
        | zero => exact absurd (hn.symm.trans hum) (by decide)
        | succ m' =>
          have hum' : d (a + 1) ((u + 1) + (m' + 1)) = false := by
            rw [show (u + 1) + (m' + 1) = u + (m' + 1 + 1) by omega]; exact hum
          obtain ⟨t, h1, h2, h3, h4⟩ := ih (u + 1) (by omega) hn hum'
          exact ⟨t, by omega, by omega, h3, h4⟩
  have hex_c : ∃ s, 1 ≤ s ∧ s ≤ 2 ^ (e + 1) ∧ Catch d a b s := by
    have hP : 0 < 2 ^ e := Nat.two_pow_pos e
    have hp2 : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by rw [Nat.pow_succ]; omega
    cases h0 : d (a + 1) 0 with
    | true =>
      have hf : d (a + 1) (0 + 2 ^ e) = false := by
        rw [Nat.zero_add]; have := loss.flip 0; simp [h0] at this; exact this
      obtain ⟨t, _, hlt, ht_t, ht_f⟩ := hex_tr (2 ^ e) 0 hP h0 hf
      exact ⟨t + 1, by omega, by omega, hc10 t ht_t ht_f⟩
    | false =>
      have htP : d (a + 1) (2 ^ e) = true := by have := loss.flip 0; simp [h0] at this; exact this
      have hf2 : d (a + 1) (2 ^ e + 2 ^ e) = false := by have := loss.flip (2 ^ e); simp [htP] at this; exact this
      obtain ⟨t, _, hlt, ht_t, ht_f⟩ := hex_tr (2 ^ e) (2 ^ e) hP htP hf2
      exact ⟨t + 1, by omega, by omega, hc10 t ht_t ht_f⟩
  refine ⟨hcol2, hcol3, hb4, hc10, hex_c, fun t ht => ?_⟩
  have hc3 := hcol3 t; rw [ht] at hc3
  rw [show a + 4 = (a + 2) + 2 by omega, hd.2.2 (a + 2) (t + 1), hcol2 (t + 1), hc3]
  cases d (a + 4) (t + 1) <;> rfl

private def backColPair (p : Column × Column) : Column × Column :=
  (fun t => xor (p.2 (t + 1)) (p.1 t || p.2 t), p.1)

theorem unpointed_periodic_white_return (g : Nat → Column) {L : Nat} (hL : 0 < L)
    (hrec : ∀ i t, g (i + 2) (t + 1) = xor (g i t) (g (i + 1) t || g (i + 2) t))
    (hper : ∀ i, PeriodFrom (g i) 0 L) (hw0 : White g 0) :
    ∃ b, 1 ≤ b ∧ b ≤ 2 ^ L * 2 ^ L ∧ NextWhite g 0 b := by
  have hback : ∀ k, backColPair (g (k + 1), g (k + 2)) = (g k, g (k + 1)) := fun k => by
    apply Prod.ext
    · funext t; dsimp [backColPair]; rw [hrec k t]
      cases g k t <;> cases (g (k + 1) t || g (k + 2) t) <;> rfl
    · rfl
  have hpull : ∀ i j, i < j → (g (i + 1), g (i + 2)) = (g (j + 1), g (j + 2)) →
      (g 0, g 1) = (g (j - i), g (j - i + 1)) := by
    intro i; induction i with
    | zero =>
      intro j _ heq
      have hs := congrArg backColPair heq
      rw [hback 0, hback j] at hs
      simpa using hs
    | succ i ih =>
      intro j hj heq; obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hs := congrArg backColPair heq; rw [hback (i + 1), hback (j' + 1)] at hs
      simpa [show j' + 1 - (i + 1) = j' - i by omega] using ih j' (by omega) hs
  let M := 2 ^ L * 2 ^ L
  let enc : Nat → Nat := fun k =>
    Rule30LeftUnbounded.code (g (k + 1)) L * 2 ^ L + Rule30LeftUnbounded.code (g (k + 2)) L
  have henc_lt : ∀ k, enc k < M := fun k => by
    have h1 := Rule30LeftUnbounded.code_lt (g (k + 1)) L
    have h2 := Rule30LeftUnbounded.code_lt (g (k + 2)) L
    have hm := Nat.mul_le_mul_right (2 ^ L) (show Rule30LeftUnbounded.code (g (k + 1)) L + 1 ≤ 2 ^ L by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm; dsimp [enc, M]; omega
  have hex_col : ∃ i j, i < j ∧ j ≤ M ∧ enc i = enc j := by
    apply Classical.byContradiction; intro hno
    have hinj : ∀ i j, i < M + 1 → j < M + 1 → enc i = enc j → i = j := fun i j hi hj heq => by
      by_cases hlt : i < j
      · exact absurd ⟨i, j, hlt, by omega, heq⟩ hno
      · by_cases hgt : j < i
        · exact absurd ⟨j, i, hgt, by omega, heq.symm⟩ hno
        · omega
    have := Rule30LeftUnbounded.pigeonhole M (M + 1) enc (fun i _ => henc_lt i) hinj; omega
  obtain ⟨i, j, hij, hjM, heq⟩ := hex_col
  have hc_pair : Rule30LeftUnbounded.code (g (i + 1)) L = Rule30LeftUnbounded.code (g (j + 1)) L ∧
      Rule30LeftUnbounded.code (g (i + 2)) L = Rule30LeftUnbounded.code (g (j + 2)) L := by
    dsimp [enc] at heq
    have b1 := Rule30LeftUnbounded.code_lt (g (i + 2)) L
    have b2 := Rule30LeftUnbounded.code_lt (g (j + 2)) L
    have ha : Rule30LeftUnbounded.code (g (i + 1)) L = Rule30LeftUnbounded.code (g (j + 1)) L := by
      by_cases hlt : Rule30LeftUnbounded.code (g (i + 1)) L < Rule30LeftUnbounded.code (g (j + 1)) L
      · have hle1 : Rule30LeftUnbounded.code (g (i + 1)) L + 1 ≤ Rule30LeftUnbounded.code (g (j + 1)) L := hlt
        have hm := Nat.mul_le_mul_right (2 ^ L) hle1; rw [Nat.add_mul, Nat.one_mul] at hm; omega
      · by_cases hgt : Rule30LeftUnbounded.code (g (j + 1)) L < Rule30LeftUnbounded.code (g (i + 1)) L
        · have hle2 : Rule30LeftUnbounded.code (g (j + 1)) L + 1 ≤ Rule30LeftUnbounded.code (g (i + 1)) L := hgt
          have hm := Nat.mul_le_mul_right (2 ^ L) hle2; rw [Nat.add_mul, Nat.one_mul] at hm; omega
        · omega
    rw [ha] at heq; exact ⟨ha, by omega⟩
  have hcol_eq : ∀ u v, Rule30LeftUnbounded.code (g u) L = Rule30LeftUnbounded.code (g v) L → g u = g v := by
    intro u v hc; funext t
    have hfg := Rule30LeftUnbounded.code_inj (g u) (g v) L hc (t % L) (Nat.mod_lt t hL)
    have hd : t % L + (t / L) * L = t := by simpa [Nat.mul_comm] using Nat.mod_add_div t L
    have hu := period_mul (hper u) (t / L) (t % L) (Nat.zero_le _)
    have hv := period_mul (hper v) (t / L) (t % L) (Nat.zero_le _)
    rw [hd] at hu hv; exact hu.trans (hfg.trans hv.symm)
  have hzero := hpull i j hij (Prod.ext (hcol_eq _ _ hc_pair.1) (hcol_eq _ _ hc_pair.2))
  have hw_ji : White g (j - i) := fun t => (congrFun (congrArg Prod.fst hzero) t).symm.trans (hw0 t)
  have hmin : ∀ b0, 0 < b0 → b0 ≤ M → White g b0 → ∃ b, 1 ≤ b ∧ b ≤ M ∧ NextWhite g 0 b := by
    intro b0
    induction b0 using Nat.strongRecOn with
    | ind b0 ih =>
      intro hbp hbl hwb
      classical
      by_cases he : ∃ k, 0 < k ∧ k < b0 ∧ White g k
      · obtain ⟨k, hk0, hkb, hwk⟩ := he; exact ih k hkb hk0 (by omega) hwk
      · exact ⟨b0, hbp, hbl, ⟨hbp, hwb, fun k hk0 hkb hwk => he ⟨k, hk0, hkb, hwk⟩⟩⟩
  exact hmin (j - i) (by omega) (by omega) hw_ji

def ceMask (r : Nat) : Nat :=
  match r % 7 with | 0 => 0 | 1 => 7 | 2 => 15 | 3 => 1 | 4 => 5 | 5 => 9 | _ => 9
def ceFin (i28 t4 : Nat) : Bool := (ceMask i28).testBit ((t4 + 3 * (i28 / 7)) % 4)
def ceStrip (i t : Nat) : Bool := ceFin (i % 28) (t % 4)

private theorem ceFin_rec : ∀ i, i < 28 → ∀ t, t < 4 →
    ceFin ((i + 2) % 28) ((t + 1) % 4) =
      xor (ceFin i t) (ceFin ((i + 1) % 28) t || ceFin ((i + 2) % 28) t) := by decide +kernel
private theorem ceFin_white : ∀ t, t < 4 → ceFin 0 t = false ∧ ceFin 7 t = false ∧ ceFin 14 t = false := by decide +kernel
private theorem ceFin_nonwhite : ∀ i, i < 14 → i ≠ 0 → i ≠ 7 → ∃ t, t < 4 ∧ ceFin i t = true := by decide +kernel
def ceReset1 (j n : Nat) : Bool :=
  (n % 3 == 1) && !(ceStrip j 1) && !(ceStrip (j + 1 + n) 1) && (List.range n).all (fun k => ceStrip (j + 1 + k) 1)
private theorem ceReset1_false : ∀ j, j ≤ 14 → ∀ n, n ≤ 14 → ceReset1 j n = false := by decide +kernel

theorem two_interval_fails_without_firstLoss :
    (∀ i t, ceStrip (i + 2) (t + 1) = xor (ceStrip i t) (ceStrip (i + 1) t || ceStrip (i + 2) t)) ∧
    (∀ m, Clock ceStrip m 4) ∧ White ceStrip 0 ∧ NextWhite ceStrip 0 7 ∧ NextWhite ceStrip 7 14 ∧
    ¬ Catch ceStrip 0 14 1 := by
  refine ⟨fun i t => ?_, fun _ _ _ u _ => ?_, fun t => ?_, ⟨by omega, fun t => ?_, fun i h1 h2 hw => ?_⟩,
    ⟨by omega, fun t => ?_, fun i h1 h2 hw => ?_⟩, ?_⟩
  · have h := ceFin_rec (i % 28) (Nat.mod_lt i (by omega)) (t % 4) (Nat.mod_lt t (by omega))
    simpa [ceStrip, show ((i % 28) + 1) % 28 = (i + 1) % 28 by omega,
      show ((i % 28) + 2) % 28 = (i + 2) % 28 by omega, show ((t % 4) + 1) % 4 = (t + 1) % 4 by omega] using h
  · unfold ceStrip; rw [show (u + 4) % 4 = u % 4 by omega]
  · unfold ceStrip; exact (ceFin_white (t % 4) (Nat.mod_lt t (by omega))).1
  · unfold ceStrip; exact (ceFin_white (t % 4) (Nat.mod_lt t (by omega))).2.1
  · obtain ⟨t, ht4, ht⟩ := ceFin_nonwhite i (by omega) (by omega) (by omega)
    have hw_t := hw t; unfold ceStrip at hw_t
    rw [Nat.mod_eq_of_lt (show i < 28 by omega), Nat.mod_eq_of_lt ht4] at hw_t
    exact absurd (hw_t.symm.trans ht) (by decide)
  · unfold ceStrip; exact (ceFin_white (t % 4) (Nat.mod_lt t (by omega))).2.2
  · obtain ⟨t, ht4, ht⟩ := ceFin_nonwhite i (by omega) (by omega) (by omega)
    have hw_t := hw t; unfold ceStrip at hw_t
    rw [Nat.mod_eq_of_lt (show i < 28 by omega), Nat.mod_eq_of_lt ht4] at hw_t
    exact absurd (hw_t.symm.trans ht) (by decide)
  · rintro ⟨j, n, _, hjn, hm, hj0, hmid, hj1⟩
    have htrue : ceReset1 j n = true := by
      unfold ceReset1
      dsimp only at hj0 hmid hj1
      simp [hm, hj0, hj1, List.all_eq_true]
      intro k hk; exact hmid k hk
    have hfalse := ceReset1_false j (by omega) n (by omega)
    exact absurd (hfalse.symm.trans htrue) (by decide)

def nfaKey (d : Nat) : Nat := if d < 2 then d else 2 + d % 2
def nfaMaskA (key : Nat) : Nat := match key with | 0 => 12 | 1 => 28 | 2 => 4 | _ => 30
def nfaMaskB (key : Nat) : Nat := match key with | 0 => 22 | 1 => 6 | 2 => 30 | _ => 4
def nfaWinA (r k j : Nat) : Bool := (nfaMaskA (nfaKey (r - 1 - j))).testBit k
def nfaWinB (r k j : Nat) : Bool := (nfaMaskB (nfaKey (r - 1 - j))).testBit k

private def nfaNextKey (c : Nat) : Nat := match c with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 2

private theorem nfa_key_succ (d : Nat) : nfaKey (d + 1) = nfaNextKey (nfaKey d) := by
  by_cases h0 : d = 0
  · subst h0; rfl
  · by_cases h1 : d = 1
    · subst h1; rfl
    · have hd2 : ¬ d < 2 := by omega
      have hd3 : ¬ d + 1 < 2 := by omega
      unfold nfaKey
      simp only [hd2, hd3, ↓reduceIte]
      by_cases hev : d % 2 = 0
      · have hod : (d + 1) % 2 = 1 := by omega
        rw [hev, hod]; rfl
      · have h1m : d % 2 = 1 := by omega
        have hev1 : (d + 1) % 2 = 0 := by omega
        rw [h1m, hev1]; rfl

private theorem nfa_key_props :
    (∀ c, c < 4 → (nfaMaskA c).testBit 0 = false ∧ (nfaMaskB c).testBit 0 = false ∧
      (nfaMaskB c).testBit 1 = !((nfaMaskA c).testBit 1) ∧
      (nfaMaskA c).testBit 2 = true ∧ (nfaMaskB c).testBit 2 = true ∧
      (nfaMaskA c).testBit 5 = false ∧ (nfaMaskB c).testBit 5 = false) ∧
    (∀ c, c < 4 → ∀ k, k < 4 →
      let cp := nfaNextKey c
      (nfaMaskA c).testBit (k + 2) = xor ((nfaMaskA cp).testBit k)
        (((nfaMaskA cp).testBit (k + 1)) || ((nfaMaskA cp).testBit (k + 2))) ∧
      (nfaMaskB c).testBit (k + 2) = xor ((nfaMaskB cp).testBit k)
        (((nfaMaskB cp).testBit (k + 1)) || ((nfaMaskB cp).testBit (k + 2)))) := by decide +kernel

private def nfaTopReset (j n : Nat) : Bool :=
  (n % 3 == 1) && !((12 : Nat).testBit j) && !((12 : Nat).testBit (j + 1 + n)) &&
    (List.range n).all (fun k => (12 : Nat).testBit (j + 1 + k))
private theorem nfaTopReset_false : ∀ j, j ≤ 5 → ∀ n, n ≤ 5 → nfaTopReset j n = false := by decide +kernel

theorem local_paired_nfa_escapes_in_five (r : Nat) (_hr : 1 ≤ r) :
    (∀ j, j < r → nfaWinA r 0 j = false ∧ nfaWinB r 0 j = false ∧
      nfaWinB r 1 j = !(nfaWinA r 1 j) ∧ nfaWinA r 2 j = true ∧ nfaWinB r 2 j = true ∧
      nfaWinA r 5 j = false ∧ nfaWinB r 5 j = false) ∧
    (∀ k, k < 4 → ∀ j, j + 1 < r →
      nfaWinA r (k + 2) (j + 1) = xor (nfaWinA r k j) (nfaWinA r (k + 1) j || nfaWinA r (k + 2) j) ∧
      nfaWinB r (k + 2) (j + 1) = xor (nfaWinB r k j) (nfaWinB r (k + 1) j || nfaWinB r (k + 2) j)) ∧
    ¬ ∃ j n, j + 1 + n ≤ 5 ∧ Reset (fun k => nfaWinA r k (r - 1)) j n := by
  have hk_lt : ∀ d, nfaKey d < 4 := fun d => by unfold nfaKey; split <;> omega
  refine ⟨fun j _ => by unfold nfaWinA nfaWinB; exact nfa_key_props.1 _ (hk_lt _), fun k hk j hj => ?_, ?_⟩
  · have hd : r - 1 - j = (r - 1 - (j + 1)) + 1 := by omega
    let d1 := r - 1 - (j + 1)
    have hstep := nfa_key_props.2 (nfaKey d1) (hk_lt d1) k hk
    unfold nfaWinA nfaWinB
    rw [hd, nfa_key_succ d1]
    exact hstep
  · rintro ⟨j, n, hjn, hm, hj0, hmid, hj1⟩
    have hsub : r - 1 - (r - 1) = 0 := by omega
    dsimp only [nfaWinA] at hj0 hmid hj1
    rw [hsub] at hj0 hmid hj1
    change (12 : Nat).testBit j = false at hj0
    change (12 : Nat).testBit (j + 1 + n) = false at hj1
    have htr : nfaTopReset j n = true := by
      unfold nfaTopReset
      simp [hm, hj0, hj1, List.all_eq_true]
      intro k hk; exact hmid k hk
    exact absurd ((nfaTopReset_false j (by omega) n (by omega)).symm.trans htr) (by decide)

end Ruliology.CellularAutomata.Rule30RelaxedWindows
