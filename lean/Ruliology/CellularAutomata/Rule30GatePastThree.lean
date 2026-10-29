module
public import Ruliology.CellularAutomata.Rule30GateInverseMerge

/-! Three legal gate bits of temporal past can be edited without changing the far spatial tail.
The theorem is uniform in the entire future but fixes the edited past length to three. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GatePastThree
open Rule30ZeroBoundary Rule30GateInverseMerge

def head (p : Fin 8) (j : Nat) : Bool :=
  if j%2=0 then true else !(Nat.testBit p.val (2-j/2))

def history (p : Fin 8) (L : Nat → Bool) : Nat → Nat → Bool
  | 0 => L
  | j+1 => back (head p j) (history p L j)

def Allowed (w : Nat) (p : Fin 8) : Prop :=
  ∀ i : Fin 3, (((p.val ||| (w <<< 3)) >>> i.val) &&& 255) ∈ words

def modelData : Nat → List Nat
  | 33 => [1639084, 916166, 412290, 223994, 33172554, 38520682, 57442858, 1639084, 916166, 412290, 223994, 33172554, 38520682, 57442860, 1639084, 916166, 412290, 223994, 33172556, 38520710, 57309442, 1639084, 916166, 412290, 223994, 33172556, 38520710, 57308404, 1639084, 916166, 412788, 231318, 33354978, 19306298, 96655818, 1639084, 916166, 412788, 231318, 33354978, 19306298, 96655820, 1639084, 916166, 412788, 231318, 33354964, 19306582, 96669538, 1639084, 916166, 412788, 231318, 33354964, 19306582, 96669524]
  | 36 => [1373258, 1480554, 6480426, 3881898, 1166506, 65046186, 20906666, 1373258, 1480554, 6480426, 3881898, 1166506, 65046186, 20906668, 1373258, 1480554, 6480426, 3881898, 1166508, 65046214, 20906626, 1373258, 1480554, 6480426, 3881898, 1166508, 65046214, 20903028, 1373258, 1480554, 6480428, 3881926, 1166466, 65046266, 20902986, 1373258, 1480554, 6480428, 3881926, 1166466, 65046266, 20902988, 1373258, 1480554, 6480428, 3881926, 1165940, 64908182, 40119522, 1373258, 1480554, 6480428, 3881926, 1165940, 64908182, 40119508]
  | 66 => [412290, 223994, 8006730, 4966250, 23888426, 21429162, 91507882, 412290, 223994, 8006730, 4966250, 23888426, 21429162, 91507884, 412290, 223994, 8006730, 4966250, 23888428, 21429190, 91507842, 412290, 223994, 8006730, 4966250, 23888428, 21429190, 91507316, 412290, 223994, 8006732, 4966278, 23755010, 36392442, 61965898, 412290, 223994, 8006732, 4966278, 23755010, 36392442, 61965900, 412290, 223994, 8006732, 4966278, 23753972, 36411030, 61661922, 412290, 223994, 8006732, 4966278, 23753972, 36411030, 61661908]
  | 72 => [188970, 3881898, 1166506, 14714538, 20906666, 30014122, 107891370, 188970, 3881898, 1166506, 14714538, 20906666, 30014122, 107891372, 188970, 3881898, 1166506, 14714538, 20906668, 30014150, 107891330, 188970, 3881898, 1166506, 14714538, 20906668, 30014150, 107891828, 188970, 3881898, 1166508, 14714566, 20906626, 30014202, 107891786, 188970, 3881898, 1166508, 14714566, 20906626, 30014202, 107891788, 188970, 3881898, 1166508, 14714566, 20903028, 34772886, 64672994, 188970, 3881898, 1166508, 14714566, 20903028, 34772886, 64672980]
  | 132 => [1715274, 771946, 7111210, 4651946, 24399018, 26707626, 14221994, 1715274, 771946, 7111210, 4651946, 24399018, 26707626, 14221996, 1715274, 771946, 7111210, 4651946, 24399020, 26707654, 14221954, 1715274, 771946, 7111210, 4651946, 24399020, 26707654, 13956212, 1715274, 771946, 7111212, 4651974, 24398978, 26707706, 13956170, 1715274, 771946, 7111212, 4651974, 24398978, 26707706, 13956172, 1715274, 771946, 7111212, 4651974, 24398452, 26700694, 14822626, 1715274, 771946, 7111212, 4651974, 24398452, 26700694, 14822612]
  | 144 => [1166506, 2131626, 4129450, 13236906, 7228074, 3369642, 1714858, 1166506, 2131626, 4129450, 13236906, 7228074, 3369642, 1714860, 1166506, 2131626, 4129450, 13236906, 7228076, 3369670, 1714818, 1166506, 2131626, 4129450, 13236906, 7228076, 3369670, 1715316, 1166506, 2131626, 4129452, 13236934, 7228034, 3369722, 1715274, 1166506, 2131626, 4129452, 13236934, 7228034, 3369722, 1715276, 1166506, 2131626, 4129452, 13236934, 7228532, 3377046, 1897698, 1166506, 2131626, 4129452, 13236934, 7228532, 3377046, 1897684]
  | 264 => [819754, 457642, 7621802, 9930410, 14221994, 42859178, 50743978, 819754, 457642, 7621802, 9930410, 14221994, 42859178, 50743980, 819754, 457642, 7621802, 9930410, 14221996, 42859206, 50743938, 819754, 457642, 7621802, 9930410, 14221996, 42859206, 50744436, 819754, 457642, 7621804, 9930438, 14221954, 42859258, 50744394, 819754, 457642, 7621804, 9930438, 14221954, 42859258, 50744396, 819754, 457642, 7621804, 9930438, 13956212, 5674902, 123917538, 819754, 457642, 7621804, 9930438, 13956212, 5674902, 123917524]
  | 265 => [819756, 457670, 7621762, 9930490, 13956170, 5674858, 123920938, 819756, 457670, 7621762, 9930490, 13956170, 5674858, 123920940, 819756, 457670, 7621762, 9930490, 13956172, 5674886, 123918594, 819756, 457670, 7621762, 9930490, 13956172, 5674886, 123917556, 819756, 457670, 7621236, 9923478, 14822626, 54249274, 30046666, 819756, 457670, 7621236, 9923478, 14822626, 54249274, 30046668, 819756, 457670, 7621236, 9923478, 14822612, 54241366, 30191458, 819756, 457670, 7621236, 9923478, 14822612, 54241366, 30191444]
  | 289 => [2032300, 654022, 7228034, 3369722, 1715274, 771946, 132940330, 2032300, 654022, 7228034, 3369722, 1715274, 771946, 132940332, 2032300, 654022, 7228034, 3369722, 1715276, 771974, 132806914, 2032300, 654022, 7228034, 3369722, 1715276, 771974, 132805876, 2032300, 654022, 7228532, 3377046, 1897698, 65443642, 37935562, 2032300, 654022, 7228532, 3377046, 1897698, 65443642, 37935564, 2032300, 654022, 7228532, 3377046, 1897684, 65443926, 37949282, 2032300, 654022, 7228532, 3377046, 1897684, 65443926, 37949268]
  | 528 => [1330346, 1541802, 5833386, 9304746, 17189546, 33778346, 66726570, 1330346, 1541802, 5833386, 9304746, 17189546, 33778346, 66726572, 1330346, 1541802, 5833386, 9304746, 17189548, 33778374, 66726530, 1330346, 1541802, 5833386, 9304746, 17189548, 33778374, 66727028, 1330346, 1541802, 5833388, 9304774, 17189506, 33778426, 66726986, 1330346, 1541802, 5833388, 9304774, 17189506, 33778426, 66726988, 1330346, 1541802, 5833388, 9304774, 17190004, 33785750, 66909410, 1330346, 1541802, 5833388, 9304774, 17190004, 33785750, 66909396]
  | 530 => [1330306, 1541882, 5567562, 5674858, 23257642, 37436330, 68275370, 1330306, 1541882, 5567562, 5674858, 23257642, 37436330, 68275372, 1330306, 1541882, 5567562, 5674858, 23257644, 37436358, 68275330, 1330306, 1541882, 5567562, 5674858, 23257644, 37436358, 68274804, 1330306, 1541882, 5567564, 5674886, 23255298, 37391866, 63637066, 1330306, 1541882, 5567564, 5674886, 23255298, 37391866, 63637068, 1330306, 1541882, 5567564, 5674886, 23254260, 37508758, 61301474, 1330306, 1541882, 5567564, 5674886, 23254260, 37508758, 61301460]
  | 578 => [936578, 3369722, 1715274, 771946, 32277034, 38206378, 57953450, 936578, 3369722, 1715274, 771946, 32277034, 38206378, 57953452, 936578, 3369722, 1715274, 771946, 32277036, 38206406, 57953410, 936578, 3369722, 1715274, 771946, 32277036, 38206406, 57952884, 936578, 3369722, 1715276, 771974, 32143618, 19615226, 95520330, 936578, 3369722, 1715276, 771974, 32143618, 19615226, 95520332, 936578, 3369722, 1715276, 771974, 32142580, 19633814, 95216354, 936578, 3369722, 1715276, 771974, 32142580, 19633814, 95216340]
  | _ => []

def model (c : HistoryCertificate) (p : Fin 8) (j k : Nat) : Bool :=
  Nat.testBit ((modelData c.gate)[7*p.val+j]!) k

def Valid (c : HistoryCertificate) : Prop :=
  (∀ p : Fin 8, ∀ k : Fin 21, 1 ≤ k.val → model c p 0 k = tabRow c k) ∧
  (∀ p : Fin 8, ∀ j : Fin 6,
    BackValid (model c p j) (head p j) (model c p (j.val+1)) 20) ∧
  (∀ p q : Fin 8, Allowed c.gate p → Allowed c.gate q → ∀ j : Fin 6,
    model c p (j.val+1) 20 = model c q (j.val+1) 20 ∧
    model c p (j.val+1) 21 = model c q (j.val+1) 21)

instance validDecidable : DecidablePred Valid := fun c => by
  unfold Valid Allowed BackValid
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem certificates_valid : ∀ c ∈ historyCertificates, Valid c := by
  decide +kernel

theorem model_sound (L : Nat → Bool) (c : HistoryCertificate)
    (hc : c ∈ historyCertificates)
    (hh : ∀ t, t < 20 → zrow L t 1 = oddPhase c.gate t) (p : Fin 8) :
    ∀ j, j ≤ 6 →
      (∀ k, 1 ≤ k → k ≤ 20 → model c p j k = history p L j k) ∧
      (0 < j → model c p j 21 = history p L j 21) := by
  obtain ⟨hbase,hback,hmerge⟩ := certificates_valid c hc
  have rowmatch := history_row_matches L c (history_certificates_valid c hc).1 hh
  intro j
  induction j with
  | zero =>
      intro hj
      constructor
      · intro k hk hn
        exact (hbase p ⟨k,by omega⟩ hk).trans (rowmatch k hk hn).symm
      · intro hp
        omega
  | succ j ih =>
      intro hj
      have hold := ih (by omega)
      have child : ∀ k, k ≤ 21 → model c p (j+1) k = history p L (j+1) k := by
        intro k hk
        calc
          model c p (j+1) k = back (head p j) (model c p j) k :=
            back_valid_sound _ _ _ 20 (hback p ⟨j,by omega⟩) k (by omega)
          _ = history p L (j+1) k := by
            change back (head p j) (model c p j) k = back (head p j) (history p L j) k
            cases k with
            | zero => rfl
            | succ k =>
                exact (back_congr_pair (head p j) (model c p j) (history p L j) k
                  (fun i hi hn => hold.1 i hi (by omega))).2
      exact ⟨fun k hk hn => child k (by omega),fun hp => child 21 (by omega)⟩

theorem joint_tail (L : Nat → Bool) (p q : Fin 8)
    (h0 : ∀ j, j ≤ 6 → history p L j 20 = history q L j 20)
    (h1 : ∀ j, j ≤ 6 → history p L j 21 = history q L j 21) :
    ∀ k, 20 ≤ k → ∀ j, j ≤ 6 → history p L j k = history q L j k := by
  have key : ∀ i, ∀ j, j ≤ 6 →
      history p L j (20+i) = history q L j (20+i) ∧
      history p L j (20+i+1) = history q L j (20+i+1) := by
    intro i
    induction i with
    | zero => intro j hj; exact ⟨h0 j hj,h1 j hj⟩
    | succ i ih =>
        intro j hj
        constructor
        · simpa only [Nat.add_assoc] using (ih j hj).2
        · cases j with
          | zero => rfl
          | succ j =>
              change xor (history p L j (20+i+1))
                (history p L (j+1) (20+i+1) || history p L (j+1) (20+i)) =
                xor (history q L j (20+i+1))
                (history q L (j+1) (20+i+1) || history q L (j+1) (20+i))
              rw [(ih j (by omega)).2,(ih (j+1) hj).1,(ih (j+1) hj).2]
  intro k hk j hj
  simpa only [Nat.add_sub_of_le hk] using (key (k-20) j hj).1

theorem three_legal_pasts_agree (L : Nat → Bool) (c : HistoryCertificate)
    (hc : c ∈ historyCertificates)
    (hh : ∀ t, t < 20 → zrow L t 1 = oddPhase c.gate t)
    (p q : Fin 8) (hp : Allowed c.gate p) (hq : Allowed c.gate q) :
    ∀ k, 20 ≤ k → history p L 6 k = history q L 6 k := by
  have hm := (certificates_valid c hc).2.2 p q hp hq
  have hs := model_sound L c hc hh
  have hpair : ∀ j, j ≤ 6 →
      history p L j 20 = history q L j 20 ∧ history p L j 21 = history q L j 21 := by
    intro j hj
    cases j with
    | zero => constructor <;> rfl
    | succ j =>
        have hcj := hm ⟨j,by omega⟩
        constructor
        · exact ((hs p (j+1) hj).1 20 (by omega) (by omega)).symm.trans
            (hcj.1.trans ((hs q (j+1) hj).1 20 (by omega) (by omega)))
        · exact ((hs p (j+1) hj).2 (by omega)).symm.trans
            (hcj.2.trans ((hs q (j+1) hj).2 (by omega)))
  intro k hk
  exact joint_tail L p q (fun j hj => (hpair j hj).1)
    (fun j hj => (hpair j hj).2) k hk 6 (by omega)

theorem legal_gate_prefix_edits_agree (L : Nat → Bool) (w : Fin 1024)
    (hw : ∀ i : Fin 3, ((w.val >>> i.val) &&& 255) ∈ words)
    (hh : ∀ t, t < 20 → zrow L t 1 = oddPhase w.val t)
    (p q : Fin 8) (hp : Allowed w.val p) (hq : Allowed w.val q) :
    ∀ k, 20 ≤ k → history p L 6 k = history q L 6 k := by
  obtain ⟨c,hc,hcw⟩ := List.mem_map.mp ((gate_prefix_coverage w).1 hw)
  apply three_legal_pasts_agree L c hc
  · simpa only [hcw] using hh
  · simpa only [hcw] using hp
  · simpa only [hcw] using hq

theorem legal_gate_prefix_edits_finite_iff (L : Nat → Bool) (w : Fin 1024)
    (hw : ∀ i : Fin 3, ((w.val >>> i.val) &&& 255) ∈ words)
    (hh : ∀ t, t < 20 → zrow L t 1 = oddPhase w.val t)
    (p q : Fin 8) (hp : Allowed w.val p) (hq : Allowed w.val q) :
    FinSupp (history p L 6) ↔ FinSupp (history q L 6) := by
  have he := legal_gate_prefix_edits_agree L w hw hh p q hp hq
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 20,fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 20,fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)


/-! The inverse-head description is exactly prepending three bits to the gate. -/
def tracePrepend (b : Bool) (a : Nat → Bool) : Nat → Bool
  | 0 => b
  | t+1 => a t

def oddTrace (G : Nat → Bool) (t : Nat) : Bool :=
  if t%2=0 then !(G (t/2)) else true

def prependGate3 (p : Fin 8) (G : Nat → Bool) (r : Nat) : Bool :=
  if r<3 then Nat.testBit p.val r else G (r-3)

def tracePast3 (p : Fin 8) (a : Nat → Bool) : Nat → Bool :=
  tracePrepend (!(Nat.testBit p.val 0))
    (tracePrepend true (tracePrepend (!(Nat.testBit p.val 1))
      (tracePrepend true (tracePrepend (!(Nat.testBit p.val 2)) (tracePrepend true a)))))

theorem back_lam (b : Bool) (a : Nat → Bool) :
    back b (lam a) = lam (tracePrepend b a) := by
  have ht : ∀ t, zrow (back b (lam a)) t 1 = tracePrepend b a t := by
    intro t
    cases t with
    | zero => rfl
    | succ t =>
        rw [back_trace]
        exact (realization a).1 t
  have hh := (realization (tracePrepend b a)).2 (back b (lam a)) ht
  rw [zrow_back_zero] at hh
  exact hh

theorem history_six_lam (p : Fin 8) (a : Nat → Bool) :
    history p (lam a) 6 = lam (tracePast3 p a) := by
  change back (!(Nat.testBit p.val 0)) (back true
    (back (!(Nat.testBit p.val 1)) (back true
      (back (!(Nat.testBit p.val 2)) (back true (lam a)))))) = _
  simp only [back_lam]
  rfl

theorem trace_past3 (p : Fin 8) (G : Nat → Bool) :
    tracePast3 p (oddTrace G) = oddTrace (prependGate3 p G) := by
  funext t
  by_cases ht : t<6
  · have hx : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨u,rfl⟩ : ∃ u, t=u+6 := ⟨t-6,by omega⟩
    change oddTrace G u = oddTrace (prependGate3 p G) (u+6)
    unfold oddTrace
    rw [show (u+6)%2=u%2 by omega]
    by_cases hu : u%2=0
    · rw [ite_eq_left hu,ite_eq_left hu]
      unfold prependGate3
      rw [ite_eq_right (by omega),show (u+6)/2-3=u/2 by omega]
    · rw [ite_eq_right hu,ite_eq_right hu]

theorem history_gate_prefix (p : Fin 8) (G : Nat → Bool) :
    history p (lam (oddTrace G)) 6 = lam (oddTrace (prependGate3 p G)) := by
  rw [history_six_lam,trace_past3]

theorem reconstructed_gate_prefix_edits_agree (G : Nat → Bool) (w : Fin 1024)
    (hw : ∀ i : Fin 3, ((w.val >>> i.val) &&& 255) ∈ words)
    (hbits : ∀ r : Fin 10, G r = Nat.testBit w.val r)
    (p q : Fin 8) (hp : Allowed w.val p) (hq : Allowed w.val q) :
    ∀ k, 20 ≤ k → lam (oddTrace (prependGate3 p G)) k =
      lam (oddTrace (prependGate3 q G)) k := by
  have hh : ∀ t, t<20 → zrow (lam (oddTrace G)) t 1 = oddPhase w.val t := by
    intro t ht
    rw [(realization (oddTrace G)).1 t]
    unfold oddTrace oddPhase
    by_cases hm : t%2=0
    · rw [ite_eq_left hm,ite_eq_left hm]
      exact congrArg Bool.not (hbits ⟨t/2,by omega⟩)
    · rw [ite_eq_right hm,ite_eq_right hm]
  rw [← history_gate_prefix p G,← history_gate_prefix q G]
  exact legal_gate_prefix_edits_agree (lam (oddTrace G)) w hw hh p q hp hq

theorem reconstructed_gate_prefix_edits_finite_iff (G : Nat → Bool) (w : Fin 1024)
    (hw : ∀ i : Fin 3, ((w.val >>> i.val) &&& 255) ∈ words)
    (hbits : ∀ r : Fin 10, G r = Nat.testBit w.val r)
    (p q : Fin 8) (hp : Allowed w.val p) (hq : Allowed w.val q) :
    FinSupp (lam (oddTrace (prependGate3 p G))) ↔
      FinSupp (lam (oddTrace (prependGate3 q G))) := by
  have he := reconstructed_gate_prefix_edits_agree G w hw hbits p q hp hq
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 20,fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 20,fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)

end Ruliology.CellularAutomata.Rule30GatePastThree
