module
public import Ruliology.CellularAutomata.Rule30PastStrip

/-! Sound finite prefix covers for arbitrary legal gate futures. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GatePastCover
open Rule30ZeroBoundary Rule30PastStrip
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def Prefix (G : Nat → Bool) (m f : Nat) : Prop :=
  ∀ i, i < m → G i = Nat.testBit f i
def prependN (n p : Nat) (G : Nat → Bool) (r : Nat) : Bool :=
  if r < n then Nat.testBit p r else G (r-n)
def finiteGate (n p f : Nat) (r : Nat) : Bool :=
  if r < n then Nat.testBit p r else Nat.testBit f (r-n)
def Allowed (n f p : Nat) : Prop :=
  ∀ i : Fin n, window (finiteGate n p f) i ∈ words

instance allowedDecidable (n f p : Nat) : Decidable (Allowed n f p) := by
  unfold Allowed
  infer_instance

theorem allowed_of_prefix (n m f p : Nat) (G : Nat → Bool)
    (hm : 8 ≤ m) (pref : Prefix G m f) (legal : GateLegal (prependN n p G)) :
    Allowed n f p := by
  intro i
  have eq : window (finiteGate n p f) i = window (prependN n p G) i := by
    apply window_congr
    intro j hj
    unfold finiteGate prependN
    by_cases h : i.val+j < n
    · rw [ite_eq_left h,ite_eq_left h]
    · rw [ite_eq_right h,ite_eq_right h]
      exact (pref (i.val+j-n) (by omega)).symm
  rw [eq]
  exact legal i

theorem trace_prefix (n m f p : Nat) (G : Nat → Bool) (pref : Prefix G m f) :
    ∀ t, t < 2*(n+m) →
      oddTrace (prependN n p G) t = oddTrace (finiteGate n p f) t := by
  intro t ht
  unfold oddTrace
  by_cases he : t%2=0
  · rw [ite_eq_left he,ite_eq_left he]
    unfold prependN finiteGate
    by_cases hp : t/2 < n
    · rw [ite_eq_left hp,ite_eq_left hp]
    · rw [ite_eq_right hp,ite_eq_right hp,pref (t/2-n) (by omega)]
  · rw [ite_eq_right he,ite_eq_right he]

theorem shared_trace_future (n p q : Nat) (G : Nat → Bool) :
    ∀ t, 2*n ≤ t → oddTrace (prependN n p G) t = oddTrace (prependN n q G) t := by
  intro t ht
  unfold oddTrace
  by_cases he : t%2=0
  · rw [ite_eq_left he,ite_eq_left he]
    unfold prependN
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]
  · rw [ite_eq_right he,ite_eq_right he]

structure Leaf where
  length : Nat
  gate : Nat
  edge : Nat
  reference : Nat
  tables : List (List Nat)

def triangle (n : Nat) (c : Leaf) (p : Nat) : Triangle :=
  ⟨2*(n+c.length)+1,c.tables[p]?.getD []⟩

def column (c : Triangle) (k : Nat) : Nat := c.columns[k]?.getD 0

/-- Word arithmetic checks the complete shrinking triangle, without testing
every individual bit separately. The conversion below is kernel proved. -/
def PackedValid (c : Triangle) (a : Nat → Bool) : Prop :=
  column c 0 = 0 ∧
  (∀ t : Fin c.horizon, 1+t.val < c.horizon → cell c 1 t = a t) ∧
  (∀ k : Fin c.horizon, k.val+2 < c.horizon →
    column c (k.val+2) =
      ((column c (k.val+1) >>> 1) ^^^ (column c (k.val+1) ||| column c k)) %
        2^(c.horizon-k.val-2))

instance packedDecidable (c : Triangle) (a : Nat → Bool) : Decidable (PackedValid c a) := by
  unfold PackedValid
  infer_instance

theorem packed_sound (c : Triangle) (a : Nat → Bool) (h : PackedValid c a) : Valid c a := by
  obtain ⟨wall,head,step⟩ := h
  refine ⟨?_,head,?_⟩
  · intro t
    change Nat.testBit (column c 0) t = false
    rw [wall,Nat.zero_testBit]
  · intro k t ht
    change Nat.testBit (column c (k.val+2)) t =
      xor (Nat.testBit (column c (k.val+1)) (t.val+1))
        (Nat.testBit (column c (k.val+1)) t || Nat.testBit (column c k) t)
    rw [step k (by omega)]
    have low : t.val < c.horizon-k.val-2 := by omega
    simp only [Nat.testBit_mod_two_pow,low,decide_true,Bool.true_and,
      Nat.testBit_xor,Nat.testBit_shiftRight,Nat.testBit_or,Nat.add_comm]

def LeafValid (n : Nat) (c : Leaf) : Prop :=
  8 ≤ c.length ∧ c.edge ≤ 2*c.length ∧
  (∀ p : Fin (2^n), Allowed n c.gate p →
    PackedValid (triangle n c p) (oddTrace (finiteGate n p c.gate))) ∧
  (∀ p : Fin (2^n), Allowed n c.gate p →
    ∀ t : Fin (2*n),
      cell (triangle n c p) c.edge t = cell (triangle n c c.reference) c.edge t ∧
      cell (triangle n c p) (c.edge+1) t = cell (triangle n c c.reference) (c.edge+1) t)

instance leafValidDecidable (n : Nat) (c : Leaf) : Decidable (LeafValid n c) := by
  unfold LeafValid
  infer_instance

theorem leaf_sound (n : Nat) (c : Leaf) (hc : LeafValid n c)
    (G : Nat → Bool) (p q : Fin (2^n)) (pref : Prefix G c.length c.gate)
    (hp : GateLegal (prependN n p G)) (hq : GateLegal (prependN n q G)) :
    ∀ k, c.edge ≤ k →
      lam (oddTrace (prependN n p G)) k = lam (oddTrace (prependN n q G)) k := by
  obtain ⟨hm,he,hvalid,hpair⟩ := hc
  have ap := allowed_of_prefix n c.length c.gate p G hm pref hp
  have aq := allowed_of_prefix n c.length c.gate q G hm pref hq
  have sound : ∀ u : Fin (2^n), Allowed n c.gate u → ∀ k t,
      k+t < 2*(n+c.length)+1 →
      cell (triangle n c u) k t = recon (oddTrace (prependN n u G)) k t := by
    intro u hu k t hkt
    have one := triangle_sound (triangle n c u) _ (packed_sound _ _ (hvalid u hu)) k t hkt
    have two : recon (oddTrace (prependN n u G)) k t =
        recon (oddTrace (finiteGate n u c.gate)) k t := by
      apply recon_local
      intro j hj
      exact trace_prefix n c.length c.gate u G pref (t+j) (by omega)
    exact one.trans two.symm
  have eq0 : ∀ t, t < 2*n →
      recon (oddTrace (prependN n p G)) c.edge t =
      recon (oddTrace (prependN n q G)) c.edge t := by
    intro t ht
    exact (sound p ap c.edge t (by omega)).symm.trans
      (((hpair p ap ⟨t,ht⟩).1.trans (hpair q aq ⟨t,ht⟩).1.symm).trans
        (sound q aq c.edge t (by omega)))
  have eq1 : ∀ t, t < 2*n →
      recon (oddTrace (prependN n p G)) (c.edge+1) t =
      recon (oddTrace (prependN n q G)) (c.edge+1) t := by
    intro t ht
    exact (sound p ap (c.edge+1) t (by omega)).symm.trans
      (((hpair p ap ⟨t,ht⟩).2.trans (hpair q aq ⟨t,ht⟩).2.symm).trans
        (sound q aq (c.edge+1) t (by omega)))
  intro k hk
  exact tail_of_strip_pair _ _ (2*n) c.edge (shared_trace_future n p q G) eq0 eq1 k hk 0

def ExtendValid (m f : Nat) (b : Bool) (next : Nat) : Prop :=
  ∀ i : Fin (m+1), Nat.testBit next i = if i.val < m then Nat.testBit f i else b

instance extendDecidable (m f : Nat) (b : Bool) (next : Nat) : Decidable (ExtendValid m f b next) := by
  unfold ExtendValid
  infer_instance

theorem prefix_extend (G : Nat → Bool) (m f next : Nat) (b : Bool)
    (h : Prefix G m f) (hb : G m = b) (ext : ExtendValid m f b next) :
    Prefix G (m+1) next := by
  intro i hi
  rw [ext ⟨i,hi⟩]
  by_cases hm : i < m
  · rw [ite_eq_left hm]
    exact h i hm
  · rw [ite_eq_right hm]
    have eq : i=m := by omega
    rw [eq]
    exact hb

inductive CoverTree where
  | leaf (c : Leaf)
  | branch (lo hi : CoverTree)
  | reject

def bound : CoverTree → Nat
  | .leaf c => c.edge
  | .branch lo hi => max (bound lo) (bound hi)
  | .reject => 0

def checkTree (n m f : Nat) : CoverTree → Bool
  | .leaf c => decide (c.length=m ∧ c.gate=f ∧ LeafValid n c)
  | .reject => decide (8≤m ∧ window (Nat.testBit f) (m-8) ∉ words)
  | .branch lo hi =>
      (decide (ExtendValid m f false f) && decide (ExtendValid m f true (f+2^m))) &&
      (checkTree n (m+1) f lo && checkTree n (m+1) (f+2^m) hi)

theorem cover_sound (n : Nat) (tree : CoverTree) (G : Nat → Bool)
    (p q : Fin (2^n)) (hg : GateLegal G)
    (hp : GateLegal (prependN n p G)) (hq : GateLegal (prependN n q G)) :
    ∀ m f, checkTree n m f tree = true → Prefix G m f → ∀ k, bound tree ≤ k →
      lam (oddTrace (prependN n p G)) k = lam (oddTrace (prependN n q G)) k := by
  induction tree with
  | leaf c =>
      intro m f hc pref k hk
      have data : c.length=m ∧ c.gate=f ∧ LeafValid n c := of_decide_eq_true hc
      apply leaf_sound n c data.2.2 G p q _ hp hq k hk
      simpa only [data.1,data.2.1] using pref
  | reject =>
      intro m f hc pref k hk
      have data : 8≤m ∧ window (Nat.testBit f) (m-8) ∉ words := of_decide_eq_true hc
      have eq : window G (m-8) = window (Nat.testBit f) (m-8) := by
        apply window_congr
        intro j hj
        exact pref (m-8+j) (by omega)
      have mem := hg (m-8)
      rw [eq] at mem
      exact False.elim (data.2 mem)
  | branch lo hi ihlo ihhi =>
      intro m f hc pref k hk
      have data : (ExtendValid m f false f ∧ ExtendValid m f true (f+2^m)) ∧
          (checkTree n (m+1) f lo = true ∧ checkTree n (m+1) (f+2^m) hi = true) := by
        simpa only [checkTree,Bool.and_eq_true,decide_eq_true_eq] using hc
      cases hb : G m with
      | false =>
          exact ihlo (m+1) f data.2.1 (prefix_extend G m f f false pref hb data.1.1)
            k (by change max (bound lo) (bound hi) ≤ k at hk; omega)
      | true =>
          exact ihhi (m+1) (f+2^m) data.2.2
            (prefix_extend G m f (f+2^m) true pref hb data.1.2)
            k (by change max (bound lo) (bound hi) ≤ k at hk; omega)

private theorem eight_bit_decode : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    let w := bitNat b0+2*bitNat b1+4*bitNat b2+8*bitNat b3+
      16*bitNat b4+32*bitNat b5+64*bitNat b6+128*bitNat b7
    Nat.testBit w 0=b0 ∧ Nat.testBit w 1=b1 ∧ Nat.testBit w 2=b2 ∧
    Nat.testBit w 3=b3 ∧ Nat.testBit w 4=b4 ∧ Nat.testBit w 5=b5 ∧
    Nat.testBit w 6=b6 ∧ Nat.testBit w 7=b7 := by decide +kernel

theorem window_bits (G : Nat → Bool) (r : Nat) (i : Fin 8) :
    Nat.testBit (window G r) i = G (r+i.val) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := eight_bit_decode
    (G r) (G (r+1)) (G (r+2)) (G (r+3)) (G (r+4)) (G (r+5)) (G (r+6)) (G (r+7))
  rcases i with ⟨i,hi⟩
  have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [window,Nat.add_zero] using h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

theorem root_cover (n B : Nat) (trees : Nat → CoverTree)
    (valid : ∀ w ∈ words, checkTree n 8 w (trees w) = true)
    (bounds : ∀ w ∈ words, bound (trees w) ≤ B)
    (G : Nat → Bool) (p q : Fin (2^n))
    (hg : GateLegal G) (hp : GateLegal (prependN n p G)) (hq : GateLegal (prependN n q G)) :
    ∀ k, B ≤ k → lam (oddTrace (prependN n p G)) k = lam (oddTrace (prependN n q G)) k := by
  let w := window G 0
  have hw : w ∈ words := hg 0
  have pref : Prefix G 8 w := by
    intro i hi
    simpa only [w,Nat.zero_add] using (window_bits G 0 ⟨i,hi⟩).symm
  intro k hk
  exact cover_sound n (trees w) G p q hg hp hq 8 w
    (valid w hw) pref k (by have := bounds w hw; omega)

def leaf0 : Leaf := ⟨8,8,1,4,[[], [], [], [], [0, 16760815, 24600, 4182003, 2050, 1035250, 11787, 260350, 640, 64446, 1633, 15567, 136, 3211, 718, 936, 58, 167, 108, 25, 17, 1, 1, 1, 1], [], [], [], [], [], [], [], [], [], [], []]⟩

def leaf1 : Leaf := ⟨8,9,1,0,[[0, 16760575, 24960, 4181823, 2080, 1035055, 11960, 260323, 650, 64430, 1657, 15555, 154, 3222, 725, 957, 35, 174, 120, 2, 27, 6, 4, 0, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]⟩

def leaf2 : Leaf := ⟨8,16,3,8,[[], [], [], [], [], [], [], [], [0, 16711615, 98400, 4145103, 8200, 995275, 47150, 254968, 2562, 61179, 6534, 13116, 544, 556, 826, 675, 234, 158, 49, 39, 4, 5, 7, 0, 1], [0, 16711614, 98401, 4145103, 8200, 995275, 47150, 254968, 2562, 61179, 6534, 13116, 544, 556, 826, 675, 234, 158, 49, 39, 4, 5, 7, 0, 1], [], [], [], [], [], []]⟩

def leaf3 : Leaf := ⟨8,18,1,1,[[], [0, 16710654, 99841, 4144383, 8320, 994495, 47840, 254863, 2600, 61115, 6630, 13068, 616, 600, 852, 758, 141, 185, 97, 9, 13, 11, 2, 2, 1], [], [], [], [], [], [], [], [], [], [], [], [], [], []]⟩

def leaf4 : Leaf := ⟨8,33,7,0,[[0, 16514815, 393600, 3997503, 32800, 835375, 188600, 233443, 10250, 48110, 26137, 3315, 2178, 2226, 1259, 654, 424, 122, 71, 28, 17, 5, 7, 0, 1], [], [0, 16514811, 393606, 3997500, 32800, 835372, 188602, 233443, 10250, 48110, 26137, 3315, 2178, 2226, 1259, 654, 424, 122, 71, 28, 17, 5, 7, 0, 1], [], [], [], [], [], [], [], [], [], [], [], [], []]⟩

def leaf5 : Leaf := ⟨8,36,1,2,[[], [], [0, 16510971, 399366, 3994620, 33280, 832252, 191362, 233023, 10400, 47855, 26520, 3123, 2466, 2402, 1363, 986, 54, 229, 5, 39, 20, 13, 3, 2, 0], [], [], [], [], [], [], [], [], [], [], [], [], []]⟩

def leaf6 : Leaf := ⟨8,72,1,4,[[], [], [], [], [0, 15712239, 1597464, 3395571, 133122, 183282, 241163, 145662, 41600, 60350, 7777, 12495, 1672, 1419, 1358, 872, 218, 151, 20, 29, 19, 6, 4, 0, 0], [], [], [], [], [], [], [], [], [], [], []]⟩

def leaf7 : Leaf := ⟨8,144,3,8,[[], [], [], [], [], [], [], [], [0, 12517311, 6389856, 999375, 532488, 733131, 440366, 58360, 35330, 44795, 31110, 828, 6688, 1580, 1338, 419, 362, 94, 81, 55, 12, 9, 1, 1, 1], [0, 12517310, 6389857, 999375, 532488, 733131, 440366, 58360, 35330, 44795, 31110, 828, 6688, 1580, 1338, 419, 362, 94, 81, 55, 12, 9, 1, 1, 1], [], [], [], [], [], []]⟩

def leaf8 : Leaf := ⟨10,66,20,1,[[], [0, 267385854, 1574401, 66321663, 131200, 15924415, 754400, 4079503, 41000, 978875, 104550, 209868, 8712, 8904, 13228, 10810, 3747, 2538, 798, 625, 71, 84, 125, 3, 30, 0, 6, 1, 1], [], [], [0, 267385839, 1574424, 66321651, 131202, 15924402, 754411, 4079502, 41000, 978874, 104551, 209868, 8713, 8905, 13229, 10811, 3746, 2538, 799, 624, 71, 84, 125, 3, 30, 0, 6, 1, 1], [], [], [], [], [], [], [], [], [], [], []]⟩

def leaf9 : Leaf := ⟨10,578,20,1,[[], [0, 200276990, 102237697, 15990015, 8519808, 11730111, 7045856, 933775, 565288, 716731, 497766, 13260, 107016, 25288, 21420, 6714, 5795, 1514, 1310, 881, 199, 148, 29, 19, 22, 12, 0, 0, 0], [], [], [0, 200276975, 102237720, 15990003, 8519810, 11730098, 7045867, 933774, 565288, 716730, 497767, 13260, 107017, 25289, 21421, 6715, 5794, 1514, 1311, 880, 199, 148, 29, 19, 22, 12, 0, 0, 0], [], [], [], [], [], [], [], [], [], [], []]⟩

def leaf10 : Leaf := ⟨17,33924,34,2,[[], [], [0, 4122895970299, 412725811206, 893148722172, 34393817600, 51318092540, 60325497730, 38624886335, 10748068000, 16088022767, 1637769624, 3476082483, 136742946, 187009826, 246763187, 149907690, 42523278, 61577129, 8262779, 12623302, 2020124, 1160784, 1518708, 796750, 79961, 107635, 93762, 22866, 21499, 12806, 2812, 3968, 60, 930, 111, 216, 19, 18, 26, 7, 4, 1, 1], [], [], [], [], [], [0, 4122895970239, 412725811296, 893148722127, 34393817608, 51318092491, 60325497774, 38624886328, 10748068002, 16088022763, 1637769630, 3476082480, 136742950, 187009829, 246763189, 149907695, 42523272, 61577131, 8262782, 12623296, 2020126, 1160785, 1518711, 796748, 79961, 107633, 93761, 22865, 21497, 12805, 2815, 3968, 63, 928, 111, 216, 19, 18, 26, 7, 4, 1, 1], [], [], [], [], [], [], []]⟩

def leaf11 : Leaf := ⟨19,135300,38,2,[[], [], [0, 65966398500859, 6603518515206, 14290426786812, 550293209600, 821140648700, 965162699650, 618005069375, 171966628000, 257412546287, 26198040984, 55620456243, 2183170082, 2989263650, 3946499763, 2393090282, 686439054, 983476137, 129100923, 208083398, 29651228, 17121616, 21484020, 14956814, 1435001, 4132803, 26650, 1006550, 54837, 242925, 11403, 43690, 31742, 1537, 7423, 128, 1215, 736, 399, 40, 59, 38, 12, 8, 0, 0, 0], [], [], [], [], [], [0, 65966398500799, 6603518515296, 14290426786767, 550293209608, 821140648651, 965162699694, 618005069368, 171966628002, 257412546283, 26198040990, 55620456240, 2183170086, 2989263653, 3946499765, 2393090287, 686439048, 983476139, 129100926, 208083392, 29651230, 17121617, 21484023, 14956812, 1435001, 4132801, 26649, 1006549, 54839, 242924, 11401, 43689, 31741, 1539, 7422, 128, 1214, 737, 399, 40, 59, 38, 12, 8, 0, 0, 0], [], [], [], [], [], [], []]⟩

def leaf12 : Leaf := ⟨19,36996,38,2,[[], [], [0, 70089567105019, 418765608966, 17382803239932, 34897134080, 4171215139580, 200658520962, 1068976635455, 10905354400, 256338804463, 27808653720, 54815149875, 2585823266, 2519501602, 3577401011, 3181619434, 594164366, 777955241, 408022139, 41359814, 55341340, 47792464, 11653620, 10565902, 6382969, 1167299, 1640474, 347094, 519733, 6381, 127627, 938, 29310, 2753, 8095, 16, 1943, 92, 497, 5, 119, 12, 25, 1, 1, 1, 1], [], [], [], [], [], [0, 70089567104959, 418765609056, 17382803239887, 34897134088, 4171215139531, 200658521006, 1068976635448, 10905354402, 256338804459, 27808653726, 54815149872, 2585823270, 2519501605, 3577401013, 3181619439, 594164360, 777955243, 408022142, 41359808, 55341342, 47792465, 11653623, 10565900, 6382969, 1167297, 1640473, 347093, 519735, 6380, 127625, 937, 29309, 2755, 8094, 16, 1942, 93, 497, 5, 119, 12, 25, 1, 1, 1, 1], [], [], [], [], [], [], []]⟩

def treeFor : Nat → CoverTree

  | 8 => (.leaf leaf0)

  | 9 => (.leaf leaf1)

  | 16 => (.leaf leaf2)

  | 18 => (.leaf leaf3)

  | 33 => (.leaf leaf4)

  | 36 => (.leaf leaf5)

  | 66 => (.branch (.branch (.leaf leaf8) (.leaf leaf9)) .reject)

  | 72 => (.leaf leaf6)

  | 132 => (.branch (.branch (.branch (.branch (.branch .reject (.branch (.branch (.branch (.branch (.branch .reject (.branch (.leaf leaf11) .reject)) .reject) (.branch (.branch (.branch (.leaf leaf12) .reject) .reject) .reject)) .reject) .reject)) .reject) (.branch (.branch (.branch (.branch (.branch .reject (.branch (.leaf leaf10) .reject)) .reject) .reject) .reject) .reject)) .reject) .reject)

  | 144 => (.leaf leaf7)

  | _ => .reject

theorem four_bit_cover_valid : ∀ w ∈ words, checkTree 4 8 w (treeFor w) = true := by
  decide +kernel
theorem four_bit_cover_bound : ∀ w ∈ words, bound (treeFor w) ≤ 38 := by decide +kernel

/-- All legal four-bit pasts of an arbitrary legal infinite gate future agree
from column38. No periodicity or finite support is assumed. -/
theorem four_legal_pasts_agree (G : Nat → Bool) (p q : Fin 16)
    (hg : GateLegal G) (hp : GateLegal (prependN 4 p G)) (hq : GateLegal (prependN 4 q G)) :
    ∀ k, 38 ≤ k → lam (oddTrace (prependN 4 p G)) k = lam (oddTrace (prependN 4 q G)) k := by
  exact root_cover 4 38 treeFor four_bit_cover_valid four_bit_cover_bound G p q hg hp hq

end Ruliology.CellularAutomata.Rule30GatePastCover
