module
public import Ruliology.CellularAutomata.Rule30ProfileGraphCases

/-! A ranked finite-clock obstruction. A profile above period two cannot be
continued indefinitely within the checked period32 graph. This is uniform in
spatial depth and does not assume finite left support. Larger clocks stay open. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ProfileClockEscape
open Rule30RightProfiles Rule30RightPrefixClock Rule30RightPrefixBound Rule30ProfileGraph
set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

def Bad (G : Graph) (i : Nat) : Prop := ¬WordPer G.q (G.b i) 2
instance (G : Graph) (i : Nat) : Decidable (Bad G i) := by unfold Bad;infer_instance

def RankOK (G : Graph) (rank : Nat → Nat) (H i : Nat) : Prop :=
  rank i≤H ∧ (Bad G i → xr (forcing G i) G.q=false →
    ∀c:Bool,Bad G (G.next i c) ∧ rank (G.next i c)<rank i)
instance (G : Graph) (rank : Nat → Nat) (H i : Nat) : Decidable (RankOK G rank H i) := by
  unfold RankOK
  infer_instance

def checkRankRange (G : Graph) (rank : Nat → Nat) (H start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => checkRankRange G rank H start n && decide (RankOK G rank H (start+n))

theorem checkRankRange_sound (G : Graph) (rank : Nat → Nat) (H start : Nat) :
    ∀n,checkRankRange G rank H start n=true →
      ∀i,start≤i → i<start+n → RankOK G rank H i := by
  intro n
  induction n with
  | zero => intro _ i hi htop;omega
  | succ n ih =>
    intro h i hi htop
    have pair := Bool.and_eq_true_iff.mp h
    by_cases old : i<start+n
    · exact ih pair.1 i hi old
    · have eqi : i=start+n := by omega
      subst i
      exact of_decide_eq_true pair.2

theorem next_chosen (G : Graph) (hq : 0<G.q)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (i : Nat) (hi : i<G.bound) (a b c : Nat → Bool)
    (ha : ∀t,a t=profile G.q (G.a i) t)
    (hb : ∀t,b t=profile G.q (G.b i) t)
    (hc : Period c G.q)
    (step : ∀t,c (t+1)=xor (c t) (a t || b t)) :
    xr (forcing G i) G.q=false ∧
    G.next i (c 0)<G.bound ∧
    (∀t,b t=profile G.q (G.a (G.next i (c 0))) t) ∧
    ∀t,c t=profile G.q (G.b (G.next i (c 0))) t := by
  have equation : ∀t,c (t+1)=xor (c t) (forcing G i t) := by
    intro t
    rw [step,ha,hb]
    rfl
  have fp : ∀t,forcing G i (t+G.q)=forcing G i t := by
    intro t
    simp only [forcing,profile_period G.q (G.a i) t,profile_period G.q (G.b i) t]
  have parity : xr (forcing G i) G.q=false := by
    cases eq : xr (forcing G i) G.q
    · rfl
    · have shift := running_shift equation fp 0
      have ret := hc 0
      rw [Nat.zero_add] at ret shift
      rw [ret,eq] at shift
      cases h : c 0 <;> simp only [h] at shift <;> contradiction
  have good := (valid i hi).1
  rcases good with bad | good
  · rw [parity] at bad
    exact False.elim (Bool.noConfusion bad)
  · have node := good (c 0)
    refine ⟨parity,node.1,?_,?_⟩
    · intro t
      rw [hb,node.2.1]
    · intro t
      induction t with
      | zero => exact node.2.2.1.symm
      | succ t ih =>
        rw [step,wordStep_sound G.q (G.a i) (G.b i) (G.b (G.next i (c 0))) hq node.2.2.2 t,ih,ha,hb]

/-- Every available successor consumes one unit of the finite graph rank. -/
theorem extension_rank_bound (G : Graph) (hq : 0<G.q)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (rank : Nat → Nat) (H : Nat)
    (rankValid : ∀i,i<G.bound → RankOK G rank H i)
    (P : Nat → Nat → Bool)
    (step : ∀j t,P (j+2) (t+1)=xor (P (j+2) t) (P (j+1) t || P j t))
    (k n i : Nat) (hi : i<G.bound)
    (ha : ∀t,P n t=profile G.q (G.a i) t)
    (hb : ∀t,P (n+1) t=profile G.q (G.b i) t)
    (bad : Bad G i)
    (per : ∀j,j≤n+k+1 → Period (P j) G.q) : k≤rank i := by
  induction k generalizing n i with
  | zero => omega
  | succ k ih =>
    have nxt := next_chosen G hq valid i hi (P n) (P (n+1)) (P (n+2)) ha hb
      (per (n+2) (by omega)) (by intro t;simpa only [Bool.or_comm] using step n t)
    have lower := (rankValid i hi).2 bad nxt.1 (P (n+2) 0)
    have rest := ih (n+1) (G.next i (P (n+2) 0)) nxt.2.1 nxt.2.2.1
      (by simpa only [show n+1+1=n+2 by omega] using nxt.2.2.2) lower.1
      (fun j hj => per j (by omega))
    omega

/-- A non-period-two actual diagonal cannot have H+1 further diagonals all
remaining within a graph whose bad-node ranks are bounded by H. -/
theorem actual_escape (G : Graph) (hq : 0<G.q) (hbound : 0<G.bound)
    (rootA : G.a 0=0) (rootB : G.b 0=0)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (rank : Nat → Nat) (H : Nat)
    (rankValid : ∀i,i<G.bound → RankOK G rank H i)
    (x : Int → Bool) (R : Int) (hx : ∀p,R<p → x p=false) (n : Nat)
    (bad : ¬Period (rightDiag x (-R+(n:Int))) 2) :
    ¬PrefixPer (rightDiag x) (-R+((n+H+1:Nat):Int)) G.q := by
  intro hpref
  let P : Nat → Nat → Bool := fun j => rightDiag x (-R-2+(j:Int))
  have zero0 : ∀t,P 0 t=false := by intro t;exact right_white x R hx t _ (by omega)
  have zero1 : ∀t,P 1 t=false := by intro t;exact right_white x R hx t _ (by omega)
  have step : ∀j t,P (j+2) (t+1)=xor (P (j+2) t) (P (j+1) t || P j t) := by
    intro j t
    have h := rightDiag_step x (-R-2+((j+2:Nat):Int)) t
    simpa only [P,show -R-2+((j+2:Nat):Int)-1= -R-2+((j+1:Nat):Int) by omega,
      show -R-2+((j+2:Nat):Int)-2= -R-2+(j:Int) by omega] using h
  have per : ∀j,j≤n+1+(H+1)+1 → Period (P j) G.q := by
    intro j hj
    exact hpref _ (by omega)
  obtain ⟨i,hi,ha,hb⟩ := reachable_pair G hq hbound rootA rootB valid P zero0 zero1 step (n+1)
    (fun j hj => per j (by omega))
  have index : -R-2+((n+1+1:Nat):Int)= -R+(n:Int) := by omega
  have badI : Bad G i := by
    intro wp
    have p := (wordPer_iff G.q (G.b i) 2 hq).1 wp
    have pP : Period (P (n+1+1)) 2 := by intro t;rw [hb,hb];exact p t
    exact bad (by simpa only [P,index] using pP)
  have bound := extension_rank_bound G hq valid rank H rankValid P step (H+1) (n+1) i hi ha hb badI per
  have cap := (rankValid i hi).1
  omega

-- The concrete rank certificate and actual-clock consequences follow below.

def packedRank : Nat := 0x100110111000011100011010111001100010111001100011100100011011100011100010100110111001100010011100100110011101000111100101000111100101100101100011000110011101000110011100111001000110011101100102012000000000000022112020000001202000000022100000000000021200000000221000000212000000021200000001202210200000000000021200000002012000000022100000021021220000000021200000012200000002012000000212000000000000020120000002102212000000021020000000212000000000000122020120000000000001202000000202120120000001220000000000000210230301011110130303030101103301101300311101110300311013030011130301011033010113030303010110111033001110330101130301101033003300111030311103030011103301101030311011011030311100303030311010303110130300111110130030303101111103003111003300330110103030111110130300404200220020440044002200404020204400202202004402020044020200404020204042002400440400202200204400220044020204004020240040440020240400220040402200404020204402020200240040202400404400202404020200440020220200440400402022002404020200440404020024040020202020440050530030303500505500303505030035050033030300550303050503003055030300550300305505005030330030550030305500330500530035005050530030550300305050303050503300550303030030505300350505050300350503003055003033030050505500303030350503030505050050303500530303003055000664400440066000066440000660044660000444400660044000066004400660044006644000066006600444400006644006600440000660044006600664400660044006600440000660044006600444400660000440066006600446600440066000044440000666600004444000066004466006600004466000044004466001751517117511715711551715117151715175117171551175171511715171751715171511715171551711517171571517115511771155117157171157115157100000000866886860000000086686868000000006868866868686886000000008686868600000000686886860000000086688668000000006886866800000000111199991111999911119999999911119999111199991111999911119999111122aa22aa22aaaa22aa22aa22aa22aa223b3b3bb3b3b3b3b3ccccccccdddd00000000
def nodeRank (i : Nat) : Nat := (packedRank >>> (4*i)) &&& 15
private theorem rank_chunk_0 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 0 32=true := by decide +kernel

private theorem rank_chunk_32 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 32 32=true := by decide +kernel

private theorem rank_chunk_64 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 64 32=true := by decide +kernel

private theorem rank_chunk_96 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 96 32=true := by decide +kernel

private theorem rank_chunk_128 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 128 32=true := by decide +kernel

private theorem rank_chunk_160 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 160 32=true := by decide +kernel

private theorem rank_chunk_192 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 192 32=true := by decide +kernel

private theorem rank_chunk_224 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 224 32=true := by decide +kernel

private theorem rank_chunk_256 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 256 32=true := by decide +kernel

private theorem rank_chunk_288 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 288 32=true := by decide +kernel

private theorem rank_chunk_320 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 320 32=true := by decide +kernel

private theorem rank_chunk_352 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 352 32=true := by decide +kernel

private theorem rank_chunk_384 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 384 32=true := by decide +kernel

private theorem rank_chunk_416 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 416 32=true := by decide +kernel

private theorem rank_chunk_448 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 448 32=true := by decide +kernel

private theorem rank_chunk_480 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 480 32=true := by decide +kernel

private theorem rank_chunk_512 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 512 32=true := by decide +kernel

private theorem rank_chunk_544 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 544 32=true := by decide +kernel

private theorem rank_chunk_576 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 576 32=true := by decide +kernel

private theorem rank_chunk_608 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 608 32=true := by decide +kernel

private theorem rank_chunk_640 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 640 32=true := by decide +kernel

private theorem rank_chunk_672 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 672 32=true := by decide +kernel

private theorem rank_chunk_704 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 704 32=true := by decide +kernel

private theorem rank_chunk_736 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 736 32=true := by decide +kernel

private theorem rank_chunk_768 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 768 32=true := by decide +kernel

private theorem rank_chunk_800 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 800 32=true := by decide +kernel

private theorem rank_chunk_832 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 832 32=true := by decide +kernel

private theorem rank_chunk_864 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 864 32=true := by decide +kernel

private theorem rank_chunk_896 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 896 32=true := by decide +kernel

private theorem rank_chunk_928 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 928 32=true := by decide +kernel

private theorem rank_chunk_960 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 960 32=true := by decide +kernel

private theorem rank_chunk_992 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 992 32=true := by decide +kernel

private theorem rank_chunk_1024 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1024 32=true := by decide +kernel

private theorem rank_chunk_1056 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1056 32=true := by decide +kernel

private theorem rank_chunk_1088 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1088 32=true := by decide +kernel

private theorem rank_chunk_1120 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1120 32=true := by decide +kernel

private theorem rank_chunk_1152 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1152 32=true := by decide +kernel

private theorem rank_chunk_1184 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1184 32=true := by decide +kernel

private theorem rank_chunk_1216 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1216 32=true := by decide +kernel

private theorem rank_chunk_1248 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1248 32=true := by decide +kernel

private theorem rank_chunk_1280 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1280 32=true := by decide +kernel

private theorem rank_chunk_1312 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1312 32=true := by decide +kernel

private theorem rank_chunk_1344 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1344 32=true := by decide +kernel

private theorem rank_chunk_1376 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1376 32=true := by decide +kernel

private theorem rank_chunk_1408 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1408 32=true := by decide +kernel

private theorem rank_chunk_1440 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1440 32=true := by decide +kernel

private theorem rank_chunk_1472 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1472 32=true := by decide +kernel

private theorem rank_chunk_1504 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1504 32=true := by decide +kernel

private theorem rank_chunk_1536 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1536 32=true := by decide +kernel

private theorem rank_chunk_1568 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1568 32=true := by decide +kernel

private theorem rank_chunk_1600 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1600 32=true := by decide +kernel

private theorem rank_chunk_1632 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1632 32=true := by decide +kernel

private theorem rank_chunk_1664 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1664 32=true := by decide +kernel

private theorem rank_chunk_1696 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1696 32=true := by decide +kernel

private theorem rank_chunk_1728 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1728 32=true := by decide +kernel

private theorem rank_chunk_1760 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1760 32=true := by decide +kernel

private theorem rank_chunk_1792 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1792 32=true := by decide +kernel

private theorem rank_chunk_1824 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1824 32=true := by decide +kernel

private theorem rank_chunk_1856 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1856 32=true := by decide +kernel

private theorem rank_chunk_1888 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1888 32=true := by decide +kernel

private theorem rank_chunk_1920 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1920 32=true := by decide +kernel

private theorem rank_chunk_1952 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1952 32=true := by decide +kernel

private theorem rank_chunk_1984 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 1984 32=true := by decide +kernel

private theorem rank_chunk_2016 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 2016 32=true := by decide +kernel

private theorem rank_chunk_2048 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 2048 32=true := by decide +kernel

private theorem rank_chunk_2080 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 2080 32=true := by decide +kernel

private theorem rank_chunk_2112 : checkRankRange Rule30ProfileGraphCases.graph nodeRank 13 2112 4=true := by decide +kernel

private theorem rank_range_0_32 (i : Nat) (hi : 0≤i) (htop : i<32) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 0 32 rank_chunk_0 i hi htop

private theorem rank_range_32_32 (i : Nat) (hi : 32≤i) (htop : i<64) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 32 32 rank_chunk_32 i hi htop

private theorem rank_range_0_64 (i : Nat) (hi : 0≤i) (htop : i<64) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<32
  · exact rank_range_0_32 i hi h
  · exact rank_range_32_32 i (by omega) htop

private theorem rank_range_64_32 (i : Nat) (hi : 64≤i) (htop : i<96) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 64 32 rank_chunk_64 i hi htop

private theorem rank_range_96_32 (i : Nat) (hi : 96≤i) (htop : i<128) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 96 32 rank_chunk_96 i hi htop

private theorem rank_range_64_64 (i : Nat) (hi : 64≤i) (htop : i<128) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<96
  · exact rank_range_64_32 i hi h
  · exact rank_range_96_32 i (by omega) htop

private theorem rank_range_0_128 (i : Nat) (hi : 0≤i) (htop : i<128) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<64
  · exact rank_range_0_64 i hi h
  · exact rank_range_64_64 i (by omega) htop

private theorem rank_range_128_32 (i : Nat) (hi : 128≤i) (htop : i<160) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 128 32 rank_chunk_128 i hi htop

private theorem rank_range_160_32 (i : Nat) (hi : 160≤i) (htop : i<192) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 160 32 rank_chunk_160 i hi htop

private theorem rank_range_128_64 (i : Nat) (hi : 128≤i) (htop : i<192) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<160
  · exact rank_range_128_32 i hi h
  · exact rank_range_160_32 i (by omega) htop

private theorem rank_range_192_32 (i : Nat) (hi : 192≤i) (htop : i<224) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 192 32 rank_chunk_192 i hi htop

private theorem rank_range_224_32 (i : Nat) (hi : 224≤i) (htop : i<256) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 224 32 rank_chunk_224 i hi htop

private theorem rank_range_192_64 (i : Nat) (hi : 192≤i) (htop : i<256) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<224
  · exact rank_range_192_32 i hi h
  · exact rank_range_224_32 i (by omega) htop

private theorem rank_range_128_128 (i : Nat) (hi : 128≤i) (htop : i<256) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<192
  · exact rank_range_128_64 i hi h
  · exact rank_range_192_64 i (by omega) htop

private theorem rank_range_0_256 (i : Nat) (hi : 0≤i) (htop : i<256) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<128
  · exact rank_range_0_128 i hi h
  · exact rank_range_128_128 i (by omega) htop

private theorem rank_range_256_32 (i : Nat) (hi : 256≤i) (htop : i<288) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 256 32 rank_chunk_256 i hi htop

private theorem rank_range_288_32 (i : Nat) (hi : 288≤i) (htop : i<320) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 288 32 rank_chunk_288 i hi htop

private theorem rank_range_256_64 (i : Nat) (hi : 256≤i) (htop : i<320) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<288
  · exact rank_range_256_32 i hi h
  · exact rank_range_288_32 i (by omega) htop

private theorem rank_range_320_32 (i : Nat) (hi : 320≤i) (htop : i<352) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 320 32 rank_chunk_320 i hi htop

private theorem rank_range_352_32 (i : Nat) (hi : 352≤i) (htop : i<384) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 352 32 rank_chunk_352 i hi htop

private theorem rank_range_320_64 (i : Nat) (hi : 320≤i) (htop : i<384) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<352
  · exact rank_range_320_32 i hi h
  · exact rank_range_352_32 i (by omega) htop

private theorem rank_range_256_128 (i : Nat) (hi : 256≤i) (htop : i<384) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<320
  · exact rank_range_256_64 i hi h
  · exact rank_range_320_64 i (by omega) htop

private theorem rank_range_384_32 (i : Nat) (hi : 384≤i) (htop : i<416) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 384 32 rank_chunk_384 i hi htop

private theorem rank_range_416_32 (i : Nat) (hi : 416≤i) (htop : i<448) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 416 32 rank_chunk_416 i hi htop

private theorem rank_range_384_64 (i : Nat) (hi : 384≤i) (htop : i<448) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<416
  · exact rank_range_384_32 i hi h
  · exact rank_range_416_32 i (by omega) htop

private theorem rank_range_448_32 (i : Nat) (hi : 448≤i) (htop : i<480) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 448 32 rank_chunk_448 i hi htop

private theorem rank_range_480_32 (i : Nat) (hi : 480≤i) (htop : i<512) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 480 32 rank_chunk_480 i hi htop

private theorem rank_range_448_64 (i : Nat) (hi : 448≤i) (htop : i<512) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<480
  · exact rank_range_448_32 i hi h
  · exact rank_range_480_32 i (by omega) htop

private theorem rank_range_384_128 (i : Nat) (hi : 384≤i) (htop : i<512) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<448
  · exact rank_range_384_64 i hi h
  · exact rank_range_448_64 i (by omega) htop

private theorem rank_range_256_256 (i : Nat) (hi : 256≤i) (htop : i<512) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<384
  · exact rank_range_256_128 i hi h
  · exact rank_range_384_128 i (by omega) htop

private theorem rank_range_0_512 (i : Nat) (hi : 0≤i) (htop : i<512) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<256
  · exact rank_range_0_256 i hi h
  · exact rank_range_256_256 i (by omega) htop

private theorem rank_range_512_32 (i : Nat) (hi : 512≤i) (htop : i<544) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 512 32 rank_chunk_512 i hi htop

private theorem rank_range_544_32 (i : Nat) (hi : 544≤i) (htop : i<576) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 544 32 rank_chunk_544 i hi htop

private theorem rank_range_512_64 (i : Nat) (hi : 512≤i) (htop : i<576) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<544
  · exact rank_range_512_32 i hi h
  · exact rank_range_544_32 i (by omega) htop

private theorem rank_range_576_32 (i : Nat) (hi : 576≤i) (htop : i<608) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 576 32 rank_chunk_576 i hi htop

private theorem rank_range_608_32 (i : Nat) (hi : 608≤i) (htop : i<640) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 608 32 rank_chunk_608 i hi htop

private theorem rank_range_576_64 (i : Nat) (hi : 576≤i) (htop : i<640) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<608
  · exact rank_range_576_32 i hi h
  · exact rank_range_608_32 i (by omega) htop

private theorem rank_range_512_128 (i : Nat) (hi : 512≤i) (htop : i<640) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<576
  · exact rank_range_512_64 i hi h
  · exact rank_range_576_64 i (by omega) htop

private theorem rank_range_640_32 (i : Nat) (hi : 640≤i) (htop : i<672) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 640 32 rank_chunk_640 i hi htop

private theorem rank_range_672_32 (i : Nat) (hi : 672≤i) (htop : i<704) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 672 32 rank_chunk_672 i hi htop

private theorem rank_range_640_64 (i : Nat) (hi : 640≤i) (htop : i<704) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<672
  · exact rank_range_640_32 i hi h
  · exact rank_range_672_32 i (by omega) htop

private theorem rank_range_704_32 (i : Nat) (hi : 704≤i) (htop : i<736) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 704 32 rank_chunk_704 i hi htop

private theorem rank_range_736_32 (i : Nat) (hi : 736≤i) (htop : i<768) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 736 32 rank_chunk_736 i hi htop

private theorem rank_range_704_64 (i : Nat) (hi : 704≤i) (htop : i<768) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<736
  · exact rank_range_704_32 i hi h
  · exact rank_range_736_32 i (by omega) htop

private theorem rank_range_640_128 (i : Nat) (hi : 640≤i) (htop : i<768) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<704
  · exact rank_range_640_64 i hi h
  · exact rank_range_704_64 i (by omega) htop

private theorem rank_range_512_256 (i : Nat) (hi : 512≤i) (htop : i<768) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<640
  · exact rank_range_512_128 i hi h
  · exact rank_range_640_128 i (by omega) htop

private theorem rank_range_768_32 (i : Nat) (hi : 768≤i) (htop : i<800) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 768 32 rank_chunk_768 i hi htop

private theorem rank_range_800_32 (i : Nat) (hi : 800≤i) (htop : i<832) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 800 32 rank_chunk_800 i hi htop

private theorem rank_range_768_64 (i : Nat) (hi : 768≤i) (htop : i<832) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<800
  · exact rank_range_768_32 i hi h
  · exact rank_range_800_32 i (by omega) htop

private theorem rank_range_832_32 (i : Nat) (hi : 832≤i) (htop : i<864) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 832 32 rank_chunk_832 i hi htop

private theorem rank_range_864_32 (i : Nat) (hi : 864≤i) (htop : i<896) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 864 32 rank_chunk_864 i hi htop

private theorem rank_range_832_64 (i : Nat) (hi : 832≤i) (htop : i<896) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<864
  · exact rank_range_832_32 i hi h
  · exact rank_range_864_32 i (by omega) htop

private theorem rank_range_768_128 (i : Nat) (hi : 768≤i) (htop : i<896) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<832
  · exact rank_range_768_64 i hi h
  · exact rank_range_832_64 i (by omega) htop

private theorem rank_range_896_32 (i : Nat) (hi : 896≤i) (htop : i<928) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 896 32 rank_chunk_896 i hi htop

private theorem rank_range_928_32 (i : Nat) (hi : 928≤i) (htop : i<960) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 928 32 rank_chunk_928 i hi htop

private theorem rank_range_896_64 (i : Nat) (hi : 896≤i) (htop : i<960) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<928
  · exact rank_range_896_32 i hi h
  · exact rank_range_928_32 i (by omega) htop

private theorem rank_range_960_32 (i : Nat) (hi : 960≤i) (htop : i<992) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 960 32 rank_chunk_960 i hi htop

private theorem rank_range_992_32 (i : Nat) (hi : 992≤i) (htop : i<1024) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 992 32 rank_chunk_992 i hi htop

private theorem rank_range_1024_32 (i : Nat) (hi : 1024≤i) (htop : i<1056) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1024 32 rank_chunk_1024 i hi htop

private theorem rank_range_992_64 (i : Nat) (hi : 992≤i) (htop : i<1056) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1024
  · exact rank_range_992_32 i hi h
  · exact rank_range_1024_32 i (by omega) htop

private theorem rank_range_960_96 (i : Nat) (hi : 960≤i) (htop : i<1056) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<992
  · exact rank_range_960_32 i hi h
  · exact rank_range_992_64 i (by omega) htop

private theorem rank_range_896_160 (i : Nat) (hi : 896≤i) (htop : i<1056) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<960
  · exact rank_range_896_64 i hi h
  · exact rank_range_960_96 i (by omega) htop

private theorem rank_range_768_288 (i : Nat) (hi : 768≤i) (htop : i<1056) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<896
  · exact rank_range_768_128 i hi h
  · exact rank_range_896_160 i (by omega) htop

private theorem rank_range_512_544 (i : Nat) (hi : 512≤i) (htop : i<1056) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<768
  · exact rank_range_512_256 i hi h
  · exact rank_range_768_288 i (by omega) htop

private theorem rank_range_0_1056 (i : Nat) (hi : 0≤i) (htop : i<1056) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<512
  · exact rank_range_0_512 i hi h
  · exact rank_range_512_544 i (by omega) htop

private theorem rank_range_1056_32 (i : Nat) (hi : 1056≤i) (htop : i<1088) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1056 32 rank_chunk_1056 i hi htop

private theorem rank_range_1088_32 (i : Nat) (hi : 1088≤i) (htop : i<1120) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1088 32 rank_chunk_1088 i hi htop

private theorem rank_range_1056_64 (i : Nat) (hi : 1056≤i) (htop : i<1120) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1088
  · exact rank_range_1056_32 i hi h
  · exact rank_range_1088_32 i (by omega) htop

private theorem rank_range_1120_32 (i : Nat) (hi : 1120≤i) (htop : i<1152) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1120 32 rank_chunk_1120 i hi htop

private theorem rank_range_1152_32 (i : Nat) (hi : 1152≤i) (htop : i<1184) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1152 32 rank_chunk_1152 i hi htop

private theorem rank_range_1120_64 (i : Nat) (hi : 1120≤i) (htop : i<1184) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1152
  · exact rank_range_1120_32 i hi h
  · exact rank_range_1152_32 i (by omega) htop

private theorem rank_range_1056_128 (i : Nat) (hi : 1056≤i) (htop : i<1184) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1120
  · exact rank_range_1056_64 i hi h
  · exact rank_range_1120_64 i (by omega) htop

private theorem rank_range_1184_32 (i : Nat) (hi : 1184≤i) (htop : i<1216) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1184 32 rank_chunk_1184 i hi htop

private theorem rank_range_1216_32 (i : Nat) (hi : 1216≤i) (htop : i<1248) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1216 32 rank_chunk_1216 i hi htop

private theorem rank_range_1184_64 (i : Nat) (hi : 1184≤i) (htop : i<1248) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1216
  · exact rank_range_1184_32 i hi h
  · exact rank_range_1216_32 i (by omega) htop

private theorem rank_range_1248_32 (i : Nat) (hi : 1248≤i) (htop : i<1280) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1248 32 rank_chunk_1248 i hi htop

private theorem rank_range_1280_32 (i : Nat) (hi : 1280≤i) (htop : i<1312) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1280 32 rank_chunk_1280 i hi htop

private theorem rank_range_1248_64 (i : Nat) (hi : 1248≤i) (htop : i<1312) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1280
  · exact rank_range_1248_32 i hi h
  · exact rank_range_1280_32 i (by omega) htop

private theorem rank_range_1184_128 (i : Nat) (hi : 1184≤i) (htop : i<1312) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1248
  · exact rank_range_1184_64 i hi h
  · exact rank_range_1248_64 i (by omega) htop

private theorem rank_range_1056_256 (i : Nat) (hi : 1056≤i) (htop : i<1312) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1184
  · exact rank_range_1056_128 i hi h
  · exact rank_range_1184_128 i (by omega) htop

private theorem rank_range_1312_32 (i : Nat) (hi : 1312≤i) (htop : i<1344) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1312 32 rank_chunk_1312 i hi htop

private theorem rank_range_1344_32 (i : Nat) (hi : 1344≤i) (htop : i<1376) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1344 32 rank_chunk_1344 i hi htop

private theorem rank_range_1312_64 (i : Nat) (hi : 1312≤i) (htop : i<1376) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1344
  · exact rank_range_1312_32 i hi h
  · exact rank_range_1344_32 i (by omega) htop

private theorem rank_range_1376_32 (i : Nat) (hi : 1376≤i) (htop : i<1408) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1376 32 rank_chunk_1376 i hi htop

private theorem rank_range_1408_32 (i : Nat) (hi : 1408≤i) (htop : i<1440) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1408 32 rank_chunk_1408 i hi htop

private theorem rank_range_1376_64 (i : Nat) (hi : 1376≤i) (htop : i<1440) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1408
  · exact rank_range_1376_32 i hi h
  · exact rank_range_1408_32 i (by omega) htop

private theorem rank_range_1312_128 (i : Nat) (hi : 1312≤i) (htop : i<1440) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1376
  · exact rank_range_1312_64 i hi h
  · exact rank_range_1376_64 i (by omega) htop

private theorem rank_range_1440_32 (i : Nat) (hi : 1440≤i) (htop : i<1472) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1440 32 rank_chunk_1440 i hi htop

private theorem rank_range_1472_32 (i : Nat) (hi : 1472≤i) (htop : i<1504) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1472 32 rank_chunk_1472 i hi htop

private theorem rank_range_1440_64 (i : Nat) (hi : 1440≤i) (htop : i<1504) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1472
  · exact rank_range_1440_32 i hi h
  · exact rank_range_1472_32 i (by omega) htop

private theorem rank_range_1504_32 (i : Nat) (hi : 1504≤i) (htop : i<1536) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1504 32 rank_chunk_1504 i hi htop

private theorem rank_range_1536_32 (i : Nat) (hi : 1536≤i) (htop : i<1568) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1536 32 rank_chunk_1536 i hi htop

private theorem rank_range_1568_32 (i : Nat) (hi : 1568≤i) (htop : i<1600) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1568 32 rank_chunk_1568 i hi htop

private theorem rank_range_1536_64 (i : Nat) (hi : 1536≤i) (htop : i<1600) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1568
  · exact rank_range_1536_32 i hi h
  · exact rank_range_1568_32 i (by omega) htop

private theorem rank_range_1504_96 (i : Nat) (hi : 1504≤i) (htop : i<1600) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1536
  · exact rank_range_1504_32 i hi h
  · exact rank_range_1536_64 i (by omega) htop

private theorem rank_range_1440_160 (i : Nat) (hi : 1440≤i) (htop : i<1600) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1504
  · exact rank_range_1440_64 i hi h
  · exact rank_range_1504_96 i (by omega) htop

private theorem rank_range_1312_288 (i : Nat) (hi : 1312≤i) (htop : i<1600) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1440
  · exact rank_range_1312_128 i hi h
  · exact rank_range_1440_160 i (by omega) htop

private theorem rank_range_1056_544 (i : Nat) (hi : 1056≤i) (htop : i<1600) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1312
  · exact rank_range_1056_256 i hi h
  · exact rank_range_1312_288 i (by omega) htop

private theorem rank_range_1600_32 (i : Nat) (hi : 1600≤i) (htop : i<1632) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1600 32 rank_chunk_1600 i hi htop

private theorem rank_range_1632_32 (i : Nat) (hi : 1632≤i) (htop : i<1664) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1632 32 rank_chunk_1632 i hi htop

private theorem rank_range_1600_64 (i : Nat) (hi : 1600≤i) (htop : i<1664) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1632
  · exact rank_range_1600_32 i hi h
  · exact rank_range_1632_32 i (by omega) htop

private theorem rank_range_1664_32 (i : Nat) (hi : 1664≤i) (htop : i<1696) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1664 32 rank_chunk_1664 i hi htop

private theorem rank_range_1696_32 (i : Nat) (hi : 1696≤i) (htop : i<1728) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1696 32 rank_chunk_1696 i hi htop

private theorem rank_range_1664_64 (i : Nat) (hi : 1664≤i) (htop : i<1728) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1696
  · exact rank_range_1664_32 i hi h
  · exact rank_range_1696_32 i (by omega) htop

private theorem rank_range_1600_128 (i : Nat) (hi : 1600≤i) (htop : i<1728) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1664
  · exact rank_range_1600_64 i hi h
  · exact rank_range_1664_64 i (by omega) htop

private theorem rank_range_1728_32 (i : Nat) (hi : 1728≤i) (htop : i<1760) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1728 32 rank_chunk_1728 i hi htop

private theorem rank_range_1760_32 (i : Nat) (hi : 1760≤i) (htop : i<1792) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1760 32 rank_chunk_1760 i hi htop

private theorem rank_range_1728_64 (i : Nat) (hi : 1728≤i) (htop : i<1792) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1760
  · exact rank_range_1728_32 i hi h
  · exact rank_range_1760_32 i (by omega) htop

private theorem rank_range_1792_32 (i : Nat) (hi : 1792≤i) (htop : i<1824) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1792 32 rank_chunk_1792 i hi htop

private theorem rank_range_1824_32 (i : Nat) (hi : 1824≤i) (htop : i<1856) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1824 32 rank_chunk_1824 i hi htop

private theorem rank_range_1792_64 (i : Nat) (hi : 1792≤i) (htop : i<1856) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1824
  · exact rank_range_1792_32 i hi h
  · exact rank_range_1824_32 i (by omega) htop

private theorem rank_range_1728_128 (i : Nat) (hi : 1728≤i) (htop : i<1856) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1792
  · exact rank_range_1728_64 i hi h
  · exact rank_range_1792_64 i (by omega) htop

private theorem rank_range_1600_256 (i : Nat) (hi : 1600≤i) (htop : i<1856) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1728
  · exact rank_range_1600_128 i hi h
  · exact rank_range_1728_128 i (by omega) htop

private theorem rank_range_1856_32 (i : Nat) (hi : 1856≤i) (htop : i<1888) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1856 32 rank_chunk_1856 i hi htop

private theorem rank_range_1888_32 (i : Nat) (hi : 1888≤i) (htop : i<1920) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1888 32 rank_chunk_1888 i hi htop

private theorem rank_range_1856_64 (i : Nat) (hi : 1856≤i) (htop : i<1920) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1888
  · exact rank_range_1856_32 i hi h
  · exact rank_range_1888_32 i (by omega) htop

private theorem rank_range_1920_32 (i : Nat) (hi : 1920≤i) (htop : i<1952) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1920 32 rank_chunk_1920 i hi htop

private theorem rank_range_1952_32 (i : Nat) (hi : 1952≤i) (htop : i<1984) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1952 32 rank_chunk_1952 i hi htop

private theorem rank_range_1920_64 (i : Nat) (hi : 1920≤i) (htop : i<1984) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1952
  · exact rank_range_1920_32 i hi h
  · exact rank_range_1952_32 i (by omega) htop

private theorem rank_range_1856_128 (i : Nat) (hi : 1856≤i) (htop : i<1984) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1920
  · exact rank_range_1856_64 i hi h
  · exact rank_range_1920_64 i (by omega) htop

private theorem rank_range_1984_32 (i : Nat) (hi : 1984≤i) (htop : i<2016) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 1984 32 rank_chunk_1984 i hi htop

private theorem rank_range_2016_32 (i : Nat) (hi : 2016≤i) (htop : i<2048) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 2016 32 rank_chunk_2016 i hi htop

private theorem rank_range_1984_64 (i : Nat) (hi : 1984≤i) (htop : i<2048) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<2016
  · exact rank_range_1984_32 i hi h
  · exact rank_range_2016_32 i (by omega) htop

private theorem rank_range_2048_32 (i : Nat) (hi : 2048≤i) (htop : i<2080) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 2048 32 rank_chunk_2048 i hi htop

private theorem rank_range_2080_32 (i : Nat) (hi : 2080≤i) (htop : i<2112) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 2080 32 rank_chunk_2080 i hi htop

private theorem rank_range_2112_4 (i : Nat) (hi : 2112≤i) (htop : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  checkRankRange_sound Rule30ProfileGraphCases.graph nodeRank 13 2112 4 rank_chunk_2112 i hi htop

private theorem rank_range_2080_36 (i : Nat) (hi : 2080≤i) (htop : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<2112
  · exact rank_range_2080_32 i hi h
  · exact rank_range_2112_4 i (by omega) htop

private theorem rank_range_2048_68 (i : Nat) (hi : 2048≤i) (htop : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<2080
  · exact rank_range_2048_32 i hi h
  · exact rank_range_2080_36 i (by omega) htop

private theorem rank_range_1984_132 (i : Nat) (hi : 1984≤i) (htop : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<2048
  · exact rank_range_1984_64 i hi h
  · exact rank_range_2048_68 i (by omega) htop

private theorem rank_range_1856_260 (i : Nat) (hi : 1856≤i) (htop : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1984
  · exact rank_range_1856_128 i hi h
  · exact rank_range_1984_132 i (by omega) htop

private theorem rank_range_1600_516 (i : Nat) (hi : 1600≤i) (htop : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1856
  · exact rank_range_1600_256 i hi h
  · exact rank_range_1856_260 i (by omega) htop

private theorem rank_range_1056_1060 (i : Nat) (hi : 1056≤i) (htop : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1600
  · exact rank_range_1056_544 i hi h
  · exact rank_range_1600_516 i (by omega) htop

private theorem rank_range_0_2116 (i : Nat) (hi : 0≤i) (htop : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i := by
  by_cases h : i<1056
  · exact rank_range_0_1056 i hi h
  · exact rank_range_1056_1060 i (by omega) htop

theorem rank_valid (i : Nat) (hi : i<2116) : RankOK Rule30ProfileGraphCases.graph nodeRank 13 i :=
  rank_range_0_2116 i (Nat.zero_le _) hi

end Ruliology.CellularAutomata.Rule30ProfileClockEscape
