module

public import Ruliology.CellularAutomata.Rule30EtherThreeReach
public import Ruliology.CellularAutomata.Rule30FastImage
public import Ruliology.CellularAutomata.Rule30FiniteStrips
public import Ruliology.CellularAutomata.Rule30ResetMixtures

/-!
Exactly ten of the 512 three-gap words force AIOvernight's set G in every ordinary history.
Positive cases use open-boundary strip images. Each negative case is realized by a right row.
-/

@[expose] public section

-- Keep independent kernel checks sequential so their peak allocations do not overlap.
set_option Elab.async false


section
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
def sub (a b : Nat) := a &&& b == a
theorem sub_sound {a b x : Nat} (ok:sub a b=true) (hs:a.testBit x=true) : b.testBit x=true := by
  have eq : a &&& b=a := of_decide_eq_true (by simpa [sub] using ok)
  have bits:=congrArg (fun q : Nat=>q.testBit x) eq
  simpa [Nat.testBit_and,hs] using bits

end Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
open Ruliology.CellularAutomata Rule30StripCertificates Rule30Realization
abbrev Frow := Rule30FiniteStrips.encRow
def Drive (x : Int→Bool) (j : Int) (t : Nat) (w : List Bool) :=
  ∀k,k<w.length → evol x (t+k) j=w.getD k false

theorem drivePrefix {x j t} {u v : List Bool} (h:Drive x j t (u++v)) : Drive x j t u := by
  intro k hk
  have z:=h k (by simp;omega)
  simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left hk] using z
theorem driveSuffix {x j t} {u v : List Bool} (h:Drive x j t (u++v)) : Drive x j (t+u.length) v := by
  intro k hk
  have z:=h (u.length+k) (by simp;omega)
  simpa [List.getD_eq_getElem?_getD,List.getElem?_append_right (show u.length≤u.length+k by omega),Nat.add_assoc] using z

private theorem uniq {x j t k z} (enc:Rule30FiniteStrips.Enc x k t j z) : z=Frow x t j k := by
  have alt:=Rule30FiniteStrips.enc_encRow (x:=x) k t j
  apply Nat.eq_of_testBit_eq;intro i
  by_cases b:i<k
  · exact (enc.2 _ b).trans (alt.2 _ b).symm
  · have up:=Nat.pow_le_pow_right (by decide : 0<2) (by omega : k≤i)
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le enc.1 up)).trans (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le alt.1 up)).symm

theorem follows8 {x j t w src} (drive:Drive x j t w) (start:src.testBit (Frow x t j 8)=true) :
    (applyWord 8 w src).testBit (Frow x (t+w.length) j 8)=true := by
  obtain ⟨r,actual,mem⟩:=Rule30FiniteStrips.enc_applyWord w t _ src
    (Rule30FiniteStrips.enc_encRow (x:=x) 8 t j) start drive
  rwa [uniq actual] at mem

theorem move_set {x j t w src dst} (drive:Drive x j t w) (start:src.testBit (Frow x t j 8)=true)
    (moves:Rule30WhitePad10111.Sub (applyWord 8 w src) dst) :
    dst.testBit (Frow x (t+w.length) j 8)=true := moves _ (follows8 drive start)

theorem drive_pulse {x j s q} (h:Drive x j s (Rule30ResetMixtures.driver q)) :
    ∀k,k<q+1 → evol x (s+k) j=decide (k=0) := by
  intro k hk
  have a:=h k (by rw [Rule30ResetMixtures.driver_length];omega)
  cases k with
  | zero=>exact a
  | succ k=>
    simpa [Rule30ResetMixtures.driver,List.getD_eq_getElem?_getD,List.getElem?_replicate_of_lt (by omega : k<q)] using a
end Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
open Ruliology.CellularAutomata Rule30ResetMixtures
def Tr (x : Int→Bool) (j : Int) (a b : Nat→Prop) (w : List Bool) :=
  ∀s, a s → Drive x j s w → b (s+w.length)
def Low (x : Int→Bool) (j : Int) (u : Nat) (s : Nat) := u.testBit (Frow x s j 8)=true
end Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture
open Ruliology.CellularAutomata Rule30ResetMixtures Rule30Realization Rule30StripCertificates Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven

/-- From G, the first right cell is white exactly on the first two white ticks.
The observation at the pulse is the OR, which is black regardless of the right-cell value. -/
theorem stock_response {x j t q} (inG:Low x j G t) (read:Drive x j t (driver q)) {k : Nat} (pos:1≤k) (lim:k≤q) :
    evol x (t+k) (j+1)=decide (3≤k) := by
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hh:=drive_pulse read
  have pre:Drive x j t ((driver q).take (i+1)) := by
    intro u hu
    have short:u<i+1:=by rw [List.length_take] at hu;omega
    simpa [List.getD_eq_getElem?_getD,short] using read u (by rw [driver_length];omega)
  have mem:=follows8 pre inG
  have take_ : (driver q).take (i+1)=true::List.replicate i false := by
    simp [driver,List.take_replicate,Nat.min_eq_left (by omega:i≤q)]
  rw [List.length_take,driver_length,Nat.min_eq_left (by omega),take_,applyWord,←Rule30WhitePad10111.wp_eq] at mem
  have enc:=Rule30FiniteStrips.enc_encRow (x:=x) 8 (t+(i+1)) j
  have p:=enc.2 0 (by decide)
  change (Frow x (t+(i+1)) j 8).testBit 0=evol x (t+(i+1)) (j+1+0) at p
  rw [Int.add_zero] at p
  rw [←p]
  rcases i with _|i
  · exact Rule30WhitePad10111.const_mem white0 enc.1 mem
  rcases i with _|i
  · exact Rule30WhitePad10111.const_mem white1 enc.1 mem
  · simpa using Rule30WhitePad10111.const_mem Rule30WhitePad10111.odd_bit enc.1 (white_positive (by omega) _ mem)

theorem stock_mask {x j t q} (inG:Low x j G t) (read:Drive x j t (driver q)) {k : Nat} (lim:k≤q) :
    Rule30FiniteMaskedJen.orCol x j (t+k)=decide (k=0 ∨ 3≤k) := by
  have a:=drive_pulse read k (by omega)
  unfold Rule30FiniteMaskedJen.orCol
  rw [a];cases k with
  | zero=>rfl
  | succ k=>rw [stock_response inG read (by omega) lim];simp

/-- A common capture synchronizes every future observation even when the gaps have no period. -/
theorem forever {x : Int→Bool} (j : Int) (T q : Nat→Nat)
    (clock:∀n,T (n+1)=T n+(q n+1)) (valid:∀n,9≤q n)
    (read:∀n,Drive x j (T n) (driver (q n))) {n0 : Nat} (capture:Low x j G (T n0)) :
    ∀n,n0≤n → ∀k,k≤q n → Rule30FiniteMaskedJen.orCol x j (T n+k)=decide (k=0 ∨ 3≤k) := by
  have allG:∀n,n0≤n → Low x j G (T n) := by
    intro n hn;obtain ⟨u,rfl⟩:=Nat.exists_eq_add_of_le hn
    induction u with
    | zero=>simpa using capture
    | succ u ih=>
      have h:=stageG (valid (n0+u));rw [mac_eq] at h
      have k:=move_set (read (n0+u)) (ih (Nat.le_add_right _ _)) h
      rw [show n0+(u+1)=(n0+u)+1 by omega,clock]
      simpa only [Low,driver_length] using k
  exact fun n h k hk=>stock_mask (allG n h) (read n) hk
end Ruliology.CellularAutomata.Rule30ThreeGapCapture
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture.Pos
open Ruliology.CellularAutomata Rule30StripCertificates Rule30FastImage Rule30Realization Rule30ResetMixtures Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
theorem enc_unique {x : Int → Bool} {K t : Nat} {i : Int} {r s : Nat}
    (hr : Rule30FiniteStrips.Enc x K t i r) (hs : Rule30FiniteStrips.Enc x K t i s) : r = s := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < K
  · rw [hr.2 j hj, hs.2 j hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr.1 (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs.1 (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem encRow_step (x : Int → Bool) (K t : Nat) (i : Int) :
    Rule30FiniteStrips.encRow x (t+1) i K =
      stripStep K (evol x t i) (evol x t (i+1+K)) (Rule30FiniteStrips.encRow x t i K) :=
  enc_unique (Rule30FiniteStrips.enc_encRow K (t+1) i) (Rule30FiniteStrips.enc_step (Rule30FiniteStrips.enc_encRow K t i))

def Bit (W u : Nat) (x : Int→Bool) (j : Int) (t : Nat) := u.testBit (Frow x t j W)=true
theorem proj {W : Nat} (lim:8≤W) (x : Int→Bool) (j : Int) (t : Nat) :
    (Frow x t j W)%256=Frow x t j 8 := by
  apply Nat.eq_of_testBit_eq;intro i
  change ((Frow x t j W)%2^8).testBit i=_
  rw [Nat.testBit_mod_two_pow,Rule30FiniteStrips.testBit_encRow,Rule30FiniteStrips.testBit_encRow]
  by_cases h:i<8
  · simp [h,show i<W by omega]
  · simp [h]
def chunks (n u : Nat) := (List.range n).all (fun a=>sub ((u >>> (256*a))%2^256) G)
theorem finish {W n u} (h:chunks n u=true) (size:2^W≤256*n) (Wok:8≤W)
    {x j t} (mem:Bit W u x j t) : Low x j G t := by
  let v:=Frow x t j W
  have small:v<2^W:=(Rule30FiniteStrips.enc_encRow (x:=x) W t j).1
  have lo:v%256<256:=Nat.mod_lt _ (by decide)
  have hdiv:v/256<n:=by omega
  have chk:=List.all_eq_true.mp h _ (List.mem_range.mpr hdiv)
  have sum:256*(v/256)+v%256=v:=Nat.div_add_mod v 256
  have matchBit:((u >>> (256*(v/256)))%2^256).testBit (v%256)=true:=by
    rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,sum];simp [lo,show u.testBit v=true from mem]
  have out:=sub_sound chk matchBit
  simpa only [Low,v,proj Wok] using out

theorem all_rows {u W} (eq:u=fullSet W) (x : Int→Bool) (j : Int) (t : Nat) : Bit W u x j t := by
  unfold Bit;rw [eq,fullSet,Nat.testBit_two_pow_sub_one]
  exact decide_eq_true (Rule30FiniteStrips.enc_encRow (x:=x) W t j).1
end Ruliology.CellularAutomata.Rule30ThreeGapCapture.Pos
end

section
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture.Pos
open Ruliology.CellularAutomata Rule30FastImage Rule30StripCertificates Rule30ResetMixtures Rule30Realization Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def push (W : Nat) : List Bool → Nat → Nat
  | [], s => s
  | a :: w, s => push W w (fimage W a s)
theorem push_mem {W : Nat} {x : Int → Bool} {j : Int} (w : List Bool) (t s : Nat)
    (read : Drive x j t w) (start : Bit W s x j t) : Bit W (push W w s) x j (t+w.length) := by
  induction w generalizing t s with
  | nil => simpa [push] using start
  | cons a w ih =>
    have ha : evol x t j = a := by simpa using read 0 (by simp)
    have st := encRow_step x W t j
    rw [ha] at st
    have nx : Bit W (fimage W a s) x j (t+1) := by
      unfold Bit Frow
      rw [st]
      exact fimage_mem (Rule30FiniteStrips.enc_encRow (x:=x) W t j).1 start _
    have tail_ : Drive x j (t+1) w := by
      intro k hk
      have v:=read (k+1) (by simp;omega)
      simpa [List.getD_eq_getElem?_getD, show t+1+k=t+(k+1) by omega] using v
    simpa only [push, List.length_cons, show t+(w.length+1)=t+1+w.length by omega] using ih (t+1) _ tail_ nx

private def tile : Nat → Nat
  | 0 => G
  | k+1 => tile k ||| (tile k <<< (256 * 2^k))
private theorem fits14 : chunks 64 (tile 6) = true := by decide +kernel
private theorem fits18 : chunks 1024 (tile 10) = true := by decide +kernel
private theorem all_cold {W n k : Nat} {w : List Bool}
    (checked : sub (push W w (fullSet W)) (tile k) = true)
    (good : chunks n (tile k) = true)
    (size : 2 ^ W ≤ 256 * n) (wide : 8 ≤ W) {x j} :
    Tr x j (fun _ => True) (Low x j G) w := by
  intro t _ h
  exact finish good size wide (sub_sound checked (push_mem w t _ h (all_rows rfl x j t)))
private theorem w14_9 : sub (push 14 (blocks [9,16,16]) (fullSet 14)) (tile 6) = true := by decide +kernel
private theorem w14_10 : sub (push 14 (blocks [10,16,16]) (fullSet 14)) (tile 6) = true := by decide +kernel
private theorem w14_11 : sub (push 14 (blocks [11,16,16]) (fullSet 14)) (tile 6) = true := by decide +kernel
private theorem w14_12 : sub (push 14 (blocks [12,16,16]) (fullSet 14)) (tile 6) = true := by decide +kernel
private theorem w14_13 : sub (push 14 (blocks [13,16,16]) (fullSet 14)) (tile 6) = true := by decide +kernel
private theorem w14_14 : sub (push 14 (blocks [14,16,16]) (fullSet 14)) (tile 6) = true := by decide +kernel
private theorem w14_15 : sub (push 14 (blocks [15,16,16]) (fullSet 14)) (tile 6) = true := by decide +kernel
private theorem w14_16 : sub (push 14 (blocks [16,16,16]) (fullSet 14)) (tile 6) = true := by decide +kernel
theorem cold14 {x j q} (lim : 9 ≤ q ∧ q ≤ 16) :
    Tr x j (fun _ => True) (Low x j G) (blocks [q,16,16]) := by
  apply all_cold (W:=14) (n:=64) _ fits14 (by decide) (by decide)
  have e : q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w14_9
  · exact w14_10
  · exact w14_11
  · exact w14_12
  · exact w14_13
  · exact w14_14
  · exact w14_15
  · exact w14_16
private theorem w18_15 : sub (push 18 (blocks [16,10,15]) (fullSet 18)) (tile 10) = true := by decide +kernel
private theorem w18_16 : sub (push 18 (blocks [16,10,16]) (fullSet 18)) (tile 10) = true := by decide +kernel
theorem cold18 {x j q} (lim : q=15 ∨ q=16) :
    Tr x j (fun _ => True) (Low x j G) (blocks [16,10,q]) := by
  apply all_cold (W:=18) (n:=1024) _ fits18 (by decide) (by decide)
  rcases lim with rfl | rfl
  · exact w18_15
  · exact w18_16
end Ruliology.CellularAutomata.Rule30ThreeGapCapture.Pos
end

section
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture.Triple
open Ruliology.CellularAutomata Rule30Realization Rule30EtherThree Rule30ResetMixtures Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
def initial (z : Nat) (p : Int) := z.testBit (p-1).toNat
theorem actual (c : Nat→Bool) (z : Nat) (t i : Nat) :
    (rowN c z t).testBit i=evol (conf (initial z) c) t ((i:Int)+1) := by
  induction t generalizing i with
  | zero=>
    have eq:=(realize (initial z) c).1 ((i:Int)+1) (by omega)
    simpa [rowN,evol,initial] using eq.symm
  | succ t ih=>
    rw [rowN,testBit_stepN,evol,ih i,ih (i+1)]
    congr 1
    cases i with
    | zero=>simpa using ((realize (initial z) c).2 t).symm
    | succ i=>simp [ih]
theorem projection (c : Nat→Bool) (z t : Nat) :
    Frow (conf (initial z) c) t 0 8=(rowN c z t)%256 := by
  apply Nat.eq_of_testBit_eq;intro i
  change (Frow (conf (initial z) c) t 0 8).testBit i=((rowN c z t)%2^8).testBit i
  rw [Rule30FiniteStrips.testBit_encRow,Nat.testBit_mod_two_pow,actual]
  simp [Int.add_comm]
def word (i : Nat) := blocks [9+i/64,9+(i/8)%8,9+i%8]
def known (i : Nat) := let a:=9+i/64;let b:=9+(i/8)%8;let c:=9+i%8
  (b==16 && c==16) || (a==16 && b==10 && (c==15 || c==16))
def lastRow (i z : Nat) := let w:=word i;rowN (fun k=>w.getD k false) z w.length % 256
theorem actual_counter {i z : Nat} (bad:G.testBit (lastRow i z)=false) :
    ∃x : Int→Bool,Drive x 0 0 (word i) ∧ ¬Low x 0 G (word i).length := by
  let c:=fun k=>(word i).getD k false
  refine ⟨conf (initial z) c,?_,?_⟩
  · intro k _;simpa only [Nat.zero_add,c] using (realize (initial z) c).2 k
  · intro good;unfold Low at good;rw [projection] at good
    change G.testBit (lastRow i z)=true at good;rw [bad] at good;contradiction
end Ruliology.CellularAutomata.Rule30ThreeGapCapture.Triple

end

section
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture.Triple
open Ruliology.CellularAutomata Rule30ResetMixtures Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def seeds : Array Nat := #[3254260357708774970,4398639619760665991,7883473769444019914,15983978520671915964,11096689957490624165,3281600941104565633,4037185520931389831,1778457652838168066,14822134093201192878,9171879068141075643,11372876449257032266,13049314634786168986,9017540330582273994,15321668585070165802,8615956459349368923,7592834498421787088,11483127453601424556,7513481001918640091,8139765920186893134,11963999453855088474,17210622622871740238,12967074244978848166,14249485436729532524,17558002762788020588,7540151876802671648,6920328313830691409,16004247434391118591,7896502883041787994,1767939293842894928,522707197795406417,11997602161156529262,11688810045475758992,14945702494690933639,5264746376178594081,560483457359793358,4078625587596185343,3748496893110613211,15720682959421595276,10846936304435064379,4813586847300117895,1200050254602054042,16310466701751945236,11858635793709263339,16949929366858430471,17519653328853120435,8337944171617659738,12669604160462933978,8946389595363079024,5539128754292858190,9226151603328801339,2186199725793908887,9535175422175917055,17077516846694234220,1574018097945008364,3957099150465695566,17520144142523734362,13328387058936316083,13325005001695596267,16126963490231957408,10789551515548525831,4670718505660988347,6723958884592880800,9136258036018236679,0,1707527910420387345,13806929252961674643,14364762499252854075,15800478741625029631,4749569229988555137,6836649657814099259,14006719520487084947,15164993368695669285,7403460880430291173,15863731927014644959,14406385964371801809,7934413902926417726,15297962753656913820,3959867383727064319,9271781573087546092,17171217918187983425,556881971322861378,24516845755297311,9953756274956116609,10650164104518367471,832333456936197999,2889770953364930079,12382629524433311078,2002279460987019658,6717066867377042561,18071358243293576820,17320778304673001935,15420020047429307252,2632439613321445620,5743892481827364447,18215548926916234559,17647812123037487431,11621103668523225663,5001111334343593311,14287502170692308545,14062707178478859582,11456491646451195455,5397092356200865119,11406538633049160283,7353527918461922439,6313943540576156816,6627819578638515729,11750162940546981020,11553407243520914220,17718829735760057404,1818998608997870172,1639640240079224307,6208632570003588595,10204557653188664687,17352828805806611999,9601733324304335324,6108638039025189231,5073939862024667375,11454954051955508273,14779494581235842591,6365157169446187887,7698930952998537348,14050812012228144991,13385519783289844830,10998261197695621954,10718563817906664236,7461581725217134284,9992508030290280961,0,8479030599321893043,17353991290753379327,15009128283516137351,6068007420536712027,3664788054695634139,3393025970792627365,4123558036130213767,9696215443070325307,2392434041580394174,14973256881263852382,680823975261917841,16836757059965660033,11121639028217622935,6991398130655253854,9511802365551268368,9552290215672061313,6104636043612138960,2933282168453912016,16144459252056154097,17432751093396220078,558155236527355326,3556689761809518939,3001995407853666946,17103915519431309954,6181145441482920599,9246384531540092378,14831928406488780603,18237372484450930156,2379717885215541990,15512274926246557499,14716746730676888998,9624567342693177766,12195585393206890859,7789066691375687854,2935297067489436863,13806067045168893290,16246391921193513747,11253717483302950378,7220793852721583594,1441173808550647068,9572021355005759776,9871799342043881075,18254160805612184570,2312287950725059882,2599973885266578154,2009954469073775807,11737350165139207790,15660788875538573675,8793408383608633470,8015662771029262996,5698975404695350348,13702068558224600140,5473403437652075795,7688720708041794835,3743876912118913684,2052591935169155859,15176426716675169178,16460494076233100350,14530355572518749809,13268586912187632514,15174260624606136494,9420304400220466854,4181183944984320404,0,10390262659122589505,1043578221953573748,17686997610311436019,6197353732818285703,9774608848308820212,10198255709090861555,9876608665809309695,12758375785929625599,15217863857372265652,9588979910041754129,16272436048474721026,8682315008297989868,6207650754545951231,11857313375075645489,15729777135571862993,13457401285840891487,270959969985765573,14447764694685758693,14801549708537056391,7584301885974334702,4289096874452702343,9409206928563436275,16508246409548313838,4866447412585024972,6879509888631222991,17871862921588659603,3302632010804306419,3335089638892326017,4287857805381122564,15992172252095168044,2804225862390021723,17323157315437626789,5846462071686608613,2804147439948383099,1095509021065185182,1280872932304827950,17536132135008621073,11555480305048704641,4874924591909634099,12975095714653437907,11739784111121529662,13156684244883497098,2001188990022222163,13407145537114614410,9530952041600360257,16850255106553830124,2601510411146635557,4248413417166064851,12236711045072943348,15022464589418445044,3000104865800018196,9719559350784728588,9968127763889730932,16479416041709445068,14096835550961566668,2332207202298555916,2003381016938492460,4239977305857823039,10261582913825396929,12301886865508624284,9330600321589505580,7637451347538138244,16990330616962577125,0,11924313102278495215,4549252478997571820,3639402460102980603,2079656616594793979,10656739997401764304,6074987973159610942,17987041228939915263,6568106514011779071,17564465619945448721,10138441886481705169,1698979634475517115,9489975670050281777,15174239956776210559,2868273516175928319,12052741978495586654,10760928652359517285,4493830197881917488,613713972584632350,16574743974838513438,462590576776096175,9138366956400562207,6918664070149546607,709122812323008542,16956247851233220271,4456812982375488787,14616296518833199451,9709679389110230494,15170646281284177169,10804474576266537863,8686172415556070143,1794490713260292657,14552822046376658367,14964616641365667603,7089442064459371950,7996060445322225617,1144320754243645203,14415744129760618939,7093889242948584656,12633607511237736752,6984892866937096528,4123640001296376997,12342723153369819089,18071439330607685713,17140571597419676510,3712708621163404624,7386226450971288495,5411985447187773727,8421314860188403249,16211119576392852987,17580795524383589264,16883220404452491438,9233977852440932126,14141252125107296174,3626275983200864976,1002360346855690832,9360716138190680528,546344039235860603,7353659883223302831,8904255528593531742,14547320105724937147,9715267391047770587,17080929818512939295,8938866256625180652,0,4559608645385399390,15928404969532017457,3954383231182726961,16871932344103983121,11679347004343156198,15593209759085299174,13855080381903798271,64137268596965375,266705474620079423,9751496456532724261,15742454227484380709,1287887100985474716,1644410652971735039,1859132029245357659,12573197558617767515,9109690739280873607,10776923192733965406,15841362069730994085,14899599013145818207,13639955446314671198,13477920634560592335,2780912164848100047,15278615469765791882,8714285414785265290,5941410803032820261,1430153261110946604,17100289273923028780,11040271955297822821,17071200406764216988,9668476852251221599,9895003721767684645,3153936802843026747,7699480606592505662,3119053875226460625,7330620731808100490,15319916097711740734,902027016372571647,5399826111157081599,6604231181370637823,1101630450954489343,17853287338562911839,40671337841507116,14152742041155977772,10695019415797309740,15798370895422316161,257750588472287039,6959305524049951653,14438456307317285925,645371294917494246,2467384066317688458,5461156393726888236,10519155070184702346,14946096458386113510,17359804277199512271,6160170829512704998,8772218187294287004,731572502621017599,3573018270485219713,12259753466970794303,2757959953463508798,1072324150668699967,9274107839685286444,3347781619383961217,0,1294067226652996369,6262223192669064906,2245465721835943761,7188788375512098534,7021326331909291503,15208054406643675089,10317521807855091711,3876358827403624447,12797512483158649659,16065357294097355686,5809081645986073223,1320638309939445979,5024134348299022335,13278395041512124415,13069179785724637695,5646412462504315647,17569790443303434065,14646422553449428817,12403904882901685895,8492931008633857007,16694018689981920751,15665926729605168063,17338457385075023825,16916713314484542481,18050641106358560337,1961059986162401329,15464184736905549314,107139235628345290,2099243840330517247,7456901351912167590,16095003650244567259,13849103091250242183,7713874553628187750,15848662083494917182,18274895063551350047,7586034665747174687,7425073725506687654,2690951920952797222,15028027888079605009,14786676868633949457,2680664413823129290,7094005997646054054,7535456479986407902,17519617951791876134,15250719472855562718,17009419489732309094,14548958758795166143,11731653132324520383,12068791865922023377,3823849449299373770,12050450883596284390,1593859349442072047,18030330831435756305,12807199061128308902,600751206211351974,6467634247651996433,15524293985413504613,15884873641818549861,14387569672450621715,8406654860892214047,10818996599212714078,15628181454017037247,18002115260971877139,0,513583512055878015,13565836311664818067,16123525899888459775,9261530383822714981,10017721729767339923,11400458808679958053,11542218322675236863,9976386362291519487,14631124526442357285,11619404437442790821,13431307793259280383,8559606439234844563,2598510412947996671,7313404982199271423,0,0,13837730870329318535,13835961394083691941,15335532326603898277,17880528297569114715,7789939982030108563,17589963009718255013,17784494857415540133,8845173728802295205,6562149728894545919,7361314975839303077,8650409550670772325,874404699256970789,4756882845399311909,6460284610486268819,3878224108810595583,1091804406872993023,10206722112687320199,14291421948681514387,1727034946213542491,11934530701993840019,13797997871996975103,15048069480965126143,13440750353034478995,10443100681662936467,1513063025137857427,15635890984554346495,9874698797326435731,14506635469574714771,16854843209128556435,10959588392862013331,12021372558668029183,15016286683897879807,6720042713221873061,7992946059953356197,1163295734602859429,10264232490362240421,11419271340134415781,17634151894280551845,16531716389043551653,16205666099540984741,2348754845152947335,12029481474092074587,9463190531687738503,12431821747444217855,5816969268609484383,12772183949534915839,5938411363885712991,0]
open Ruliology.CellularAutomata.Rule30EtherThree
private def runWord : List Bool → Nat → Nat
  | [], z => z
  | a :: w, z => runWord w (stepN a z)
private theorem shift_run (c : Nat → Bool) (z n : Nat) :
    rowN (fun i => c (i+1)) (stepN (c 0) z) n = rowN c z (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rowN, ih]
private theorem runWord_eq (w : List Bool) (z : Nat) :
    runWord w z = rowN (fun k => w.getD k false) z w.length := by
  induction w generalizing z with
  | nil => rfl
  | cons a w ih =>
    change runWord w (stepN a z) = _
    rw [ih]
    exact shift_run (fun i => (a::w).getD i false) z w.length
private def hit (i : Nat) : Bool :=
  known i || !G.testBit (runWord (word i) (seeds[i]?.getD 0) % 256)
private def chunk16 (a : Nat) := (List.range 16).all (fun b => hit (16*a+b))
private theorem chk_0 : chunk16 0 = true := by decide +kernel
private theorem chk_1 : chunk16 1 = true := by decide +kernel
private theorem chk_2 : chunk16 2 = true := by decide +kernel
private theorem chk_3 : chunk16 3 = true := by decide +kernel
private theorem chk_4 : chunk16 4 = true := by decide +kernel
private theorem chk_5 : chunk16 5 = true := by decide +kernel
private theorem chk_6 : chunk16 6 = true := by decide +kernel
private theorem chk_7 : chunk16 7 = true := by decide +kernel
private theorem chk_8 : chunk16 8 = true := by decide +kernel
private theorem chk_9 : chunk16 9 = true := by decide +kernel
private theorem chk_10 : chunk16 10 = true := by decide +kernel
private theorem chk_11 : chunk16 11 = true := by decide +kernel
private theorem chk_12 : chunk16 12 = true := by decide +kernel
private theorem chk_13 : chunk16 13 = true := by decide +kernel
private theorem chk_14 : chunk16 14 = true := by decide +kernel
private theorem chk_15 : chunk16 15 = true := by decide +kernel
private theorem chk_16 : chunk16 16 = true := by decide +kernel
private theorem chk_17 : chunk16 17 = true := by decide +kernel
private theorem chk_18 : chunk16 18 = true := by decide +kernel
private theorem chk_19 : chunk16 19 = true := by decide +kernel
private theorem chk_20 : chunk16 20 = true := by decide +kernel
private theorem chk_21 : chunk16 21 = true := by decide +kernel
private theorem chk_22 : chunk16 22 = true := by decide +kernel
private theorem chk_23 : chunk16 23 = true := by decide +kernel
private theorem chk_24 : chunk16 24 = true := by decide +kernel
private theorem chk_25 : chunk16 25 = true := by decide +kernel
private theorem chk_26 : chunk16 26 = true := by decide +kernel
private theorem chk_27 : chunk16 27 = true := by decide +kernel
private theorem chk_28 : chunk16 28 = true := by decide +kernel
private theorem chk_29 : chunk16 29 = true := by decide +kernel
private theorem chk_30 : chunk16 30 = true := by decide +kernel
private theorem chk_31 : chunk16 31 = true := by decide +kernel
private theorem chunks_ok (a : Nat) (h : a<32) : chunk16 a = true := by
  match a with
  | 0 => exact chk_0
  | 1 => exact chk_1
  | 2 => exact chk_2
  | 3 => exact chk_3
  | 4 => exact chk_4
  | 5 => exact chk_5
  | 6 => exact chk_6
  | 7 => exact chk_7
  | 8 => exact chk_8
  | 9 => exact chk_9
  | 10 => exact chk_10
  | 11 => exact chk_11
  | 12 => exact chk_12
  | 13 => exact chk_13
  | 14 => exact chk_14
  | 15 => exact chk_15
  | 16 => exact chk_16
  | 17 => exact chk_17
  | 18 => exact chk_18
  | 19 => exact chk_19
  | 20 => exact chk_20
  | 21 => exact chk_21
  | 22 => exact chk_22
  | 23 => exact chk_23
  | 24 => exact chk_24
  | 25 => exact chk_25
  | 26 => exact chk_26
  | 27 => exact chk_27
  | 28 => exact chk_28
  | 29 => exact chk_29
  | 30 => exact chk_30
  | 31 => exact chk_31
  | a+32 => omega
theorem real_witnesses (i : Nat) (hi:i<512) (hn:known i=false) :
    ∃x : Int→Bool,Drive x 0 0 (word i) ∧ ¬Low x 0 G (word i).length := by
  have a:=List.all_eq_true.mp (chunks_ok (i/16) (by omega)) (i%16) (List.mem_range.mpr (by omega))
  simp only [show 16*(i/16)+i%16=i by omega, hit, runWord_eq] at a
  simp only [hn,Bool.false_or,Bool.not_eq_true'] at a
  exact actual_counter a
theorem ten_listed : ((List.range 512).filter known).length=10 := by decide +kernel
end Ruliology.CellularAutomata.Rule30ThreeGapCapture.Triple

end

section
namespace Ruliology.CellularAutomata.Rule30ThreeGapCapture.Triple
open Ruliology.CellularAutomata Rule30ResetMixtures Ruliology.CellularAutomata.Rule30ThreeGapCapture.Driven
def Forces (i : Nat) := ∀ (x : Int→Bool) (j : Int) (t : Nat),
    Drive x j t (word i) → Low x j G (t+(word i).length)
theorem known_forces {i:Nat} (hi:i<512) (yes_:known i=true) : Forces i := by
  intro x j t drv
  have out:=yes_
  simp only [known,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at out
  rcases out with ⟨b,c⟩|⟨⟨a,b⟩,c⟩
  · have cap:=Ruliology.CellularAutomata.Rule30ThreeGapCapture.Pos.cold14 (x:=x) (j:=j) (q:=9+i/64) ⟨by omega,by omega⟩
    have transform:word i=blocks [9+i/64,16,16]:=by simp only [word,b,c]
    rw [transform] at drv ⊢;exact cap t trivial drv
  · have cap:=Ruliology.CellularAutomata.Rule30ThreeGapCapture.Pos.cold18 (x:=x) (j:=j) (q:=9+i%8) c
    have transform:word i=blocks [16,10,9+i%8]:=by simp only [word,a,b]
    rw [transform] at drv ⊢;exact cap t trivial drv
theorem classification (i : Nat) (hi:i<512) : Forces i ↔ known i=true := by
  constructor
  · intro h;cases yes_:known i with
    | true=>rfl
    | false=>
      obtain ⟨x,drv,out⟩:=real_witnesses i hi yes_
      exact (out (by simpa using h x 0 0 drv)).elim
  · exact known_forces hi
end Ruliology.CellularAutomata.Rule30ThreeGapCapture.Triple

end
