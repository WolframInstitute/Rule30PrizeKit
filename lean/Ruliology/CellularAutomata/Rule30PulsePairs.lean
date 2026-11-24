module

public import Ruliology.CellularAutomata.Rule30FiniteStrips

/-!
# A two-bit readout for paired black pulses separated by two whites

A block consists of at least 17 whites followed by 1001. The lengths of
the long gaps may vary freely. An eight-site strip certificate gives the
physical right-neighbor bit on each white tick after capture. The three
successive block transitions shrink the 256 possible starting windows to
71, then 11, then 7. The far boundary may change arbitrarily on every step.

An eventually periodic driver makes this readout eventually periodic,
contradicting masked Jen for any evolution with a leftmost black cell.
Equivalently, every prescribed right half requires unbounded initial left
support for an eventually periodic clock with this block structure.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PulsePairs
open Rule30Realization Rule30StripCertificates Rule30FiniteStrips Rule30FiniteMaskedJen

private def table : List Nat := [115792089237316195423570985008687907853269984665640564039457584007913129639935,
  113947465846534355848707577528334216114457678769101294627901297138454684695275,
  77081756648648951432750934350252493119681726714899083298209681364853671508587,
  76177130951479127634286400278014724415852024530106349897987720450141596592683,
  76177075736639308359936478800720394312444218917974361884164337087006563279403,
  76177074010992097078958417475088069917098422035412851165103608717655335936555,
  76177074010992097078958417475088058766725822770101279792781562586159995560491,
  76173540316861717558020590277065450843612481681215037045840700226110065484331,
  76173540316861717557824430847788945143576022545543456439235970552804080624171,
  76173526513369020762820766712007831192178638840713672693875233630394186736171,
  18276598471178533858870434668427853747088765287991455918359891028037870297643,
  18276598471178533858870434668427853746408200553991122666404613137987245974057,
  18276598471178533808653620785334407632999626232962283629878772722820824179233,
  18276598471178533808653620785334407632999626230426982429422313919827417768481,
  18276598471178533808653620785334407632999626230426982429422313919827417768481,
  18276598471178533808653620785334407632999626230426982429422313919827417768481,
  18276598471178533808653620785334407632999626230426982429422313919827417768481,
  18276598471178533808653620785334407632999626230426982429422313919827417768481,
  9308082195878321786929399657238249500747145232440464204667349278320665825554,
  87921403909845978509959092149887466507655184321387578072351037331155508676680,
  18166793183279649266187645710646842316974991440479101155992843882222221559850,
  38030306938552811678086419077549010051149760153345990876459986161065547338004,
  7874564116889461385681751830695431111451282615065776868413512733547940567240,
  19184496226424753450904194462762160292203226097124170065211251930438289594976,
  18277205771911492782260199577062771714108133255856410870280841626310773615136,
  72445382366664313912622454054220390534484406391496921730978840911727831982626,
  76063871567306697028886360496259413596006022984091212653338407464874448953386,
  18166957315128933586364372690396280763990238941022588116937585711109497823786,
  76060351622749120968650917841760875198760406283096985010634611324072084120104,
  72427713895805082733710079855013962725569431750482860438460366850558997307938,
  72441835081140193067371950612922727111525119774430543124016329819981235626026,
  14544906166121432814419655216450073110175614570924598577252088854715551457322,
  14544906974919832828938849053537522445422164209631228336044525870305360486440,
  14530771982722032366879484185331579343300703915807960234202178190619824889888,
  14530771979352039033485654210815514752756887214282651856524329407831745765408,
  14530771116633745684665180781471031968128705657894030335226010012516217790496,
  14530771116633745684665180781471031968128705657894030335223704169507004096544,
  14530771116633745483797925249097247525383444115248705019358034136299194032160,
  14530550260750648185756727336909654660568965030724488250134815369211991302176,
  7265275130375324092878363645070801132990035824103286801606879370042355486736,
  113078212172247514051432894264557377598629182470854976671688965217188855872,
  14134776521530939256429111783069669477569712441349164376964261198002915328,
  7237005579122571172730977595466321102296842729886931147235595026035655049216,
  112153378135748396062959377143599284911534244360583446453886050782679104,
  3731637940245649654848823549669958041154899946000076711100271175967304583168,
  3632637565394985979033388978205529201295274219726667600267505000165073748480,
  72370939213704981213526581277150186383468534619895937106733024274974892917248,
  57899579242906637450287648201174173294326745541791292703448685293297217962018,
  18106869845331498052333022214146715944329579242846188058721504555765887672330,
  14148799073654827785749197064643821534117861866289074504599337901645365800,
  72427700038392492604405136126975815150565678110951118522861835567475525165088,
  14530772033271932367786933803072548202138519131964643619030211787557464711202,
  14544906108831546146724545649676975070250165951717298437068357692201753387048,
  14530771120003739018059010755987096558672522359419338712901552952295083221024,
  14530771979352039033485654210815514752756887214282651856524329407831745765408,
  14530771116633745684665180781471031968128705657894030335226010012516217790496,
  14530771116633745684665180781471031968128705657894030335223704169507004096544,
  14530771116633745483797925249097247525383444115248705019358034136299194032160,
  14530550260750648185756727336909654660568965030724488250134815369211991302176,
  14530550260750648185756727290141602265980071648206573603213758740084710973472,
  28269553043061878512858223566139344399657295617713744167922241304297213968,
  113078212172247514051432894264557355820557699530793315015714089584023322624,
  14134776521518083752075039860864636882543529058555813761817978594023440384,
  7237005579017258881062420408762694083841019230048017992084344127175515963392,
  1725436587099375458016972639265702744446043784629826066990934402269248,
  3618558002636918287197406260721434143093835218756634071641005999497112717312,
  210627797213203639676643608482697665810159008137927400147048727040,
  57896928055670460237525651941644246957637739613954202775465816484233575694336,
  3533748050272855239106790279641372494973006568234509446744739775649021954,
  3632637780863931569242117579003945922572606450296116334680126853238805757960,
  13806862690329267814633752694947516786248045242180756992856372606403104,
  57896928918401969246474004603080664032393867674644161624093976435292601589760,
  14530771170553587596945979094957513509413516147990548076904060776382396891138,
  14544906108831546146724545649676972282656849981889932630617154792264816394280,
  14530771120003739018059010755987096558672522359419338712311257141936377569312,
  14530551123468941735444456298627921887942408778795542404154564207056584187936,
  14530771116633745684665180781471031968128705657894030335226010012516217790496,
  14530771116633745684665180781471031968128705657894030335223704169507004096544,
  14530771116633745483797925249097247525383444115248705019358034136299194032160,
  14530550260750648185756727336909654660568965030724488250134815369211991302176,
  14530550260750648185756727290141602265980071648206573603213758740084710973472,
  28269553043061878512858223566139344399657295617713744167922241304297213968,
  113078212172247514051432894264557355820557699530793315015714089584023322624,
  14134776521518083752075039860864636882543529058555813761817978594023440384]
private def mask (q : Fin 84) := table.getD q.val 0

/-- Stages 0..16 consume 17 whites. Stage 17 consumes any additional
whites and then a black. Stages 18,19,20 consume 001. The high part of
the state counts completed blocks up to three. -/
def legal (q : Fin 84) (b : Bool) : Bool :=
  decide (q.val%21=17) || (b == decide (q.val%21=20))

def nextCode (q : Fin 84) (b : Bool) : Nat :=
  if q.val%21=20 then 21*min 3 (q.val/21+1)
  else if q.val%21=17 && !b then q.val else q.val+1
theorem nextCode_lt : ∀ q b, nextCode q b < 84 := by decide +kernel
def move (q : Fin 84) (b : Bool) : Fin 84 := ⟨nextCode q b,nextCode_lt q b⟩
def cursor (c : Nat → Bool) : Nat → Fin 84
  | 0 => 0
  | n+1 => move (cursor c n) (c n)
def Follows (c : Nat → Bool) := ∀ t, legal (cursor c t) (c t)=true

private def signal (q : Fin 84) := decide (2≤q.val%21 ∧ q.val%21≤17)
private theorem init : ∀ v : Fin 256, (mask 0).testBit v.val=true := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem closed : ∀ (q : Fin 84) (v : Fin 256) (b z : Bool), legal q b=true →
    (mask q).testBit v.val=true →
    (mask (move q b)).testBit (stripStep 8 b z v.val)=true := by decide +kernel
private theorem output : ∀ (q : Fin 84) (v : Fin 256), 63≤q.val →
    legal q false=true → (mask q).testBit v.val=true → v.val.testBit 0=signal q := by decide +kernel
private theorem historyBits : ∀ (q : Fin 84) (a b : Bool), 63≤q.val →
    legal q a=true → legal (move q a) b=true → legal (move (move q a) b) false=true →
    signal (move (move q a) b)=(!a && !b) := by decide +kernel
private theorem monotone : ∀ (q : Fin 84) (b : Bool),
    min 63 q.val ≤ min 63 (move q b).val := by decide +kernel
private theorem strict : ∀ (q : Fin 84), q.val<63 → q.val<(move q true).val := by decide +kernel

private theorem holds (x : Int → Bool) (T : Nat) (i : Int)
    (follow : Follows (fun k => evol x (T+k) i)) (t : Nat) :
    (mask (cursor (fun k => evol x (T+k) i) t)).testBit (encRow x (T+t) i 8)=true := by
  induction t with
  | zero => exact init ⟨_,(enc_encRow (x:=x) 8 T i).1⟩
  | succ t ih =>
    have e := enc_encRow (x:=x) 8 (T+t) i
    have f := enc_step e
    have val : encRow x (T+(t+1)) i 8 = stripStep 8 (evol x (T+t) i)
        (evol x (T+t) (i+1+((8:Nat):Int))) (encRow x (T+t) i 8) := by
      apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k<8
      · rw [(enc_encRow (x:=x) 8 (T+(t+1)) i).2 k hk,f.2 k hk]
        rw [show T+(t+1)=T+t+1 by omega]
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (enc_encRow (x:=x) 8 (T+(t+1)) i).1
          (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_lt_two_pow (i:=k) (Nat.lt_of_lt_of_le f.1 (Nat.pow_le_pow_right (by decide) (by omega)))]
    rw [val]; exact closed _ ⟨_,e.1⟩ _ _ (follow t) ih

private theorem grows (c : Nat → Bool) (freq : ∀ t, ∃ u, t≤u ∧ c u=true) :
    ∃ t, ∀ u, t≤u → 63≤(cursor c u).val := by
  have mono (t n : Nat) : min 63 (cursor c t).val ≤ min 63 (cursor c (t+n)).val := by
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih => exact Nat.le_trans ih (monotone _ _)
  have climb (k : Nat) (hk : k≤63) : ∃ t, k≤min 63 (cursor c t).val := by
    induction k with
    | zero => exact ⟨0,Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨t,ht⟩ := ih (by omega)
      obtain ⟨u,hu,black⟩ := freq t
      have m := mono t (u-t)
      rw [show t+(u-t)=u by omega] at m
      by_cases full : 63≤(cursor c u).val
      · exact ⟨u,by omega⟩
      · have e := strict (cursor c u) (by omega)
        exact ⟨u+1,by simp only [cursor,black]; omega⟩
  obtain ⟨t,ht⟩ := climb 63 (by decide)
  refine ⟨t,fun u hu => ?_⟩
  have m := mono t (u-t)
  rw [show t+(u-t)=u by omega] at m
  omega

/-- Once the third block ends, the right neighbor on white ticks is black
exactly when the two previous center ticks were both white. -/
theorem readout_from (x : Int → Bool) (T : Nat) (i : Int)
    (follow : Follows (fun k => evol x (T+k) i)) (H : Nat)
    (late : ∀ u, H≤u → 63≤(cursor (fun k => evol x (T+k) i) u).val)
    (t : Nat) (ht : H≤t) (white : evol x (T+(t+2)) i=false) :
    evol x (T+(t+2)) (i+1) = (!evol x (T+t) i && !evol x (T+(t+1)) i) := by
  let c := fun k => evol x (T+k) i
  have f (k : Nat) := follow k
  have w : c (t+2)=false := white
  have legalW : legal (cursor c (t+2)) false=true := w ▸ f (t+2)
  have e := enc_encRow (x:=x) 8 (T+(t+2)) i
  have obs := output (cursor c (t+2)) ⟨_,e.1⟩ (late _ (by omega)) legalW (holds x T i follow _)
  have hist := historyBits (cursor c t) (c t) (c (t+1)) (late _ ht) (f t) (f (t+1)) legalW
  simpa [c] using (e.2 0 (by decide)).symm.trans (obs.trans hist)

theorem two_bit_readout (x : Int → Bool) (T : Nat) (i : Int)
    (follow : Follows (fun k => evol x (T+k) i))
    (freq : ∀ t, ∃ u, t≤u ∧ evol x (T+u) i=true) :
    ∃ H, ∀ t, H≤t → evol x (T+(t+2)) i=false →
      evol x (T+(t+2)) (i+1) = (!evol x (T+t) i && !evol x (T+(t+1)) i) := by
  obtain ⟨H,late⟩ := grows _ freq
  exact ⟨H,readout_from x T i follow H late⟩

theorem capture_time (c : Nat → Bool) (freq : ∀ t, ∃ u, t≤u ∧ c u=true) :
    ∃ H, ∀ u, H≤u → 63≤(cursor c u).val := grows c freq

theorem no_eventual_pulse_pairs {x : Int → Bool} {lo : Int} (edge : x lo=true)
    (blank : ∀ p, p<lo → x p=false) (T : Nat) (i : Int)
    (follow : Follows (fun k => evol x (T+k) i)) :
    ¬ Rule30Jen.EventuallyPeriodic (fun t => evol x t i) := by
  rintro ⟨A,P,pos,per⟩
  change ∀ t, A≤t → evol x (t+P) i=evol x t i at per
  have freq (t : Nat) : ∃ u, t≤u ∧ evol x (T+u) i=true := by
    apply Classical.byContradiction
    intro none
    apply Rule30FiniteConfigs.no_column_eventually_constant edge blank i
    refine ⟨T+t,false,fun s hs => ?_⟩
    cases v : evol x s i with
    | false => rfl
    | true => exact False.elim (none ⟨s-T,by omega,by rwa [show T+(s-T)=s by omega]⟩)
  obtain ⟨H,read⟩ := two_bit_readout x T i follow freq
  apply masked_jen edge blank i (T:=A+T+H+2) pos (fun t ht => per t (by omega))
  intro t ht w
  let k := t-T-2
  have e : T+(k+2)=t := by dsimp [k]; omega
  have ep : T+((k+P)+2)=t+P := by omega
  have l1 := read k (by omega) (e ▸ w)
  have w' : evol x (t+P) i=false := (per t (by omega)).trans w
  have l2 := read (k+P) (by omega) (ep ▸ w')
  rw [e] at l1
  rw [ep,show T+(k+P)=T+k+P by omega,show T+(k+P+1)=T+(k+1)+P by omega,
    per _ (by omega),per _ (by omega)] at l2
  exact l2.trans l1.symm

/-- Successive blocks are 0^r 1001. Each r is chosen independently. -/
def Tiled (c : Nat → Bool) := ∃ a : Nat → Nat, a 0=0 ∧ ∀ n,
  ∃ r : Nat, 17≤r ∧ a (n+1)=a n+r+4 ∧ ∀ j, j<r+4 →
    c (a n+j)=decide (j=r ∨ j=r+3)

private def atPhase (r j : Nat) :=
  if j≤r then min j 17 else if j<r+4 then 17+(j-r) else 0

private def nextPhase (p : Nat) (b : Bool) :=
  if p=20 then 0 else if p=17 && !b then 17 else p+1

private theorem move_phase : ∀ (q : Fin 84) (b : Bool),
    (move q b).val%21=nextPhase (q.val%21) b := by decide +kernel

private theorem tile_step (r j : Nat) (hr : 17≤r) (hj : j<r+4) :
    nextPhase (atPhase r j) (decide (j=r ∨ j=r+3))=atPhase r (j+1) ∧
    (atPhase r j=17 ∨ ((j=r ∨ j=r+3) ↔ atPhase r j=20)) := by
  by_cases h : j<17
  · simp [nextPhase,atPhase,show j≤r by omega,show j+1≤r by omega,Nat.min_eq_left (by omega : j≤17),
      Nat.min_eq_left (by omega : j+1≤17),show j≠17 by omega,show j≠20 by omega,show j≠r by omega,
      show j≠r+3 by omega]
  · by_cases lt : j<r
    · simp [nextPhase,atPhase,show j≤r by omega,show j+1≤r by omega,
        Nat.min_eq_right (by omega : 17≤j),Nat.min_eq_right (by omega : 17≤j+1),
        show j≠r by omega,show j≠r+3 by omega]
    · have cases : j=r ∨ j=r+1 ∨ j=r+2 ∨ j=r+3 := by omega
      have at0 : atPhase r r=17 := by simp [atPhase,Nat.min_eq_right hr]
      have at1 : atPhase r (r+1)=18 := by unfold atPhase; split <;> (try split) <;> omega
      have at2 : atPhase r (r+2)=19 := by unfold atPhase; split <;> (try split) <;> omega
      have at3 : atPhase r (r+3)=20 := by unfold atPhase; split <;> (try split) <;> omega
      have at4 : atPhase r (r+4)=0 := by unfold atPhase; split <;> (try split) <;> omega
      rcases cases with e|e|e|e <;> subst j <;>
        simp [Nat.add_assoc,at0,at1,at2,at3,at4,nextPhase]

theorem follows_of_tiled {c : Nat → Bool} (h : Tiled c) : Follows c := by
  obtain ⟨a,start,blocks⟩ := h
  have valid (n : Nat) : (cursor c (a n)).val%21=0 ∧ ∀ t, t<a n → legal (cursor c t) (c t)=true := by
    induction n with
    | zero => rw [start]; exact ⟨rfl,fun t ht => by omega⟩
    | succ n ih =>
      obtain ⟨r,hr,endAt,read⟩ := blocks n
      have phase (j : Nat) (hj : j≤r+4) : (cursor c (a n+j)).val%21=atPhase r j := by
        induction j with
        | zero => simpa [atPhase] using ih.1
        | succ j inner =>
          change (move (cursor c (a n+j)) (c (a n+j))).val%21=_
          rw [move_phase,inner (by omega),read _ (by omega)]
          exact (tile_step r j hr (by omega)).1
      constructor
      · rw [show a (n+1)=a n+(r+4) by omega,phase _ (by omega)]
        simp [atPhase]
      · intro t ht
        by_cases old : t<a n
        · exact ih.2 t old
        · let j := t-a n
          have eq : t=a n+j := by dsimp [j]; omega
          have hj : j<r+4 := by omega
          rw [eq,legal,phase j (by omega),read _ hj]
          rcases (tile_step r j hr hj).2 with p|p
          · simp [p]
          · simp [p]
  have inc (n : Nat) : n≤a n := by
    induction n with
    | zero => omega
    | succ n ih => obtain ⟨r,_,e,_⟩ := blocks n; omega
  intro t
  exact (valid (t+1)).2 t (by have := inc (t+1); omega)

theorem no_tiled_period {x : Int → Bool} {lo : Int} (edge : x lo=true)
    (blank : ∀ p, p<lo → x p=false) (T : Nat) (i : Int)
    (tiles : Tiled (fun k => evol x (T+k) i)) :
    ¬ Rule30Jen.EventuallyPeriodic (fun t => evol x t i) :=
  no_eventual_pulse_pairs edge blank T i (follows_of_tiled tiles)

/-- The forced initial left support is unbounded for any prescribed right
half, for any periodic or eventually periodic clock with a tiled suffix. -/
theorem forced_left_unbounded (c : Nat → Bool) (R : Int → Bool) (T : Nat)
    (tiles : Tiled (fun k => c (T+k))) (per : Rule30Jen.EventuallyPeriodic c) (D : Nat) :
    ∃ p : Int, p < -(D:Int) ∧ conf R c p=true := by
  let x := conf R c
  have hit : (fun t => evol x t 0)=c := funext (realize R c).2
  obtain ⟨a,start,blocks⟩ := tiles
  obtain ⟨r,_,_,read⟩ := blocks 0
  have black : c (T+(a 0+r))=true := (read r (by omega)).trans (by simp)
  have nonzero : ∃ p, x p=true := by
    apply Classical.byContradiction
    intro no
    have allwhite (t : Nat) (i : Int) : evol x t i=false := by
      induction t generalizing i with
      | zero =>
        change x i=false
        cases v : x i
        · rfl
        · exact False.elim (no ⟨i,v⟩)
      | succ t ih => simp [evol,ih,Rule30Jen.rule]
    have bad := (congrFun hit (T+(a 0+r))).trans black
    exact Bool.noConfusion ((allwhite _ 0).symm.trans bad)
  obtain ⟨z,atZ⟩ := nonzero
  apply Classical.byContradiction
  intro none
  have outside (p : Int) (hp : p < -(D:Int)) : x p=false := by
    cases v : x p with
    | false => rfl
    | true => exact False.elim (none ⟨p,hp,v⟩)
  let y := fun p : Int => if p≤z then x p else false
  have fin : Rule30PeriodTwoSideways.FinConfig y := by
    refine ⟨D+z.natAbs,fun p hp => ?_⟩
    by_cases small : p≤z
    · simp only [y,ite_eq_left small]; apply outside; omega
    · simp [y,small]
  obtain ⟨lo,hlo,hzero⟩ := Rule30FiniteConfigs.exists_leftmost fin ⟨z,by simpa [y] using atZ⟩
  have left : lo≤z := by
    by_cases h : lo≤z
    · exact h
    · simp [y,h] at hlo
  have edge : x lo=true := by simpa [y,left] using hlo
  have htiles : Tiled (fun k => evol x (T+k) 0) := by
    have eq : (fun k => evol x (T+k) 0)=(fun k => c (T+k)) := funext fun k => congrFun hit _
    rw [eq]; exact ⟨a,start,blocks⟩
  exact no_tiled_period edge (fun p hp => by simpa [y,show p≤z by omega] using hzero p hp)
    T 0 htiles (hit ▸ per)

end Ruliology.CellularAutomata.Rule30PulsePairs
