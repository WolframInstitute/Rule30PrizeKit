module

public import Ruliology.CellularAutomata.Rule30BackwardVacuum

/-!
Finite backward-vacuum certificate chains for all sixteen new six-bit
black-ended cores. Definitions, one-step predecessor implications and their
assembly are kept together; the general padding proof imports these facts.
-/

@[expose] public section

-- Certificate component: SixTailBackward100001Defs
/-! Generated exact predecessor sets for `0^12 100001` at width 11.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 11
def N : Nat := 12
def tail : List Bool := [true,false,false,false,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 1317989400684132247985462012217008492691201352246603794343706666106002621345561402409288057184803891421955702295376321167301153177543164830484060369180090017640453495090693794266442291580023684417164027872494288824460186556094461377712526642456239223829354337386792673889867678111635871950739338192516214902167506932502668247458716151002211656322019560292365041312606140162746987742145281007848629457461482662396370400050857265093955131417747864622795962383692493719340178441553202898291525157677655586689669236231444940542635973249732161923962974338102025256960
  | 2 => 1751908409537131537220509645351687597690304110853111572994449976845956819751541616602568796259317428464425605223064365804210081422215355425149431390635151955247955156636234741221447435733643262808668929902091770093793903262101427020667245404086806376697406385616626656709576385194849683752141293079934664734130970765878715171136162413072204924748873679065711426447998850066778333718121991964513739512673072339149010837460911739847867210523319581621310970316642246779308497122238906298733418426677374861649143537026598176315370698624028790832359356342725644751882551273418615338243510404238335279104
  | 3 => 27373568899017680269070463208620118713911001732079868345900368032400627398718725292926268515275851627369364831330611136320742589481102451961246789098172553796310440059930898937831532899140431697171996589133372471298476111108549982396631949032816042695338510810450306688361361341374187746597130687730785433918035877307301201106010546800269207441184151848083044844303430585173620321866859358449430993512509965788634300449476566452937846926468905379725292059362881641023577917146879476653395984596381509820407536177924414733086977494570204801516147034391649652224148646014048795380196145249967407104
  | 4 => 2830360686206494015618260612961201965531482417425069711887864957172916206599794486414315782576699888824556990922729544316721005326280942714130736553281220605850220879759521892631204991795510498766854180024563807712780964482489126000367039514864275232218049309336693170010183686314883550041185613819885718530151534752233734599534650355749042532377018848119517090447662054959434547496636676416064070556996847636463649993555483457119191347189016081390518293520439276270554224449952689924981210638426984079698226366130714716757286084027081508215918264722236709263864517099520
  | 5 => 1593375729078624757834311285001526599239683186684251774969581917460247882416775459467729816104120843283852369170877115390986064722139528607288195340735039504592972721064074653105784049741096097203529696892371133786586341040034582622191081752466667455207243968322294712819735780160185363709119737418408925362049216839850670171528013069776779806535708934815713683122307015609784909439068218467984800170799506292306562754867660108573992190874872086852000300810531658481141782231079706261516811971912210821616689124451049910811102070019864820610282075891119598576153701166643239162057064448
  | 6 => 2019812879927269695613778158893852118390193932184884169330400842536360511893303688708883175411331825373449152297652616112775356600017716672122884917828526732719753555478493975704922126600471118222486536967484669092991959316674880811796692224832047175220689896161960929390130199367541192940215261419604488471375611583581058129598537930637734853402721520805713313419533382680613906910021484959699342212577464066211683532652466710055031688217906696524524607917542306644685496490691327395379778286261955338321480196855004102422073736833122866441729016826043160173602112978086501469171658339862002975324536438520731926528
  | 7 => 505939456621781934182333634262711907723457786510614666702623247608958432828961229629170052401352843063304833797108182197240487785100483631355172060168818570002500441461660283223929116715087128073061495400438903707492336731580555441582045701300990582485412814383512484312848985549011221308746612487502741102968009902776019813253842167705620865892699313341877923170745709359194414733039710890254395680040380733763588402229843144029568297994650436808391462690767427205660215894342879588368381589993953108201414428725717925962777241424396136997374870267200708853195210496731855839994504982316700812617672310194540905540
  | 8 => 1009921849677805655225254357077489938146191822121588806868201500524550573448193004328724958002615625331404071737897323981654162684115458824432464128529597219200397118068895536435884805070325813758820581627543053543453842986212552146092355020385681425497659370193976100491742320612630459033107954455537721141518009503268422745401285553931348182057017460061368651354148456044250017145109099486428100134439066631947684388580153036472869707463700120141612825757511010159647112092272933537436840100902753041220177504414685346630591378278970157520096476549435752021173022630313927549285822303016111742200212229507931703424
  | 9 => 1972473515094665972944023235392453122585699625837126710945455653535440377128167168774243250215021573711469602107049439764163021080099563470025651739763740444058521001518386462215310814495305163478574112609874223312128151189635089053992185973495524787023921700533499026425388397061497358404760372959632548679801455471819096320843650858518863340052021255430261145898979253761549615526244139707783754325870462549774469639943459598820907235336832665409791113128963946854181388843912570405317273021186370422831888782765863268725037733750233357483987831773113937857583047095362241513749976816850895043503907293567648256
  | 10 => 246559189386833246618002904424056640346398767971044437844205305923353721326884737972088398179181625952391585344234323973285353864258029785682259204724273073597407738807842275606582135946962245378390103032097460789847522003189594174891680586826420491519968853131627906189734625984040426066727338297659926022487073893672833801092980733532938775779034357733565374209031747996072849505491072212103550671273919406725717414261079770780384834268732515426723904768350380442150641388100633098617297770558007055764080895297501874134621834990018375355320612171405830890492677232368552636823944100558567737658916539318992896
  | 11 => 28703274225248587860240897297057851755587621029967813031908150430214378589581920526192182724891406339481426807256947066629220304248533733167513788959496673492964260134865600219034330380914610977078080141289898597726869584683415635384000362852907650881640438611102775213230872427219883869342612965973874165649826778203406694488326666924691466871541626497031899050487929281529433379840931762485318641860592098023494269930183318087115704742279863533651596777818891671248812825360119267838522680347285861397556024324796370832440833190287544892258524849757080987807583546805464360284314387456169567556993024
  | 12 => 213856007023575627102112993817344677452429701031873971312867207894190981995160798577930288867813623576064124652033302683157633938723065777897569881568516501091772495715321587590954279962874156307868271422755888165618541122588710089953350157619489476458875169256662749859788536092771915015168817978984603026852523165723365611206807065226702155868858523483404475445065903425598236306175238049571458475783762100294437273949870662860301108011928454444745527490200455490515753234728805730997210095575395109465733580133584092252619513974493134338434166406877891818646831406589803732665538850516369424
  | 13 => 63119152483029311134208743532558499922742388026788054750254580913134092068101349400775784006880690358767027267425582069324452263965802580263844067848947909939171524277967751204727309931880629493052765259975288332760053917097130950328367609215699072651551763020763561149847707824718829676511346343302733681546072348037553882961182317625683135884466224597774042155451614037851309531164820339911551456875797023580899353910008359664207006616463745096348849301413262110625416495270841626044754631658390983576283341312813449794672160373154548036741182251054030066653459377613962178359692849381476228694163205918482792448
  | 14 => 157116580091015368459875823523641645037079018622232775651791514674285674485261122730377591974181566269709146733693208801868779954374066038959587047164187945587589305244576910023937953327072539218243905702460144669954918486219555720532173395667103935610549145058165657002716035583194357997901607959950386793095812407332950240925825308105618911502768423083330841525583287057491932048768979126041244698978214457646966894301225383105373575423336244962119140903159838026092434001036943447715849860529464190001853824803704259455893376738401107802378923367596032
  | 15 => 2030684202530045705555113628492582013902486762858899984101222940720833585354594068410377813909696557106868748039287806440327756032912128284695211906920520342013207884701066631582134258521945358626603732205641463607185100031672051229116235490597863813854851788309325872133508186377795228505841685013845492411677703316134923376236733581269153875124534380113883712554707558946274649125223296912298659973934033352297156342401790425641982883703750601121688798865165442793585729649675936444892108805080509772897461425651584812126830592
  | 16 => 22764757236272150845448608801544890529699448070214573731542130224001885731721805946360208679001072341752808202824217284477494812905121433368607413453405435241035171026302307078844081862378898986287227723031901649882194160845698588267699583066325683519210396334860609957459378162416780929141270829595389495389133348556933419291404463361528399509576771317627518967750592485867313959666142869543658007128819325087866638628344845905209826777292546113606776832405698212781255130446003437568
  | 17 => 16158503035655503650357438344334975980222051334857742016065172713762327569433945446598600705761456731844358980460949009747059779575245460547544076193224141560315438683650498045875098875194826053398028819192033784138396109321309878080919047169238085235290822926018152521443787945770532904303776199561965192761047051351577287005728952652821735984108986866610276357675617870244379434256980638641483535093292326373531858799166625357628570460558031263448272521936380677802446789067842847500729660664088708794565812766370851851942073975347730759844719138465132286353476323058907951442632862271715932249195604970341910183936
  | 18 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001

-- Certificate component: SixTailBackward100001Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001

-- Certificate component: SixTailBackward100001Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001

-- Certificate component: SixTailBackward100001Steps2
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001

-- Certificate component: SixTailBackward100001Steps3
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step12 : preCheck K ((List.replicate N false ++ tail).getD 12 false) (Q 12) (Q 13) = true := by decide +kernel
theorem step13 : preCheck K ((List.replicate N false ++ tail).getD 13 false) (Q 13) (Q 14) = true := by decide +kernel
theorem step14 : preCheck K ((List.replicate N false ++ tail).getD 14 false) (Q 14) (Q 15) = true := by decide +kernel
theorem step15 : preCheck K ((List.replicate N false ++ tail).getD 15 false) (Q 15) (Q 16) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001

-- Certificate component: SixTailBackward100001Steps4
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step16 : preCheck K ((List.replicate N false ++ tail).getD 16 false) (Q 16) (Q 17) = true := by decide +kernel
theorem step17 : preCheck K ((List.replicate N false ++ tail).getD 17 false) (Q 17) (Q 18) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001

-- Certificate component: SixTailBackward100001
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11
  · exact step12
  · exact step13
  · exact step14
  · exact step15
  · exact step16
  · exact step17

/-- Uniform column exclusion, for every padding length at least 74. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100001

-- Certificate component: SixTailBackward100011Defs
/-! Generated exact predecessor sets for `0^0 100011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100011
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,false,false,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100011

-- Certificate component: SixTailBackward100011Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100011
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100011

-- Certificate component: SixTailBackward100011Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100011
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100011

-- Certificate component: SixTailBackward100011
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100011
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100011

-- Certificate component: SixTailBackward100101Defs
/-! Generated exact predecessor sets for `0^4 100101` at width 7.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 7
def N : Nat := 4
def tail : List Bool := [true,false,false,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 4722366482869645213696
  | 2 => 21267647932558653967613834469092360192
  | 3 => 5316911983139663565690434912111296576
  | 4 => 10141204801825835212523381458944
  | 5 => 309485009893402662762708992
  | 6 => 75557863725914324467728
  | 7 => 332306998946228968243966163579584512
  | 8 => 9444732965739290689536
  | 9 => 170141183460469231740910675752738881536
  | 10 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101

-- Certificate component: SixTailBackward100101Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101

-- Certificate component: SixTailBackward100101Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101

-- Certificate component: SixTailBackward100101Steps2
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101

-- Certificate component: SixTailBackward100101
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100101

-- Certificate component: SixTailBackward100111Defs
/-! Generated exact predecessor sets for `0^5 100111` at width 8.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 8
def N : Nat := 5
def tail : List Bool := [true,false,false,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 1606938044258990275541962092341162602526925360265662480515072
  | 2 => 7237005577332262213973186563042994240850641689535093906432559913459056115712
  | 3 => 25206486656162139942283408814551425115726423286211848175680
  | 4 => 3450873173395281893717377931835411013689777664060010308813497034604544
  | 5 => 210624583337114373395836142479626796398655807444784530366809505792
  | 6 => 3370096177428662549712438821866328563869674290033663802344229306368
  | 7 => 14134776518227275503921912379727790871922952195198546151671126788784783360
  | 8 => 220855883097298041197912187592864814479084524216769223218767087739600896
  | 9 => 68719476736
  | 10 => 57896044618658097711785492504343953926805133516280751251460479307672448925696
  | 11 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111

-- Certificate component: SixTailBackward100111Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111

-- Certificate component: SixTailBackward100111Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111

-- Certificate component: SixTailBackward100111Steps2
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111

-- Certificate component: SixTailBackward100111
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C100111

-- Certificate component: SixTailBackward101001Defs
/-! Generated exact predecessor sets for `0^8 101001` at width 8.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 8
def N : Nat := 8
def tail : List Bool := [true,false,true,false,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 1606938044258990275541962092341162602526925360265662480515072
  | 2 => 392318858461667547761004486883037804972858128243487670272
  | 3 => 421249191782635688338395187855910905047545647780953685456731504640
  | 4 => 1766847064791239833937556495156832568144945707417758698693990480212918272
  | 5 => 904632706752666235962034791112005348677772482317568746437442502369545814272
  | 6 => 226156424344289340020940673535407586574198466656875044685142784755575586816
  | 7 => 1725437409449919607461710043402296785520141325815789610988888494571524
  | 8 => 842498333348457493583344265025506424433759966595489862602920558592
  | 9 => 1606938044258990275541962092341162602526925360265662480515072
  | 10 => 392318858461667547761004486883037804972858128243487670272
  | 11 => 842498333348457493583344265025506424433759966595489862602920558592
  | 12 => 3213876088517980640286904978804817771196723811124770984951808
  | 13 => 57896044618658097711785492504343953926805133516280751251460479307672448925696
  | 14 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001

-- Certificate component: SixTailBackward101001Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001

-- Certificate component: SixTailBackward101001Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001

-- Certificate component: SixTailBackward101001Steps2
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001

-- Certificate component: SixTailBackward101001Steps3
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step12 : preCheck K ((List.replicate N false ++ tail).getD 12 false) (Q 12) (Q 13) = true := by decide +kernel
theorem step13 : preCheck K ((List.replicate N false ++ tail).getD 13 false) (Q 13) (Q 14) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001

-- Certificate component: SixTailBackward101001
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11
  · exact step12
  · exact step13

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101001

-- Certificate component: SixTailBackward101011Defs
/-! Generated exact predecessor sets for `0^0 101011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101011
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,false,true,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101011

-- Certificate component: SixTailBackward101011Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101011
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101011

-- Certificate component: SixTailBackward101011Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101011
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101011

-- Certificate component: SixTailBackward101011
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101011
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101011

-- Certificate component: SixTailBackward101101Defs
/-! Generated exact predecessor sets for `0^0 101101` at width 10.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101101
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 10
def N : Nat := 0
def tail : List Bool := [true,false,true,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 4249103942534136789516705652419749018636744941816255385595553105603228478886817941913300018121834285351114635889972008122772634701221663761282709153744371630289981031815224393163866112
  | 3 => 9516908214257811601907599988159363584840065290620124537956939899622020205826587990689077212775400643774711832257235027522909345571487396529861315719055326314814455073792347245307224163568933595697422149216092441761606229067073230804364931451679374391341388606002756129612438214868467712
  | 4 => 126633165554229521438977290762059361297987250739820462036000284719563379254544315991201997343356439034674007770120263341747898897565145822484177753904735444846393260786157879296
  | 5 => 89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737068892787911683731292425163608903546110799409451772239191746199797202053246477510444956207562702033389100358222242362999049846181264125702651381636615110656
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101101

-- Certificate component: SixTailBackward101101Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101101

-- Certificate component: SixTailBackward101101Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101101

-- Certificate component: SixTailBackward101101
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101101
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 73. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 73 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101101

-- Certificate component: SixTailBackward101111Defs
/-! Generated exact predecessor sets for `0^6 101111` at width 6.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 6
def N : Nat := 6
def tail : List Bool := [true,false,true,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 256
  | 2 => 1152921504875282432
  | 3 => 288230376218820676
  | 4 => 549755815936
  | 5 => 144115205289279488
  | 6 => 36028797027385344
  | 7 => 281474976776192
  | 8 => 1099528405248
  | 9 => 35184908959752
  | 10 => 68719476736
  | 11 => 9223372039002259456
  | 12 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111

-- Certificate component: SixTailBackward101111Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111

-- Certificate component: SixTailBackward101111Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111

-- Certificate component: SixTailBackward101111Steps2
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111

-- Certificate component: SixTailBackward101111
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C101111

-- Certificate component: SixTailBackward110001Defs
/-! Generated exact predecessor sets for `0^14 110001` at width 14.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 14
def N : Nat := 14
def tail : List Bool := [true,true,false,false,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448283120630877367300996091750197750389652106796057638384067568276792218642619756161838094338476170470581645852036305042887575891541065808607552399123930385521914333389668342420684974786564569494856176035326322058077805659331026192708460314150258592864177116725943603718461857357598351152301645904403697613233287231227125684710820209725157101726931323469678542580656697935045997268352998638215525166389437335543602135433229604645318478604952148193555853611059596230656
  | 2 => 6618101122405145579226797354461794233797363068350757088890617253739824155567158414016435442197129096347988290039858332139252143230980594030470965356514846555693057808869694496032107873479147555295912111331204197924096945708536202851208503366551745445196246047088788933568184180354148242976351068731760947085666650651039876023864766997182892276589111286598577410277837838466770844413959844395204909585411598734954245262583303539123437431560341541603103946003384640667996852937685849725599535310132054631970125671904833441743220039917557074038841342567276146023930656382402769982739830122949477224658407794180287446156631719237574347512972377143138851154103784456748148477267650761202338830781019935040057447233974113628887009715060774892063596433649186603069910972990852325378673351285458173992676913102178579101734547272031467264527343106197184028018289367037003809235626268684351583639317711385397958533836880889789657606264667455584468352424749610094497563122735881480861047092701805943426130231327239937637561870813999859522574342052091384673054938003206430117841333886322862951251680796009396063226537962828841992161092152374057816367941622236593798229832973151068031950371018861784638472194531220575386373749770690317127410164340282570783255402663612467341585727622908836896019897040719067609155101829200245722806690142081769860671413094041942074323489434852094708012018185842913280235306269800580089530245494411570141734184004971811138507979933165083897232973836050653919693997977006664301379225014968018816319562797237033216512819327311110227388786349038735614463890411035411321583537285806313711535044882885821787262418521242960124144069037006983525515674336884853114493261564339452526678901449997129460051367105551900437281623991064416416593980201366769466298102072934109534800191354379262573342504918788638055962501120100976544734916222208432625908860974690997808320875829180219829479434165206282156870493548537787279673102134142524112258930155205916149771823204388645378959709095348458621357775002376839247182826835136604914685951493019559726415081045449508480362219235002320834441603633907141903302978721629457473700985207145265588761627598611420109871602264095758594108396189696793104142670058371307891388871845904654801838282912051339958504125282589198721055412406516543010345522146295409281177346924531438712326529174078266669384032013710799591156538105262954899394946864233439010890620698735799511274689900471507956107211493825622040242231882517153199937145001482067736923591548538185729670674095343563317482176185170007866514835202996421989256464728536493771990759835112370255247141256842077797359061123724589192199377080900018048936929796515640219367686439903410556321997677177800720477482717084951739614826914885760499099273944920876107001531662099402896326451770987792815238780680000671637641442421990615554057747391455632523932128562491013385481887398217521615679761779524513024496021310649931926379282626059439501672656218418523567020441506231513541755381170284031972751452854719410498527756252692541531499573092493446328083698636746420907581781504843852673207096447094860771800032714300576723709169161272990546115303804144354426203998587332743641726076196679995196940564862224790665715399404885022682653151944003473979016803913832038958896304557826626751610274623747376176364217705641157266281074229210667693116107264032438957316267342636694895952233192457689309264215998463892588419445009490070671838574961725529921328826455206693472745178095472949658383771454853758509711800182320588195675973129142140995667920777640708135982069958659102695518891359361863897699617111942752834238094858036168538841263709549689855225895044811723676161481969153470802163036748719542971758225306608289285891659574583457074482682170775469954284399417204216505673633057057353606968361149523863641156853759540501335641096136937761031614932284026105711711168105992001945228016034328246566056100569284025315647302276138117052990220435631936863001145355238336593023111564406325968314019703342652592295139070145962399856472721763535830451260496064979341128836880009265521385424747202437911697758274559778887114373685074103787690558883722233004465376396493120924484770509119040487497462391362323543329831778239777018627892281509971726741275180691631513601722422320491791212806391160535897488411008366872714154951833619425112671891306664536415241833178703835797281236909276467886652464601725198399362152551579485579751901276705130945063300806954075020654339268374267988802174214486476552264403608989986930593692111461862262856479774534688731088098383967482741525399562413223075842202441796184250281962195847140864914119649656832
  | 3 => 493600531644361024300188265991694997637507520604700710464703045780871885032506445216235502957877094021988778563994017089462052427550340867391359936408656111392993654792803144222167555824215005404508304138378675708899187195233545224889493565893125228352285069532161037414113085387782428661091064808303506873219382367545350146187274792570630411540165864620585810800140598958842141301603739639114646362101329880190622044849524972597335117225735841209227443826765750312158102842031707733458162298503991203455296189091649919760483000106147703139835233993661528587278571222575960351829366217889691683059979101398070717487009184549080774549247063283807609718440301756596180137687963365299936108244471165939993815282418664424571352254170038690942132580594591839743443012123625928329095498107317683278864036148163121164699697108714293223400320555614029934709540770397546944549960726712398935810672735680486189272012646214687064455421531980198884179246775993928121264048397906185943134882059997500857324516623616458871214775087443837304014011057470696802568005064418640883475582422315785589133159335219806154661185890623087675004766658229017817928480776905031994572695415134234304097518836164098150757948652158460756019471355327570258330304960997179511152887605189368977384094322162793185232327059879847874015140342067520631235306714541314112843139595731859945851361906189591224735014522962681832534344772648093516694047949759648557858560403080552590510100734047161274307500515229808973139271585074970510011919118714209705368803644945438668183065717147170872113083825556891408979226032793201278006317549910966199227349547092135478316828691395515916427533809399449676291537361744204817503838159763732121880529164744801346343387966165594293365153182737320481033072907587351260282877276596758761817080894519405540724772276153466147674206739592072200400888123150035332670021093105428840406471602633272349494557301403916716718128640660504278420758748684739143440985921242538523428067224061959679848671067430718526721794474515335330377779555673987634587577425410905139899595724719623611511231133651336087727866636345965768958345064409215855952778125466077421692454385757448674388633995783909187587699924712509863586633119955427865199831331437180396881991551259128975166217213372090766587390598766933762616024051573881928653946072438183844906200001258721112225862178664350153492131328823905275905694792999437598707130757744748214833521938499176232084699668480144618155443411556531622237183652030134793016520366424641701947607520555190927593717944208044763764194767240125077792323185195218472617866990535310402986842283858827044147276420556487879989023167720925725779302176849251437241621155919033022918916152082633332003962316361527281406134659155956935622430715855746722053159433586983974285823688326251749891395459898795376067244150352591655581610046796692485173025785630328149105327181941108808556300881832304668037352097902137443806966222571444838202669317791579805903812496233752097222866481969955847633515564488975098046827373361096759524817766666113068631238113982564014088569592599970923340453674607878406185018023466519101332949669729173532337047474286495243714802267228676177868296895581076499724032932577836923146719644205589840059529722838998909147120266258073107115505443261330393921361401480624642369275259234022013413658706316683215280031977205394372765401315295769507176621083944505107107154039313039301856292656738333096218467031080394222064050821383699280581937371460424054266725868142087273838525819806512487760138536668844997982081445201971183508264673808921136006303997845551468738604451828090411323127131535984252726695185365768922008981496787218349808680290574047032934379294004617699282040767926629083544579657211138423374407310851689523911976678452812294115802420540279608233325804395418010379058859219868703183569794402594680852604393712771132271490697740081287820832840941101549881554263704999453318313903192378612199769758266309178332174495077688192064157211736159954263740431920497745899338857007763151768308315135753886091772401662195087864785394980968556900141183407788445895694647088445552487237645352904247582378365461598594081605170853700674807718395139931914095529046011158966725916232441343282426490076309279067563682085289618665690961859100510264668207304592302008524028914562215031215227830021698819391044691657503877701176904739175861607693644106870609862852233889848551099155007200479040720764101449211216867670112970201645149353744253082794983424
  | 4 => 304422472668572751599692102460263837253341191388884346748658592201682111056853433714599024719790566984547899313708635319085029470053310869103909087098637755704585724590969765117877907581574400261238862410250752434425485358590974497764725873811182020387122953717620990813318378568277306645347196999464605530780412241270056778667600580245749713483711824977025082025598766522779552623477608262506736391967107871383201048269818740242557797562631552541097931465539026634683275492557296286015868138376639698757526850368890475045502188232333346246450473719539829712483259361072569287635262778543862273095724713652368404153261402238393856340321011365157436152258974045746135831242759746220760944682470303388464249136781818258691775446650551972372736424901193829364759157521136588012577203549137117477308048121770337030119816896992011906257572263203626160606944869254869297123948838649681308033963320967584853478949962707678311856713349487990766403450242033701034609778171934641584786599829374037962516114121524829870697136228061857575366777314063183411756994556313298633147929495307512853649304910477199992462765555010942588709329570015917510031974918240066113448841725378472471275707527311054640776465350671377561598002026494885831268732349895861393335839427868409916601405850385461539051106139752397463952700474273158225645418770313391634154660992189485598532200370432267588661515008253213742431060573884924423894204453672318104852365164260454659777964357084858717403454947136531759558070606345448158419987654835840007835004054882435210973332191441967116362848612039518349754322494759706172200995378659320286739981051986447843129492801986147809616166273921941597756631996171582839779852134306773369458531893292343810411361477892239062151239314250612357475033313020042037691831329519486560489668362835959414986838927023584804011348352278207136611823440988618187493641786653167536557864903923629080340204214490431023043253228281384788810176397358600465308475447437352758799408375150112234137065534952335220908987594096657669841905183414410245974399901213888264197112335636943960700209884867502874598663282565942936910650541738486569235346019620936753164432155448900046914500220912240648330464751653368386743733573434143608798192357480644989007170053845266066047381423327548124712076556896029480404096197721736556968006997439704979266981205807070417584097230320881811000019474939865376078995787727162628481971163211596531660123911686583130224907913231000106776319244386961066679705090147961596723617296247542690838789901937994168875843684113957674308774931584607043469515452548128744488346420953948463508653688467157969005959498174390424045205361399976013888765050404330950715976977160172601191889206448625822455861726561806158433572071945758771325035224202213096900909118137777109162131385642814908078969856895070593396746807836942014139182673892458303165279277828180062598450950270875032075531841443724130739089649648725163945206975033670782241142144034133729728543780042738279593377968700184226939756481559396352
  | 5 => 6850083439984847370755782630241201997003038219453190368047719735869930036071829138847427743586154051355486240161752007943088217406504061213298900951085287649036423582764176172465063832332271586898351038289971200289575242386895049521421714897640636557997863619157041202439126318254655698707874744862529766817784798972031133236769344446857365597419357183496540373644085906335291150297620493712519167378455829296548356573772803639835163663771316870493401429780038575757871213640836129810123018681444482421528575610944618972010253906964008143049339997516956643539305018007173171747748002469150902929286853231241319818755040774280825272584561742851213934681745413972930020499583720042502554516600285387301846744372381003556348038867175950585053868937723863628425264459721356405164754577573454198051814475987964807191373412054854520218053793916533001357468870422385695774311856887933853021335750488302263049837301747172475844484259398874613350177508956103950588849786928960354200357972301784178923393615042244170535780876803428361938569694299167676228189765275417897946466532211754151486306719444949632660522877143161042958854885786526073326492024941632894086215535577782900592638687376864685339407764043989773794098688699083042358045708481483201158176153488140058791188752131801874138983981229765706847297563342476093882163852024440783314302402987787226324366131554246109619504728821957262801535572732225799682050291413614173344871911694206039546455432362158634412000648543941760327568355754782292834747724348539795061807285140961650912993990503739392217004954994467248562816125948165361275652308977125655180517737669908960378366973293592170686183662857838509035617842166608376955458207801930289204037260616057109055165671060759012438972863586123938823235988224759473136825017118203762520632792101197476189304604689380195717804386953416925082181172438442199561624916782567597547448521424396678375777188626746021195811057411326525162004777379880140771367802300765285966481019652929249812754509165476420099275816468850704847525604899236269664851812725475797104052114780187783951574453579109617166209397927571745883896930233706428112148515901725176702086970876793089230674085448751080258335992725290060047276476095964003717616923480137066144843405057140798225424060215668756822639862395053691213235197971822032841394273068093414548594624205521358026643569688983119585698090563542150889020110675384171121939401872575063479763241603045687405077881281512036579249865377834993082451741746928548935237020294260912563833920024470626614384227345795698307721082371812145947212382955134786971425303364319593252695401571832842561963828025171103094258392178458609779783268168214220321673002162642029020739649559485698933269797320853073132972665063097834247501111712045738885047945479537065422446591122541834387774885882290046792044034756636746624419016011019911489871672361855222119417466264666365748009559190554764443657734571498765574307526658253992026593767278226214953807730105136742712404768470302777784073361811883728541516077171807381882578025220992543470598564308355114966151362432679572809454564069883598849582666502463342293353667544433297640212734316178906673793065490751096234343427319780734326749155332400612780759557424552192050179473020545299001997366713707079213894156093707271161321311095474585120504261131935185920844351047494725451146453401012408257074065416061060908172520404865267922192131762489906766373310337414790027341466229856190296268853016583534093420049838385073140796129189992774456399588492082984661713339637130804044091867306923997544594340580732180322297872724770174596798221998305457943433376837964750855766262910247503798146901083561221666086249057616655300599734222520939332435934120135877018280452527427860514527606979682391146711774536437634761724949200871888701403657807267390514450001291304492096283094531917214578274948064682195951775264053547284170146854610899838800228138395724287832410729499515224900750616818122719407726334372560834164278844943467856651458514810593412849379172171850174627837851502436601380713852567309220160751620425667573253927135654297890321018218833507634237595541772616852872882132230952513498820466200691294610184090009928535827718213268575552222519132230113032911600065086250781162800943365674775892687946089086720010187872995498374055087663701228969441549447745275509051405118617759927750281424121319671622445547558365891369291711323021609887924816005525781288503331350426492128329642341978499836805120
  | 6 => 64495473597036925594381364801886037032351087341524352657512964288078305136083157061569739677343731944470224227638398992076399124487821327407278433659031639130519510404850040455044045006230818966013505817777749160557816860531986552100889150203916620283277946749681960586811984114861976052576505588027520388572604303882890342680344062731626517243001980064987917366347534302599495451132810437953133902679300732033526886373734327263963951762081314384454760780921057702379370503456015165747540318796128145425587655600206302386758917531616803347647698122138587758346133573709318838734769892043926252593431797705310924303450660165598389381138200121329198774718123480681092721669783246973804172744072248012189089153064838292944096422400612366383239619357808849343371951941700810534383486654260085857567700070320584025611267899852957799158778659439875265369615984520215113794284900016158253582217116951273204875419728517192117842690744057452797376662132379226934912696685384556897020644477175510670136635446287740920271249579958575135261313807686120259760161037462012958852355028572724388906544427991014954680659492951916581259408913839881307477862987638928903815866759687799604731162330907253609678881998414756187357061733177346815482693795017317160054119363418147883376326794492931731795415989054754330259680888505003388165494077179896708449293797341350001508018408264878098740017303769057860946259432287489164567210055700106627876394340331233258782921897169331299315873801732839768319281095777313560793120307207974066591383035817188552296333232022338157646275154740771169378325720947039274603638839443301573109018669959154880151126511623661094869672916858808007606918054597665062717194023489472512524436312270895269371637935037931454774791083858906660541332184537428928883916842711855953786321860563440186841925911583662743020357986145064728047150122660363728312663051338449465165692714704509115242447104353006657235632232649550870756692926179943080119801308558340988386755564894993775786956840993341789595659109980508568931475734505213162539426845957842779385163491712320384587896477783288336717772173600731129980248369626694406217429997258181647433334639437559240570571120754684922884153354428465682000804782688167350566284571340635636585229802659795336124382266688067488691675806757976990982361934154867527451250663810508157485048829006252867323780862013665921537514455709126607423010026541769693869733381981623352513397171956547626411469037151128064035201685228631126990286089513316403635719213046294540404274243904818211304914459328625805528055013036612132560905303858164382061989317894468676844492438275443255955791972332367245410814475563743802376226326074213474088299890053341110350442060852830048687879803146578372879923560390163868343106502128369862953772121026094988923364928415101716708161307301644110419084445989962873634822457524801872095997552581776282038995097882206022419911249965930020214965502733777706872990718908092811771182131753419317134506941457443029797495010165542421362943808998563398190056122754331227378886951268196025687853829211942919658863877298254161574490329170983146250971510036254203155756822993981396157388116702778345486616084315152205009664531102975837361308097278324472577228016328438173631896546234740666706968234781534629746365695327415653957045778942816401469289731584695201792492496305212102118855425459772155085291548879593817834632914865954390219672474995790826056695781768120855454128632405526622144675795242102329915844754316996712168799319281403218383300593329517135403869812620187537433379248100263117153289591310158431894826461441003164273631492935119540386039664019998392652665581423277246668136546070485795766590988086384757359968148526715387357715159960261752712993631379196583689055719516259747659052728468310267807549108375089998447321281370167150833502523951543181273357055039774084957250833138224212546096794895278324362790714901680796521379249444977080416565281620624348490683269063816276545309092081454677309662917143294430993207349252538680370758453229017666353052219163086631258310783454077094358522815207916708003007511118471685011596342129748496607867810869385816154593115022604646632979658430145524503400859361252071890729227727602186572326180401316071345474157179207938824013304109603126933044301788468665727030956502734151489882009225609051060799584739142245551555798952845923062028491201180842285839329163809395045661315253689025368938987940358732891285046396919102450874762344350159220178644600902692101042456470831898271030003721462037961338462632341031404277253968006141513034855949392071892275538776878352878020329026449154257644631697738578072265831781599287907907941599662179391801785973635073203887607094460828492489132830959314857052366026196177003146368644145537412599214194111979948777287723501275443664770446088261896445624745899210110275725495571181832982241330705934504903384575317854522343704466680925532587137637983562667053046468444160
  | 7 => 15016522630359261667910349742017229328013744051923126135373712584394566979278614060387420392908093506579805218530446056294347887041005615006964289038216610048019172003625408392497998444058710996230332374726702912202604622879301602795555001402607004098873160655629190658952003726813318072378563201969213490647340457594593071998785567534772566999490451885829514596753608262788676806272739640143084858872235394141894133140350950034163159648693730977767352957931710031087955227592773457369987889340137688142752918678571336967724095160508767850006398545641044492948282362808208601826650815774132017018820162524992999662186928685130881803612613735405306930821903364714886844199308336667276242079942505155851425886290383125443441475113530559950407092232796069538349758531709528840087518070025987941746118542521203132630326841890126970402155436540246282192178076510499981364344374450715295142878914008068236148198062494936945612826302529345069296545277500523683576935392967155667395567775968973134099437162002523656975387594023738236051236173127907731321272656960802458643343988736692931464757329231894475182591626347465196235338102287736503684240109665720524591255831147910664459960824488864856313786921340078603904612420502412451602685302661669986800505281361305137829431402361319963314766820188375148561902346932386469660420893859229820978951704954327665268987554879446811771358312389993894776598626877521521464243917556972851850293920403170702259345744565673787520004060870004699418514663425639828651285201717779344458314965712956560070598237300614171879193578652711467199734267405928094780893219098937199099920465025174983134163035212920556125372670096291596950561823770551196566439099455977899098996874538080162800794864182179367822140781095356326743072380454987027503762181047892080738066458336454769519989528017456973431799695273890787145162605422707893271862961384611075887777941541663566345784580004417464134635446649013370888424933825739333723666441572466012276877761423949850571632853571417256159470881196448624110611952654727697747793158417377941988375966577965265468467162537936078973651000873285218010104853625044415583792449302123923924190195689990576242925850456375763688766831665336913410927179616327662196920807527381997750749647460714534587191777978607309461048652231027900756221301635561807110784956122047392237472589492256909025150691132852821942752225506538417528094375932596145990317770764685153999854154937907566763203123518437278907106184068681560762130142565908340246615589616832693601596008787695725389346169328792237882347242583994077141919703972069652451727080367026491447411433462684055482521082914283876655274359675659001459709773566344532769894334768346608001237917999710637623871002641689474409367901316609116457971327014128449573671259514499375270406168947395906987786448331020449315881690796337745679451579770912809027294912151248885954812584738342352123638845408996545229780978106891294934607731654210978445258367539483760143712862307654360106885019224637163005965404670064638378209843329159876662696625009138807954342549650295206857036489383744256960882061820047866773954160306132451431873250647365942087901936691151579939859034924168229833729242410663615768202393348415952603461411361505541503178794731649036575531591053242913963070411884545773969466500553895436326515343517534226522058521308382551660983856223059982239710574655728942923456636964774112130418698087721735720266661805260092830305051611634964956383634460180015661059488063035665550166277879022720216348617418723429720142586177599382081597026727360744547181351568268328371616173076823614337179768016183799519680554757032540823492751143153350784379270700238077546579294447594126057005367336656134116760788007142276953145829357796577272350166028304426323046886074109515990414198695225952481917069088452961233417039741332430310435215787966733294114634135978603195616254428177413191840329617298068376851004599704615509127943036955319689324905817519496067356147459280604466592712646766492021884726496829327170142988514051240889137832238494556390956944721882235636378810285899868955130438467841926078804031300758248642027082988047736521063659850564470122559377362351647762132022609501966251034796124218037603152765176684989345767863202343295754427759579731615750713104131580508396262684730473282948070400611931215238161675089218174445995518473121862241548378951610824049161210496489911457441153044160050363159182180016497017388457466767782616430877584655979412177618541205448395518077005007872244857722545514660131684470576341649787157377925333700740348665646007062894913336269476093937875059681074494892120556860211386807992309498348035731992008311087350133535555032450306420285184899772243164971338764161440309009872338240419456109140357119495203181441704579333884720980317348405530415248950908831680077081261022318675316095893396540959962672776375448109929096258700445332063085257908588359263861498747994813497344
  | 8 => 984122827103224572668172680692841141240708730186833994407851627930882341554003251061549982869624816047214114801611312745306383125119343985096411646408563756106984456429594764410748826029831683848951062510089202054109896565102988868604260196288246492781881714370093078120896249442653469129851045715669798913810420765916394048940303838923981877282440253082005429438878373573767701867565647626137974836961313869600581570417168695852621947441336539639868787984685334583140160618907276901472872416935204090471625598663452018343138210733811791096508536269327333721999526549979402282388867534299319182450736016885094885698071413946176933315768848540463518408502259616702444446354903367391828830374881144950819883778229921289233331638679928465744112040242353761187148954581254681822369419813662523333881189136944334758223430666732346933422790252697873345986659493324772616369169467035918998468791565693852425692792222368141070229680716520432834119489541639470292078169162340071453649445658560457189531037776194312555307795608848093285205177208530936264810360340806579199645853251089936939810837995249266926647581037605138923158069076807866869392629240044814834787307918170944126098692747304731008735608367201230503819132531046179103935136372334275129940403644546501051195084181748995322897142971966671264454276226710433466497429611778745525622201451706274407449135175192989663709672067622689452320394190698788828930050950010368714760806990027881886978182871892172117590398181327687584939110279340426841852376431134370793336076980345623394874133774675655708328267060396235959423928153433562769589609490329110668532487139409646847052353030820014534878395528823691993586696779126592992676475643942852029844241172144977519805082042727719154328962553166518613105770423902535334318035484180982118060787148867993888099023869495086387263061619059489609149330337391229544392627632412257060457620439350210042880547155712555686797631151512426436056502178059513154844985608497699894339273627229122808151813312829433513354004455821257941246410701145922843601589323670143770713145087507752282012016687465629245526094794649291919653908076255405273024173557904872440595396474693217415010641347410202512102230530044347522542901353141416115088268356102050515524001947845298942332224951425537217162159325079380596320400677445052604502583583582549877055696170156973493171316766315790120286415081462547553827729051418276654098874723784031909845870637832206294639978413204080342628364879775794667025902365409285224309968543568548493232412326026445037244010176635112245399585004559257763035320165775288926008089468542165736446854933708715470261024079225061985296695413622924686539181552661422102568246765620863198153975061601379660244831230688282073583718383615287613939740198849479502973633475187697060968797323038036787914331457405587353934292149784343741193017528406124029278114999485981481581509067978782646300173089322925594492315139889784398095619502444846868829955492082367790817337123185161740558224602309374690287773268973237553271876755406056945962740126604285019470001953367405376369509682861135618262568440398275300979402095549111766065401919518515530501852610033762407293936358786973807255192778050111224335671997171873699998904282424483479195606717247732400438128250580494453871279014603854216800666356141655769662250391715790762241666772277471130078202780179771546691785032352812275876276969457747976036734372314616873319798503242299706045423857963926764761231648759301559234881915318624700974844513937332796676593221604800380043138852672618945701569592119919639383582622188918420812372486776555508917278518425495571371725290409773821393101942471238370421102074957303235320803773795714758614660291388032943958514124634454185108091341522626969393461283245850828856931767128937428778977660099365764424789775576595272596173790216772435160046373554366939173470643305309939403070328067156693931604246325443396737737496071204589612296154056523480602413752428464650684079839093730308375427391287359549708410108910668250591606404689598009741198859245567284041357492299801057134570518768306472107106406965283269399652759935440756982564967563091973712431969285323118597987622929116502679079120265020507753054157730114472116020082647623582569046938723616463283373451970875821307896168579525543592293095683576101490827451178193475608383478387540572410701159046427007530565430406946302303945024646366301166460038179154849574120657816001915862541745999618123482506944015570586485580324250397027749125689841806365368805199163086344392194117966704482015969297757251197421152017512377829420172348086176336910273260962108268241204374944908118516321642656723194303103516545939783129106624842525241647335997616219711665360004673653547335992678731930380320988423514615786612633636952391573172355337034726079615802401666863470454834513085257830265587708223391330749092213767936390079062124450094947009001061657039897087884211845250975378603769856
  | 9 => 151944150049958767944066528182172064018826680977700209061021343813957241840457703423492929418717403393215385697480526083920694652156688207421110688140646528063083197576907583284489707928705845075449579938295281234371416668140078470990027551005120992982454912101368615477993780450066821626470182709211526690765383779117439547359858194145660891915504825209071840022191098001578278533389064514223543856588520382229225900244267646991712419911754761013201142391696052348127120533196529012275489090974101916158881279153011484278749556783600229597435010665329986903853687213336995889479231870099242982187599645662827632278418523432470246480737894816445024782314525946423017506018144388360723185172668007717497730290187561760717808301684887967508824138872738789427054176015401124921227041488977257697723090090584520899572618789750837937333292254562011024942099546460715601049119512153964884086575576001473143758293848781742659706486500790612566009385550890532845316040024062187363376808338040723973189895611486140522092065432143253602065808168651529747770728981483882427325271594460845785559851777566344607603365524098764453485401496485602416913534449027335719615864003092802694749334852159693896191829002596427173407167842140915672419916018495708699325742150896627827335640877493635012944655755518172843759777638227591295291856007462484958551456711550661576970783282821917589326575504402507218053602985427155622091612484790721868800079578496326738053021022383816083144040217371845508774238413665690589652933416771225824739151379224610192261131937341030557425036340716427916230962417467738591086347030364977028579123182565320321295300401298020723963198428219434229231941252057357498833590123795518890392464415534204452194234985867735994227740585780519165259521870883677668909395931834087035281560621403564979170481467920871143161897236521125960389174951427551442094251394762367717556394182108847490490570872598656791862846815436226525391066654379146925853429399871260298293380495569673444940893785190467763069185599025574870442552011700771692920768748083540103169812164969971764475218746385938209873539977335191664856300729717229884989663662931892273006188267380544260155938911390959237817796084563844718925682941862356235839786320138271677768632603099218680168374891696852497891808207697180523009770139251485425373901069384738550112439382846473408984750990370980618685397869925632548692013207966353639907711857118876834942007825626801720805916102746300075345944072999450762128381097710658465842523836746842721766723091901095679185264137902144735165701498798122449161026895940634319129332828188399895461706157397576584728280903794053096578722410762158159973751210131786815265328391463988968436960248917314787892100078549746260156144516343506401935106548669691548162217708591117595324204796657227142880509740073600081987061743470537290015864377981518782725178497925084563190079302889380100277708804427929018318016532107993152316306176320263462370588105145198162913344367681722786465049391527612913708584725141378530121050044208203373886437712814361954681638945259947327295893068151317625938261090910115846658019202802831683044749633896241902874654464972928263018110282890873547206958959619989976330049728878539183455969880813927249880538878890251562246176847332272997582336802147286127126205017902331704503194799501751168703795797562898862961209445046288912958237042283828695498383807007199630681078245728962362151975813550284246867407220793846049625177066331534741862727385898725556345256554445143770041082612429084648314507517957956996530941812161119704964978147293039792767958642457683573123722276274457928702947468996278693828085789847693534391703379927120337014073250161215022646061382765988819558718854870851025031267655391581556177218316437549311147692669252344629176874831198637216425867860829427089767259765774628647284720000544901398681199088106925200154847768061572461006773270294147738967390370484240637750893103167827000734819495374137360090850362900442902405242922697575127249063426408268426656297283933222781035846651768580028947987836726593575573050130477654668077688688605797248461663807329851855445120778927077530599115734399274729686814181756293154808518493421903929340932773407034837167521672911414360952028422747111099086979720982424501897827713678312371026377684489660511200735313208702827958093211335524678727236100454510758381777626817498212378006400200060001504792870831637688326727923006423061347461488123382853444506276131291587810373055879603994662138845978580471716789129183599376755702753016192181829672413499262946167563918494609236053788850525040017721801048064
  | 10 => 7030249892825324972379822766815048056051211386554059086163445552045114598657391681690708991585648111712892045106229479113991392885411833764210780161532944281474619936765067581498089377678485843599964022546435553863751876027695357007635809909873860748781365802161900503307137331389577755247129697947896248203213015823908661216969321357355241868651882208876862346955139423394469062976736918844205990698169958479328901841777041310892109177203622213522362529733217333928133082561561788881651438844608038044170060085909860579384684099706164638740106017767533232925353494700462541848268427667004381565666350659464507900412243969842307177142044436670571840081572338554250341295918146844633429449764876864969468187590387395448030655124160106778604440851862629561591098563989050192940579488372874131341325902276116221061976247261745918798984688057234168908740689971362732775528432233439809883391665678724214923278370057944788112924646169558990486056437359097941397971535010662005722985127492652284314005775031486778827322036909274522010254207731290953193553046406851336802628843423962990672587560567882064858329313613166250407305662680056008668182692358499590804535713616792471925239615527389014353534832110620637887196651133665428319533127452448226717813461951309172909269196863774897598366677691571162337686101414429763573983175939556059236724493796502240766989870195099604334829877487785638270231468436237434410412556679846577409836051070300151560127247802105371651711550465237200249298584741842456181127205470160318269214613182812448762443004407187487053510119887144787200000404727575449270625256335749254778527802062781611706148766983913224762424429628843932769947399204820007434598590146322595456396220208777883264207977432215661111995761599722566848163484289542431820749032038223559607533491945812439863570039597369080229406525611640398020477110329276513050053578572989691392338996963539922674999076707943570201993093489368964124971846191479131069942676288399996864211990794153506655885104006273890682266437028071620239523922880435235235802939695674388449786104798799251341665846907502460427755436409173649318910275510469066591066801052621002747216923269984782703615561929040603157018360409374428791215088875591472252970124965144771790578171656810540879952747645461230001566560278391606770059544737469182045473679900570907990549737132149849351055135510336251440787834760495215463725296842105976887139636283083537497247749097652089957609344260142433797159445803940961809496573932285502797343115113330143257222192859595724617987916523716148453649762017333227832577779691787791353197510029224037770289357951596493062542065492553726098620972910381382610952030358036878701130273427346749707384271179037141869149049105743458947659232751927753291823751256865099740664631322182384520125978701013145653258512561379604696784685381446001479841264237133270456965921516844696419295030863432865552676208735026882040795447594867349636221396707392375850163426578575849247546519140245396931884146781520995199539091373078671282494079764082461172720408587326267383266023592237866157355800209177825618217552668461844606277190913196304490318537282190313374727839224334732391525253913419301494572288838319312564252107462114699969563378849025929942403971522841390977170423176215889243317421725273839767300233671014344975852255945276097372868658201657472376948233521153765336955476584909775927802280875249109704111488613267227541388832727473789861382703586990691823111007102496669480183039930335865996809667257152842033308842509224371550724076767993393122819807370224832580874348748009370521691532562166876593012048613748646691878195980069013879764721518135880082187282224684642867221821413772710481819645379413733603684014196055358669097109470118762225263214078838249530296358073371253881833953482734537786659991271431901521179320032965226815103517370887605293383160422166811711007498292216159930135563086049626037216634649030531111666970157213318506333835533689972843839634616255547320835709581477224821430389728861223510886304526720778422141589634062465583270782145917524327090727727875924969672182323319417447446710150720963958477941513874137603456006436577405943357506972732454126147908868369156029806480552820629750274984497276380793655367635988956540444694344314253234704597103590685986178674541075965894836338303273823795092599357117987142432077750604226326238414692809663109494633920669063472354666218860215508673429931369124595238779978150212059554807015775004783668490220408438632416505071790256361648792926016812385709427738248074014058881795747559127127923014735426361706898128642282846463447685835347767426715222518028450931386587137764494264345791290210560070833452917607960878980628215415882580925285506239707813834799093162973069088208113612571829522440151628921456692512686016177301079528348402447244947920621928448
  | 11 => 18153861928668697587368153788117068115656425736416631824518271097610349772881413166499097570292678575710810311124047524690433742105907257330193176553360824463158236891521698099524258475327968478441017779279055094507267275958918627107968688464897674960612891740091463745955227368543717746568318041349975654607148072596468592411939144936219284310804451249406759150948305228055100902922847128737865303502118152957561663956392629439955425389294094999860291109026800269386796469753957784539851200271543163783509662234417923439574823026782522125457407134781805774172107138289081661012078681593422719112160639865306107341866888794688960326563881636551963058948891873611311873399207299616628861230420720650886755039941560249125989324488249689946301486050212124263843657223102342904603010463986058326556064899786040803834730318084858548241361472354695193843539501840326525580925293385538522340971555986628849849382405216155297826744943706930332717677687638365133668491379347979825430276578893623018710593384858691807219705715226644430363914067986448833006402692609246528064734007303779242056063656899361874959437226185257063268906349697168214601175499779172053751206383707091413173348838612603240126248959075706999655037530621879961151259796172163872920839943664670921944888062243180432795588237008569553424045140102980032196583378481393937418952070502100041687657227551166189218571949519168052322958864001860737393230894167597306406073035619218406792602505540448131430372902560011784110846876579639850541446031032583431968817162653877643565788902896403075230887967353684442805043576532258218194126505768247437088989113709005767524216032739169560580626792924487177013710755271607834601533983439605131027596123442244125816371532303895875947701798918093561135496988700420966552019597218059088803346351290812054154430240835486780954336760878591696394070632776867161409743006262596216624776171393638973431855509820405852356832506572304109598715834499850031864046600610618330090143941534191153656945659742729454482430922965005400749447662633488081429114053965139772498785343682105426728173390580897166725054734667156011828741374737976715888981891664228145584622404035343343746726981186439169520671754089244372704878307239319679652508323944441809533221414837813791227305517742426088984858881172507936935777799532175633857556273525678971911116411525465686056253734024383975438554972527720681651809985445960833778155980345564179773255582463659476758341715176020624874228536963922439935426863423922660751135999590059570559343837885258107074153623251624978790205309017837480817799974491470521321248266235365252199134332388969693034567009442019288596439609634353531503180759235440105372198958124550836073251199246763949608069444700287851109491439496150569300660206977449996286246086970638231389977337558042802035304969030227532819371691474889931633104094819951175974137494384974273381027827724721665629943570687425904994589163831646839336192592737399091706833587053082318163487249969147805923556718912483048067282897744819154332087818294089403489147685060439545765468273251581139801270807153464507873341869586857424534221458056747410598346884572453225991475001938784775921704234952357772770714693537636640269088416162738885943211739360410739720725066076144438271126257943495469196999967712871543027665541087847018165451248305096455772176729956377037983174542697206882263811008990328793844714474582817004202111267467726289210069090138718888061483479431625134156362619914780257108504629118026766348593193571138679078638681812120840212233378035646550320653086853761323571882953200447786884731512926213774042753517258567505574993184205471809711324353375593800545152022317170117167557677903018662649871688616390618927278311315447780287193430866151913026217416179343155993305760734480502934781457375075123711419034189943699840710588472336643944679663724910360992564461358170371415212268604339070819493537704716446855316158457195302216825608194704742809172056859502674931889355735862580358424412307970041749760613330198212557516369221915128372237832455447938976844949046924602108374831951815570612146835793464709512841365381614528793075334930926722722853441811898143284460889622058669483473243474338804904975540632724391776388567119442866678281589610059397211440424278632718184562373352439797243983159924725120749759802511384147048592644641007844318379675897231146340788198474075377867036652424219173107856839671120745824785073916051912940277779297229194486249865001159787380144750571622725566625902616684887722988877160701001742321116344878258980921317697955439230912976586788507766761290918801627692715803886945300987744068294814488528679052391316694376880803062411413235217527101203039688199842925714842636395462832443391286276637454572566621060776789401176836388287665403659180355033354950565742066195627558155886691462514594057878185919382447906753657716706999737046956499367321845077236366042160478453020039218588149852927900506522168641364909096960
  | 12 => 70913523158862099950656850733042297591868331335399705681818116520096410094691777239842529145420283206852072489636078944198457654556191572576058268158406865736516725899392148904914280561332061095953686788313865055138714599907291487852146191070271784109789037652390748977509239534625481066330748417072871035478734703165453957402152927379330900743839638691301539230204286818032898610822587581878585985340516686752131511909935936308464081517472729995497397296762879102826578672011025340784633492506860939889423293150007151344939521621468950889856106321481834231725742469294508698303395552877418319255146410287622723881549097834547592265802683835233209029183333431903724799416899151608678682000383490095210745548228283535827897279435830319657127909182907989829256473291001808582926591654100424684582959637100099798615562452665600136832116809113285099401222855781284393207966879933765925532764065876774687409951773580003606870628941396498759336365756688279240911090176673304398455638263785056856924906720827831878950387247268820740977095329214600775271583889628032697368315007803886428300595891025853628230808211633036486404466855709495642973146634798129482407303291491697166568146751493034178940762480812106634819345831100703222434691239676482405582025601712617125222557092520086319549835423768867373705650817826095499066771073758433463769437239404176330281569964506169572231494025999927369536255182189011625490810149879938688877187045836863216099695486299026885422028023790037219972436898779173839563716101729264942636296860351912627138963240804363820716066094610806494243409960929164699699207599953220414648507588211272427796137944154319173920124517966096648372989001612792603875608604714677091029720962719667424852498316371769700150554539383856981938006939615810166482953899770766837320619864775030151061058389202649484624522120563909875302536747609608848573514686884173607813704809060881776094713449046683642732450254398999488006351838440153964961896793436466528511634929242449957633727661814886589509034799041144536830433852725469885677795452809013203746224816274023116412178271567823221277896286074406106697129722455287740171311657547246554225129148079987383075980521171900934649904628436792122442842829894634072538636736884094245880475979385744759463970534810635924868245689063808942606535787091471152934422994054063267272795043450579760285971137397429708311393189543545348406077419145866174547836115275500570028882117504635139930749625361906039699919640302857280427105435077228362981906507406869356275450841668361322760012433200753240197622328624960817036817045772486205161202186947813968113689260222289689989134105183961874065359374434458149484715501804547500071053579821029192412157273466146287276613231966754963239315325611027682946101024137673213031383446974868524216200710446490971820494169659324747365333938556367735040132173812328807440501273433902714606819015515978331858173563650124228457480767508698640947584079120768088656552512809850300467079626967858727015974885341205083277627419689806000209695595449843828720012976784208986961043341676692551230101307080404840317053665632938198119707262055354719206231066022158394048664926125377695924103026507660855702659818921927447879550034808363981875825637080860461105774931913601441586578752559299027109243722253644898512670153175945961296423866459220817014604938089492145413519691351815169334690424782305310036594337048008070675989064978696438344749688227081611214335663960847728992325895572957578448919952379194356627755383735252722588326091262359747916592084794323412988340711876371331727732246234310519738478175467180845010235043451354519974254197526567501378636757937618840419316248379120535748436826541133209418782118616124708659816818659000164914434397850449277591089094374707604431324174085251931733296721853526929174485842422442926714030941486292117826725178842710738457787991362571266191173723707293476302479756847544108232908996144801914836355026072597840280403115607144490920472692189114300749622337279962890910059584125322848180624122120066694420360267978624591623177435960219399016492578522683756000575549067180594738672078708045580294765360569013884900459055367260130487222997066430751068477560884839354662184851847471966413525744260037333331961657273621753667590829331095907895819221976015582913046749788092748745675729670736771842976806651215694789670348633158134707563024435951019036174874386420901313958418370006601984543411625668294534702935735562064533072197789035276520479862895785888585577858413715898641632379804631134179367457413095028274326427004466400730096705710062647538000432073307962543480552749838272842811616648132529520513442057528133241565840963531346072000607048811248956704304268807209474104617454200208405956089152517314307090768262582718405037171989183255921573096107212808395526706756040174026722690831336847854399454966513691385880459770292384610433871493325930001166591107757289946465607682237495029432945641038609923566469376
  | 13 => 1134616370541793599272017288422626549108339359186550402169252308440004072988506938164297962769217679001507928049263929046386456217382417716748006440966925908561163221316191988468794112436859342457904784283195673103906927434041731223906767733716600222577155022931499306357830902341759936306430213999474550908414555810742474593306938075533593114743494807995576579662694614480159765318331958573118736753414661311539247346479002427318593289679573362266240093370365950009869133785490327990765434725385810021912683349111892544658200051792707304044994803172313048683156908132035121509157394280616622974097570929544545982584954129593827758737895485218597008937879268831933549883475786243071306827378003093482341604403974377371151303860066685985703680604402109336437266044267165520539916254045990057972411438334180744303000764640548850144688005632514848299511328017224789639994224311990820474951982177348488096619158767939912919436094696397665640295564080349322753053210604843348961122749616758757554093311343965175528415695663660358592514946104669683981185518024275050842430405195390041222151475053924814974494562443550793066282884966271098339858083327882649384630313272705948305233954860039958738376799901999918839914394609715842647503147290673925241916922952678630362724327062936648019908187561941921119488083964475597926992749964517327825381711036544812575775452373642276875777924652335745812629594726782578706212466860097573935451915930721469845266453507920743390445061156437327822850300432241414090297807492946056325182418216073315029284803941101120985481777557240843206426063496523728972398213932958379471823387876574017337755567982835329999382104979932110789407587432230824583816868779606236952077515294200298405186134401818992573938643501145133837617487110415192224575870032178907174671247591690103267386831805387897374406344845112490313398817199110365102457802189361544634178549689787284658715642283618680418434554488333412858138149251630092652898976429992855179357509403843800784351218323905193666354236017868245258910580714911080794859730114217885153123630524710226719016756657545940433415337541672688045127357101920492956380807072865155131186913229768359727243476293282328669808238507409429640693361409979909364765211814758721202021913639652603223842721290408824019699982882739532837399330476699047002662580276041287571591723810393997008893998606585906313100306427083711538342247920585705793628719153714601471202229738536750848370651073670274141258429623864241848886890082590798020255555974435351148867399289732557922576516920306778621901482723861079058097295626037021983809564307984719694969263737441098840682482333859271703251314625696103594587417228266644633467044161748232128600476072568288590678346574904496998730099091765886791919852101514924556351666465930665216228469677185901619663301921727824324098391497232109030105785217716575041498732222656479505107061026089303634146854858871089057089274541876547064545713672033979688127430035953835452161485004948990654852096326090872295080056178154666052739072679133120267984597206938537354969306731306876724613164596655510046898855044966515559728891742372201829338491862573351476146832791250507362555021840879260940662328827671465259733146624250040996877807665774637617341127739249350476418111667457037700710936128678792089385984779939589329482609995993392341224232380696025374636013891512546757775488511122297127444531824684222956652212439206202903584108726260891083558684695253070723392062235625962575613192220192639490358584311144496526165751320952865168699688143493670345344060829385730885166427990728340667536729096085197535060835947736300858551843005185139328736479081345450581809228491186400366499579123335970385053702496218103902987354199395783072947907961967068829896595040931249419328139695808997527270211786339190042412630057952324787955172392538110176535279316350294993868402066426144068721297874033202534095372313285149504537505266067263920917227475567739341284354520645570701490365561879012538050730221606729814853967232978650957766596693983223993237422257360891308059820021010231095977687082636080736340974590751472356399234327020902241624903767040173641893226788880506481404856635202002791103925741385993392970045043970667590873083425084335835328343161110495736205317718393868609975146415156226225356174808922075678190224717748451649462740779717284758670439017950293383026718745398015880393592937472546520096054641806253586840446570399756573384914110073715178446606925331697614592892943736602569629048016699788454017730207876348049028703731350974407998688813914236202000426959471456222642653701541674076020450552240398516471398847837507634078205721379865030335303181104791907921736189504291437849838245950724238961285206157652361892358566405897886183805091460377894288234359976550486650333685984371608166678771750529773933461698044612843106076770884695091912431871044948044951127661530233657033091127921691423092513847381517109368707367580638453684380893184
  | 14 => 66043364963365811808646517557131301921127513437720937122640003757483147405888035762076587740750168772236040525269996265727853563735895723780722112569560455831250502501976579409820586682389950044537949714297487940345947496624582634174356860791921740540229208547379560883183035176030383901151215971651179735802314116886823895486270396600619500413216774036122552675077153546475857408680705118002461952201423268528110875036212119901889884439996580233217618101217847930283420040019689789351426409558975398717471850112888083397471697198547167501607774981927631984344196225151985887418468823105960288817809960020269316510325919569009673368377741458887221900753630446255508059335312349333874070542231269430195333730509389923657282045880864092468416939235623876584481830056766309319396745770206271818175404198207550761521062571933640215110627227210585754590912318793878355319115276014655013445421147252130448326375116286469809718834354058678609020210298190728000638421639843928927611900690876797382763692962721629725748614094301820116168592031012596764776039605886459696402882840590499221963325098266193420994588176237267954017996144088601986910063199423192506714482518515363330873763502427237172348504060469692675485111659546768131149647454302840815078303373485933060729152709118590377104094250031036173076168945356598263255206927587795929338145424539713338618977271126534844202664406274831819113240844911988116435859976167680096889669918732237624318811804144715839061048744777465730505923992949372540792664407830866784973478364128291864472357816369787931770085830847130993675053996686109223065291127800719599883472685711120402720314810187237662229160078421355068484060502388860607820337625434906902092854855054527554860159015729117635226767293768686258608665115750151178931122076997237093223694526566596105467098120950504079681580448445211997928689854911693114348691780548645957433939956125401181624909448698914042280071668635769020323273854908960908294027030393142474363451151160036030636433281472623801380448016329499004498707570557962084367352274339181459758292484992766306111762586783912439815387229698739505112191968468139293187244151902148532691046503843204679265372622838292695069738475723030284654779509187701046503021123416336120852076297829426593008624804177514363499605780600289709824245646604959323920250946303490789855299017417583728970536263794052492734278653208357668108730921378569559091249385765484603232496770294249980593829155485493666355517799480449418966836902505153090190320024259922689602391146022864373738162003867564293999537088992768149409541565385763766033543124254244735402234497760884810951965427219539697752401567690250207933130255718427844528699779792748858271857697248765695673902697182926932413738479289924711209434563708007670548837209332984764143085257591179615726528922237314958861865464232388903927646890823821010077091997318713089051933872811290417928946271298263849199994302421011733549837986433671171050597337763691294047543457010715154106215289451741553231855358804094695335535194945238781318200524891126495628080220723089242867296733258988314049552209443772795578122617701227048979804151000381850477310778226059970492623169287331740797532877057484989956425279381619761899880894094514162607595325482841965137281561700129008253424804994118796012574278699341766879999313710063619709836346878744311450182824340745509719341564936461162688169315299559175817139181228433885934087191402974006609081101872717201132392901358906999041684066718618650965305332357674008424024122414275296997759656154757541860599378545348840178281530975095814612416604874490939906657114284127755981443615117047094482442332204379698559981928767801992777286738539126680941027240530044836968241489345553457509137376731166778912337263804995108146291551056520367650675651852424336987260001920079420284764192212648167448138164025094539742909228530131685418206749991150320788225889191693716552164249526431501528296527670240274481257781098141614185053184297016067861022555033363243623863261200609219153242822737297097843405930153909754448460310617618299700661726166304108358223534238745048296074349886431471249751113134763473635481424236176605613613990051295664938170508210439288146303684166892542837766628494973754454661356061010630649301239048474267592730657626455584700136080591233134466415085758080852638027818661815570576782866392106887805587694057188960658052491260827255404710468883537221986465220369064955076256789131061000747204733207789819616413933253055947199608418014450137298336490568627601298020955279675474782119020070093812416305325474613374125977126961299724831507679227052589795645283739066870991933636683226446112303517035101133227779372750260414708656549712073257894302004640496716347490609175300392609870555264686332319095474345778750219385309654347099635384081628386736559605980083023033731561274372064567126074545467125787886200312654874857178130504408066271776977537015434037593300538898969001984
  | 15 => 1007741774953701962412208825029469328630485739711318010273640067001223517751299329087027182458495811632347253556849984251193736320122208240738725525922369286253552083383905038756606797854547644261325888010331342903408534082578339676988920393647362683518721491688770190361680400630208115907995154436356480330817642730413313604108708816853867469699692804904676422259552738416761572532111631417771222334516038441454770083313704818113450834674475369839576313293836849763717359406612481333452314947374349854846418205203303566865168691649641072453651799129222647695215240119294729143604250140176988838063121843020006790837892538966734845792002495088765940538678971280755734230917752260576612717904349875973846755287482134222004182376017660548341432960186251162167619049303383411283696800131565345011296476898132812074483203435501761859813413705965414835846918230008462182443344860095513786962690630100975158891228764579832484778331897420741390624946920569484218247705607177863140076289678480237948865478218892649529390337773040092047711715991244205632078074184203005948866323272200817728107199614299121813220546457622555300120065642616844698021613918420171653942849277550718194218406162795690468158307925039146473765564859495089518693515583440233417306647469677567106262268027977760691030048032351775361418238824283833322452592236200683143414107377923034516975103289485650706135968813422325318308300762577549298603364455749661421062877783610187790130352117185682942979557402351676388012390644314517891164203607778623509658733626914782398570618561832142241437097806738111634394670596359864005712567465603657439737008251919326900717350866784052978411156775256690793193183600812806385756018498900583302882210358702103937672640910535578637344658868910765030395660240213073160612252058736179330233922845972828205149765625784776123611889052514422530925975312830506111304325657317742623576415943989511713929607348855820604148074107497051513667383534688147114902078330832402365580773267611660024192548586595000223866882338594451073051226263816244857847304736113911845688155942599446530163162805565342618020661972629004783534905137346369317507040385192726504003825181793355625344737943347585514540087390782300434074237666438854718406745994762793452093704315092625237455348666966917118916492633996219645369397471276126056578800433258451653956976403110630809528158778585752397856365132937516740882538322279145801039975078259505112030744823738486343265049994067190231535622797547033821673192265709142944525964838103081076625281755343084496389542141481756654089194363458764248570407509523957525144996272920005241876974770740648696381485617927360079030205503174832684326128613547615974213626458900609024383777288666538398938420389280740114593972972638377216921619391513158413804945555118991509001174824371036556973238654890559013623762318260190041992548450973687272120529182721664666737492075613419410865660310347993822615946903943226563330692268281035030745146278058115332469638868287575963918240519203891725207053428762568094457904890468984661454420998395537932941589414042085657266827404440929854987361960368908054423379711086087744151306993478570541410304136923913315985529758062232214138745560577506278632095491903754176942835252467578805942317000875233023584421964165157868939933622469857765606150135424203041178723098682311336608431894636944843232601864402972518654133565915453554349579207894194092010741169940032565428226590199479788561230856858211656267525993749541374214682373558928621976640072245089532136535438161815483441876732196059499674436241104753664723072857353831949320360959687996138028259552950159155779008238885108065145350166401521289956619867936255495811501057377022853188554376147312648619969826949689092345683241995025420789062757169186962697551516092368084343249236573083322476617116408922816749066304933702180468214340270790552777387006735243801026508275803363441749852735393559134542097609023401276330543976089885089583735952025943453073982482734137228535986200533149684148860600223434840089929903465598674983896238679091463100649172240447028193744973782971645082077695889365043809521438240511597693704351220306221862761596043198140005823916696962550270045360686786514292035306765211014052517550854349026485815608321366377230806739366382790705445688301276914526180891792365278236606426725661934753471492028602667405893136500110668912908225940216800526870501848242844784586900177059783654347391261916129055238890443060641159916422195598663438261533189275152356427449366800729042984478828096959943059013282823860878584138889464153279203262128504948533238953220905119354523030901692496147963417272122522049280568627713696223831088464159444411681078921213488304030680389391159955839020614405367942803779024174865627830790692680328955897731388977729187256380824714934805726774876130821501496663758404975222669155957938837998959686983531226754171037569462376163554084695365414558047274794715841716758190751744
  | 16 => 1485375069467709809978800941274932849931287355518767912690015589477359227010593022556292170855823447387440035757368932190327177649812562344626591088388003552216360277040464702649866960337305941028563148039444777305808229785508704785613849359022527730671772064860180945309923607763450039180731467251236567958288683241118484525702378907603535158589853807275081185282692114755939711163733723207165935733625647707720277437912594585258017910367544055458921159235624811719199548854054742488401364521251167573703848202475499020200432616405402749202491799035829773791206453182329429759518092851083870903836889933819932881258626297195227799479852889324358659003360268944825488708091158851443555527673636325898871344673926284601156814621010285439965277285873968231727065713675173507878033756404744482000756724721220603452253597684115718537538315273496894162106524590610604598128201405455093987228816441508910027793197551880934874365939331638177402108503340061467264984752117770012616003688590352639799472305259350735531571541259688794583945102099215334325135292040651656284501538216964686487532579399513487728108736557149082046738481059709167521350347880588773243991365086076310676899533201886170330409195239241309591404541591987330814873085427277662809335943485980127614502980635902788810417722681629456863363576567297651494206941952411584140053444118548007538085730687940664499838441733990738806523960279830000409388035267881440370775812882571690134570185797961248414287969125058739259705284306986550523058319667475328858536092283795454808180285160364771276166881417774436491398930242087616535169883065635574378996638302176019540838700864653668242033267304035932057741630996778594092995187464661072201260799020126603059450806529323786118753873760609648422496627169049814070086917403030894052155635984987866949365270214659354611231918385904566546697752104772481827201929664675263261643426158668757210506066206611710266947654195726384572331531358062081701538063216319446940732334469298966138235011168078645809233884337463239155143223767625526754444707696299689995494888220550701797455838966312858414215704228491770119613036267190642419597920424075010105907656378281717286593936467862939151636460145195986591511608369833025002655965414083614476371164550147489218832526757607315020965958861684084209909812154330301481431766940931589517118376855468793390254057747045889335230627119875677824031463314659512838686924798863397392632278485487721200912181516633237779667358739548796879303063787826724864068400520121338025127018620619411720047077203343938083532805228099267008801021105831244852344641933896471401898832371225433627060814109767443392313153572315839183174348523111623554695972138524411378398360010049321607899343233559340606327661124558072770262344172507388836403762783168380613922630059952687268926408088642497516127569111935898813954801050389302946717551861461291510136385800676248321039296864897129937971361962655394538768947799906016822453171825886122681865998087891741129082451034147946351281791613456991933908950293926305857215167175235224858414028311222760317795790545078337561934450292526159168636627979140631697867774540292686838161532550591795980800283568048205397919058928782985866317507161070103086505895991503394037838562254862956963280569951070243730785599317734944154997452942290612209771613129715972146519923580361992167546740078816058308917319516320580841979408640583493002142989980064145106386333375552136035297646379385399650260924925875137071088939529198413485869837987774978932729907469777818628677489171248455134253060868938220936091547083301492364271412402722219464151331547966680500966921379422360840842578273697544068360091550620848879307555637713672644076295634997184507366994578140618904830801638553423657501455814345245610332160222904418669552528337804313305340363021983572083706158016140262323815804581051138539154925480733224596073835401665782668942228860800202277766763840478117325904221100712741185273761082958182524080404427872648314071136677187829678701333460461093052882895528972081984459702343008320948712317525429410681514690610782179001223075747690406774391070166548005156766286404741976869286398874575908517808692586949783903249109649234611415078077817135447005542290552948955995708680197347924151672616982070751385083570004260710951157789054515904216049338211683594473154449242573698206982048285851882038943510639081126040889776300065742079022741481449855201878438484005355963297681469977804949946368
  | 17 => 2313284827013243103186074624473136618212998487450156093529859582953194086330516300557847280791159072881004892121487589809129035152727631572205363023722458496152048742539948402953679028934997447588873586690716755630824320180607809412491406735273037070734232172982345884062832430548730877669463319493824458465254429200334052916015160902724594129033265126241409919706764368423388861577355353804863473063345392124020805577261345417749316118010882899959382863321187854629829457001405337582429766110219538664796043657522434678436331221741316767955719920804492548156183297942091545264523543799868787913359681561499937697346420232222757192262627019848978006042826976809232862378719311439750437147869371615838203123112627168079547695833558352711368585579531823460650865828804541224787414265308460609532793656796893132407628551478670296958732986611282750365190113508350981386353855201749521720880648587468928616479574050450755297088710807830309888943054689178734782175129118046716026386207254786204293002378572173834008181962306284998852675325739364555341538307322480352973368546848482383717149727822195724546739176106808332083950322873649240394957575322347495144258774426268922023924451339680734041855640191063315766967698368633201377720595148300199660928619692242452406892498645139523976293933539824069612018223116618142949825312530929035760302889744927975937843868047791043436020459538307151568783130317455278879986904283458172953943075502997989586505140149995920473112037446435636878518995879214168256433815657109444867860443904335256856778444814504778661784746204543719477272370291372644173357870009334868427282104391116719675657559643045055704194601004275562554843343663919019230114097959851455461031882745293986780506888414532146636723048267745631049598699078570016351151745594344826984972341419050284705569787064289702577178455518014413444635510746251955175697033422904624851451350073091909151950844593336009365007015168461566283760912182226122462695768718292652175020485403367356258536946781149310373408666295864773278493267786653333056153113671521831116772399636063071792918942214104218914035328870882961085264658697889048149182656509638984367872726171436092936102236478256248116813340153615828337168780859275308701323546804349043953117961254851970888819690899407633268734989012576749078215540514576403911900265484844168559836754861573218901608672545696746234780510100052271012079608686619701902887509610125446491296926707685086547443071564523565029629820433231209358278639370386990474332730805264836256092525017216478237126474197813453330818054696511892174266241396712687185981670604598581392973226243359803212624932983562272400033330604847552057903551738084726124604325426405377820372426255418926377848617546742102776537399415856277983711140199304760333545545298584206440533692357313186491878409064361853273165535228573240977903372503261532622789127300088487487238394029810422666385466970778336148869797968122809965235033171451027255494057767759469747208675743998381104063313355458715253066406383050466794255653884226923582202609552492995730625519084420794602011619128969866521215668871431428816786102901994284618381929531556184562344177001848362456728022364312896701657332998088449798623649239848635850443879850211960689253409354141070428939497824128540409413248941619307160957044656297976070072968289642734735308612199416414561168159076602970810515319972166923596436692918552639341425190259499891373857578951590300332795233974744051372588413037821050555973465549961248832197533178672850435262484488717885484939482648697109199057387457059187046459342100505258706129021446928972057457054317373632696876357890528763722029629968976943842761148525554565389355924226320123684719675127689209163506004056166321595800719688798985696192576369879973103627496033881341790641946468276859871714873550571386851847444730217219120187897660251579381851322111863198934289986298731858210020835153398424209213245005169603756702476876934946735013303607219989156235124545674222487994158862259473376515656482207921178852428755352280722138852773996041319827325597320393471877292164029939195389026310673935871607697175174546106101592478380042839037857080101100734533564554078253197525858884779492356189429375699321634366907519921382200422584803131392
  | 18 => 144256098564356137219951220436871748849459542994107319340610992241676333070088221244364534794145594610401699401421570292451166663950728591498796048101521339455784873370002013870682709036931722449217789930493324214239257934695621898967552849266305149205444854968188524854984062979600310066455078719804848638705684479747069839312529031330749062545186584530047296280160398003364168717028066604408694693131008515429821765925186812524790498619554596395924707433717174765284152591141881976357035379530578307196429931342000085576312110142376852958018576818683190003190314413160854078947606041038355047822423310093649333392609602700711269450293980649493372841099810813716855826828516200425762727095559892531961205540661152183052504380350598664238337113869569597665351192633683614497864492932002311624124702489776438774969147421471252111880139157901062635901973906921609547995155625268868848532103025742150705972321911704163932552086991279006553741357118402533242014113180452372957220472624202645706683636222967117937295994459423514299149799212836960474828301244027670681751523894655688364013469821587390643197128523194385307678718127939309288012681411801930077313221487142878597483482018186896761043592508676278420436197332475652908888260648856186856215137808423945038952778467754522246441063312855325406109810099322748216587064311457501090867035210932447180497796772328894683819272860967071431698859022537477374170428592606940518495006937572051736426782644538766651786621022684725401018017772973454409742712187891407790691974702616924108290971194812082902476058579265122735005740750549373840761432332140580869258439519713233411461292081723442208465905982603994133867713471217323112223066363878272328847602785548761318103174702704953876701194144509071227463490401690366974721480252926284869663975527378609747339690688950671217437186504900644560170618224632554485611481782034665066377318944117106858533099335388467833111797430863925707644410257790402928016346385133248730012464225073260758926503866422262179713414045416557972999380732927175614374833159663849500467162949513674807079464976407472926908032843788383829341682472329827640339972713757392944605888445254724924428229582564965179054857126296816960877580168631639700917164616451286780663802567347171108185893406094306674250010311335327735439893388789262809100889162624008593706109750499125146250338006755173269580110729469876203961568122579259683283207894872161855591095549059677203541193689291968257584730925900969096891606091095138223408902640889230949644112517087198995573311163051495757562350833131353723955482035144785564257512553597517533617190237695866649436999015130601080766412109713495567940665943370223721468950792950765751603134190626661148726207923171751629109809428786318543272707815327553113744915117689039159798399772510873723153697191884713294179659685505039051822665758070007177638420098563575828612461660517027958161648002859050154989595087341733727059666329833570554551645979938724028127722971238363071073146500838047616383888999337642967609603556425015172095982403918050784469466803655790207891578849971492601074633509226855266399152640418493205400233947216518626076372643660706444931260984932053552045242427075833152651318307711752300671010539898704276451928892450631525438985539488647193953751445930513485605673204873567704794460986556244812873870508751296383939386347171602719571551040948774770194370814041888578483606940931630104402697938472718892832183744834997034778886894924967877350477899100576054662972415178033284272419073102514407818091823216258464040972070552980668674599662333633579296333738562450849321762385529555506504355453042774733334467685909164500315867570920923569785279511950434094177772182735119313595750459625891730653246447054632967323723092728724111472874037177553720051117413972428076336075885597268897078129904581991607808748070602785082663701927248360028382792779218221581467648
  | 19 => 594865747678615882542879663314003565381722343548255118736337410616630679090241843452244297736306019957557718742419654629448833690654343713137262349170782503040435817183002448761071625809765723422976172854741067923518323732415492392357140483922807069238022169202443061452643427656618079347999942895053178509060407681660390482161856378582145306703437601208682661975133940044533758686135305417823772877890396715811106725951908929815345155671925328769680324822596641589145883829482702642556778067184896640862944007954207337644916269031709617444299949490311557012560837236025936219660661599201471352670683475637369507296908449144497222586700182308964188569037205672895924286797538585218822095871944822442688842369161120304119539530699737837667369892008245871310742614507423836167988948579198667113174867405720826538879125494463015447394802338076552128630070903411513794001720975727663850799035640794798584706982804219752491585627531141013313100024021074904100001030496716840618811928940313739863536438741419219352524017082316668506692702999020350954331193650802509094131286861883139620399465858854403950870132703965488209824438934802008758845969343994044004472125629413484844182097066972890078922182473026356827727453163593714265947550139347559661748404351815218096963796346172410406417148682239343431032084521229277568266027525254094945933423431899958823773645685786750350507598779548726520016515760341759108247097818348038874055299142450671805734607137060905247538989637778322582491925031025533258542323684732018320284669732418586091676478436956021320001805809394639097855026047281380653351775920165055322550997717583813344334813881910302171240178953207677106366473378036503453544435248062525034078329626380648832032749173746330899412031156105204637292282793632423208825080061587937017363130978644540733098825776915372212354849317376813885178113563072526274562614724020074557397840679937984256404287622135935727727042447493077510397403490469607829027659582820840552983227079975738454291564860751649408292571036530740444010884909169208564698439185729787923026291571464223624851849274062647887960468225011325713624974790354101983041423775460945576066660524005986941818288912766662994426078162719667510657656067040695225510627681853951747958481562962100583938595054467627957269744108448558971634686804319537236396375558357563553198212540676776568606776445269901301489322659897550488216469545962330114439456450327105059143649149353691079858592284770257701514586653646227196440158404919528345457078922675767524720088764416633289816707428907794789491111904265680754619322357782281967343281760954607157018964997645540504463967824263389977972670866605261295879007330704706961657928640624152100904870124003052979426163718727642776976939885112097152885502232025158733233215806358393956419287552706240387523658591402242888678046033929882498130312319336221459744975406388495493464185779473695006690362301294024932301959409397958606405666807984391149779888578307019534038159999223039355057024760780757788334108665763603878015074190510078255204095827287905709033256485033635210613737963228429215162791416155324667626856667377437255708934357658557727582234833639539098406641662645970001845553131720274229828887797847657402127300811287349474487871111986049314314152109582185751414207176398660126407196271912308412440887843827927129024702719469609142360878858787823056440989592448334925342748397466447738476630157752383466896785732181498393457369649899500877780477401640914305553022581080874607002856873706986743916312878966541751667296012183013083609720763275632070320421528627481563429160114106365997055979828513080673674105562372080803134576267484553230631518576096835626054051481777632490030391329955881746888340998508629564813119527430939106759003357433249553276069969643231738099807382328569749877721933995792299430789983987517501447328495830663735437034860103370044856133154592890117437985461721028661575868547460987739907060812989659029785625311357613124585851479515788616908294020641007337691232958576821567341613162723672674484789842879668839110334387403633063704508272691825067913220725553877962132390053276632236915375019968359095878465599828214266657794553287166107543160002134226978981726854090093857638087302713819245055215654848778925839209314327088119338137993792604070615914509974007134079333964367295549540533406427428728355823680649762425686866223021937655618473500697205577975818041233426564102476793778723542509411599082521794695065325249440207081156152937228171531564114504497808893546260031991926589024762249979521671332705996060860340010524973981285484671664932330989362412536532871445607443984903071760207102238058886216806589287933732610085139408335679894763370660142207089620488392258096996741058669613518709215484594216010829450836184815635319368541357280071503770203474636276161254279879428087554840913946230706568121439586174208481235880645008510768798598358082916747699997701689551128093160265407228816766478072839929856
  | 20 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps2
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps3
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps4
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps5
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps6
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step12 : preCheck K ((List.replicate N false ++ tail).getD 12 false) (Q 12) (Q 13) = true := by decide +kernel
theorem step13 : preCheck K ((List.replicate N false ++ tail).getD 13 false) (Q 13) (Q 14) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps7
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step14 : preCheck K ((List.replicate N false ++ tail).getD 14 false) (Q 14) (Q 15) = true := by decide +kernel
theorem step15 : preCheck K ((List.replicate N false ++ tail).getD 15 false) (Q 15) (Q 16) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps8
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step16 : preCheck K ((List.replicate N false ++ tail).getD 16 false) (Q 16) (Q 17) = true := by decide +kernel
theorem step17 : preCheck K ((List.replicate N false ++ tail).getD 17 false) (Q 17) (Q 18) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001Steps9
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step18 : preCheck K ((List.replicate N false ++ tail).getD 18 false) (Q 18) (Q 19) = true := by decide +kernel
theorem step19 : preCheck K ((List.replicate N false ++ tail).getD 19 false) (Q 19) (Q 20) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110001
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11
  · exact step12
  · exact step13
  · exact step14
  · exact step15
  · exact step16
  · exact step17
  · exact step18
  · exact step19

/-- Uniform column exclusion, for every padding length at least 77. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110001

-- Certificate component: SixTailBackward110011Defs
/-! Generated exact predecessor sets for `0^0 110011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110011
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,true,false,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110011

-- Certificate component: SixTailBackward110011Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110011
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110011

-- Certificate component: SixTailBackward110011Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110011
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110011

-- Certificate component: SixTailBackward110011
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110011
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110011

-- Certificate component: SixTailBackward110101Defs
/-! Generated exact predecessor sets for `0^2 110101` at width 7.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110101
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 7
def N : Nat := 2
def tail : List Bool := [true,true,false,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 65536
  | 2 => 1329227995784920595342347523963486208
  | 3 => 42701449364590422419349652019974512680
  | 4 => 75557863725914324467728
  | 5 => 332306998946228968243966163579584512
  | 6 => 9444732965739290689536
  | 7 => 170141183460469231740910675752738881536
  | 8 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110101

-- Certificate component: SixTailBackward110101Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110101

-- Certificate component: SixTailBackward110101Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110101

-- Certificate component: SixTailBackward110101
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110101
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110101

-- Certificate component: SixTailBackward110111Defs
/-! Generated exact predecessor sets for `0^0 110111` at width 8.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110111
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 8
def N : Nat := 0
def tail : List Bool := [true,true,false,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 14134776518227275503921912379727790871922952195198546151671126788784783360
  | 3 => 220855883097298041197912187592864814479084524216769223218767087739600896
  | 4 => 68719476736
  | 5 => 57896044618658097711785492504343953926805133516280751251460479307672448925696
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110111

-- Certificate component: SixTailBackward110111Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110111

-- Certificate component: SixTailBackward110111Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110111

-- Certificate component: SixTailBackward110111
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110111
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C110111

-- Certificate component: SixTailBackward111001Defs
/-! Generated exact predecessor sets for `0^0 111001` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111001
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,true,true,false,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 524320
  | 2 => 268439552
  | 3 => 134219904
  | 4 => 33817088
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111001

-- Certificate component: SixTailBackward111001Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111001

-- Certificate component: SixTailBackward111001Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111001
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111001

-- Certificate component: SixTailBackward111001
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111001
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111001

-- Certificate component: SixTailBackward111011Defs
/-! Generated exact predecessor sets for `0^0 111011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111011
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,true,true,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111011

-- Certificate component: SixTailBackward111011Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111011
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111011

-- Certificate component: SixTailBackward111011Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111011
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111011

-- Certificate component: SixTailBackward111011
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111011
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111011

-- Certificate component: SixTailBackward111101Defs
/-! Generated exact predecessor sets for `0^9 111101` at width 12.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 12
def N : Nat := 9
def tail : List Bool := [true,true,true,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 42593471463832657737390643390308995585859016161606975400354909927828421164939140831709258661226346359372267899056045841646739939778599826051116197585066199863634535747350076974814621903232495581213679990222150112359103126088426471569810133237825899462621387001548374800219988340321699013116683247989749009409373046071593105705393303548047024794886699546792561973900437672832223489189807412370029050049265982330823702995479472184262084937048362728231242401894771453213919284150494619967027617494490899631079643499778782222412514867519648939692191586996979318126917746205986015282002829968686415322824519880555031722356753574645955319857279518526626058634276573369844233542167819239054628386551351235622079244633380486230663569027697438555878461753529591482282966180462463972262822338506589786068205503601109040650537232720116570151347601856895418390793089601665629416523486099643431936375579151316165457917365375060893521502786773822620491694771060666181540231827132225233634007426523935777743104235288566052942301358350540716568568289346548484093854247406952295037070605827342504065735771535490281213750267202821188443791339903445918253337863626821673281312012996084236640321536
  | 2 => 42044150990595335229503856911921787380004877248545658231887678885613395009127591621822951677851256633559849976143942737872814703075066100420072089515453314847604913040800777155019722924662706903822596374538442842387262758268929310734322653080106272776796254339829977867250585508053391359539234745502834019166169284051082738455477876772551247089386352844995856306598755899279519947236246445368850253467751015468241468418108679518064919999342810661509317563278916002479198651542363619302593982507741941749498492776428706429378245327431155728406249133869787500467057749955232903737424040190583322175984683286571719313578474317369886227081261707573936778238307719627455329288658535503975615579491921102381437290186637431004032624254444056973909745994838027642143161308689394806612306422788631025920963419524153594574089344139247207650427382195412918482737735563510263656904876185286249843958033160034246527710540769221812337674963778992152587103436066370820264021546060928937605610038407572260015151513600
  | 3 => 884631792303004538966103260724113936154909488552025335759523501210048328097827480852819662435218856360940939291516351481997219441959744260755718683712880134148829737197743394919043409692136064574599255390528829210138843057278210887691153385493275819091305305535568573195928400224181282596388760548646906131019473967832794682706458900381711229850982034533290904632544731490136121061930651012469579556644269055363666419584883401902419374756054214408938422113248061378605072023122382686337021044379196772132782098203571578709600740649113013269095112900405926191190733088717285759031657197158836244402056302993731261805659309641443884660158555165196788820763777892886356729558462153284067483282920843883963194023602837591204916922121584395400545245695163046707035370379941285331532110918409235590319731604461199818416985300543368210888827274078332716553963809870295626643324965448463688297059767507973585251109248295207016001663745003700442237502021859248764541753707879077754865947030772813648698563243729222577133434474291347853885947709333473601734893752712940579280208584161402929200433050995446127587386317073407811628575688736674064184649479316414903140294467257455967321743067101539255016931889505315938369536
  | 4 => 556449705130762155260120536926294119933642100397887586428298872892180913411031165359924263875151019902874951592414225916517627251233366179164179925632098182657121107261482851834468362328112178654299934165807877706704520625431065114305197283283042841532245246733589957379111969664373014280661881108392059617268582346180656814912868516088325018971733162297356165304395201262872454495438865750255358589480556222958893555736035545900964794598659986371135185933613084098742262434673273275134989011881225491066648508712096454319616555030441344315652497748427126722551568516977971147704476426356573623446393573085656586744983899464459625643390478187782859305183339214820720957976679810476825614016730142657929336966400377142437268165588787758254000258589900148712395315160086459431287517926199657770909822823632190340744561381180717713296317486027794106456274781180775124018297118615605963015710687964440519436755015004548006009294210800468542084712904947146396157571852646270627741696
  | 5 => 51493133110513519019787684348156147103900351381641517560519328775577509525826485340866255578285760925681112683930218652875765956785944824960142267131498355811893336400463101037379494604250614856187566079163636640717503725024521608480286620656304616216434391554341502030071843955109514197660929968609460859820155216659073291728117598653434487406820153773699844454896844898094261560977958027120825428709735734157335837255558411395135976668777721830677554277930192009031306077541947957753552070077146836384724187264778116245339929735570438883965101768795502614060804520663389320098659665841393905711601856933130923178859551685505003673501245071427929046129272863559643127151804952564093383674311262958773704884721862784064359608957177739011786320328794057239813106287327854605740693620150675155603135342463193395533888574814152104824412179706874680019808949965267150807805255678531250962961782726532401947483717306422473855559970817481450741929950501077913613937963196592269372563296913183813262231873178751140964264424252766198708681050300352186547742501280157439453023571481223382185371517994957207172046663713970231997021294585061049006675927138126140157882400426531599032003835428581745282860202328064
  | 6 => 65274305103521745343340112319959810382109322199948256879376129201805991168697883336717068124394969374737257023584984378633822943884271780808356706447028406789521668098011800786760258869413413016743829714076016345272115535317944956718220427370270211076106213696191673511475300643025136998774392849507833539802452777569674033409449800091815806142532865046070829860319194413281977424591318616386546876855914149488130539294915210456444305148109160613879987308171333730641902730046222754725604745918149499883341281318679375154236012241945820667577395287666479723629280999336235743747676705323432386240411747777523982043652926111786787506776049702967429000287858456800861042071761035654946024897900903529700425694378148439522864754046427779088152635813985354132469794636214595120720773840959143997973010790268670575731099385378753267818103157118571591793208845146120257297888532889947502999141713502032705904762496812768236985423858760199090345954947926300437429757967741103019153649089907946918583956598687118327419534647307275415202594127885349562225409569848309397646480160037036998252898631880690519980590631062899425685108375269265281031785054283920241704650464479726994388837121747202907301578935344261772408418938690010134299541504
  | 7 => 16350448491361915159084141253795700476742190930536882681279896460070320702024627701892317787482072939505770392432694930884454894779713586552762105446438960636177891332912164508415088862390918138495768984988348545670095894021126145594528180954250448602092901541622408489355931223851550815228466401284223890909589704538601491880733618596672995265581983379687923311194439725673046659235780893990331766491278031265653583171983876466268001143688977000176163265626001153516629831712690368856558278146674568421994370315221897044619579873541191039981689946717572931725725939429677866616536889888046331414888987355961305619483995983407275577535251538377433011909876811687055934287518385090323110279182651703384039885820861980481851280999075101726240770482480907530345418316555644334160679988734040444017365872532012929295007752290049486712649853693090022578733146263166736224306252253699550270623790931962094481649037843751485757933935305647462779944617767704128590762548093941492804223705282279449230376532106110634233331245488738253678282600277261326444349099428270835824832780126493447779872120921513592476741003846028390106784572433711724832136455754111439149513301391234408467339270099482685801591376339214000588651069342810723730850884
  | 8 => 32637650547587287822273920727842050629207190031918712050934557816496127732634962249082902626410692360261514570624791129141198924884271347749161149173220330730341345801395805737112813421412004970051357684509335823198100008671945347312238588648429459821085936584894171694896228660063783614333115154807566625334497259570867852362440604230770707563838085639369909872264351987705877784914373588437232742535412376977325618851991681116550104121478316404340399525533381911543023814587144446584565675631437501649741145573693436957024904218533686830089270370782347801203005885262884312550271943801304077187227110221162048718019962851747222289230698669518049011287856276057343804056229956592435915536592094981797954361372526067117352472673405655179477585657446349280963594598828325616848824203855068854760946362807361132258479089927118249412006960854432689951530467156111941448261851632132271018547945836428844668032087030893165669740877849332139171067144486299822378943612711212150978434891709570807765012844477042586710297255692199317221425253184646802901509010034536861723236865091061812424853614179753427716029183348218900258130049641455422932786165254970888558287819304020900861221635902875381082487181783731886436490699171053145507760256
  | 9 => 63744438562814484051010297284950218663327896060020982689467375688717889890842129934620777095641940816704718427421480520817047300038104735324035055984998857794408876078471557977045729753097129086985825389429836608086452412359684901594003726861219073216747034284860775526673796651927985040903012351260982096751697121930080242009615536628814566849025854280506262564382177607891199878430064108263329296264105736330683147386150840909842466626085671134513865729078133256243706903031506113969140729742325993189256286689844652350076781522918739769136124210047792275906344489607945496406689580625688211655288027736037687190138898492583131636790371947364854365766409200048970387883585857189115996318379321373609670592560785621233129314607816485442716350041794033794293986007471146402818203681593672874715979804562566958028359457373667789934524376420605258552641218649601860123864416898682579249271632746567376941944925251007557179213060093055970712305133199155922502310190018042071218308136629362455907861933634651480571222804018117331305457484388349139339943685251375720268198606211272231216426744196046708405082382699785917953706616172927238987073856345783928652710731315599239208486313669849429000487072809374068118176956106356346061312
  | 10 => 3984027410175905253188143580309388666457993503751311418091710980544868118177633120913798568477621301044044901712185908653211873772376226834347671843915425407203510194945182793961950645959410546548568992659972939401154780728903628332795466172579142065036040911505904022488723940811609684427548012155775860829725605426525522681911241868591757508344342467474783816183495163500083080419582915101178412429780068491135812504394646519671539252037940768139638492650317297323879061655836490514768709445015143112570791755778324360638114671826477000723136853427339392942602854912552332970768447230620937565907500046400236046636082008223588200824751177130766010186978413774749196527015475249008920805043042532660275160613752898686312358202422022941243789102843547833393187516822929460179275345610211730855320394998386700060459117496209684253803261052997807484144915016265043003721045254236236004809603748645497847287721958002663344946160567230266113844214237224370562437263992809664308975716668160138529704525054265995758799971731289998915537334663585707868336591782776463082985319075701097840767170281998125514849005420676972356946393000404644944535237273445465750755466457295540122397147860537080345856547286139084057869034232187166130176
  | 11 => 24685619739496446847994910529323207663700032299260622694384830333895284689921860657421220154290374639892804784504835314169777317143970130686810306349920332341764490937404921887015415076571986446919500669985847319332901291925213647978089310724592024567954100785077620772501936773804714971197389877407111757324236066827547648353661760585879168948172989493490244041225506858568213866154871047628359506981406658664212356415768152822715218314246592523605178840172041357968477731342745068221474903912206819394840587382199634279515695673500005965368715151707058596211517851243956211045850874106413637079954158173342907210506753083452651746358928483352620061080124762881544405861537539016360514202949854399393833312491204989883468791102040758533334948283701143201935450348890954393660762970571949804168950045882426602599875358871653951465734020771507022646475831513068523882254718633398862047618798696382761733371138419967228558225164887145472563995239556028905398206560754544755302915869049873297981891313287937748517907305007017833928047295274011441642821657378874540194542067321240561783457296779074953467024900096
  | 12 => 4123678330405087685498374221366984954089317057900104262462784875123790425105688284686404828183633224942349909964891086086676925759584441340507088115762723035704344160664907942351632995309234873230720724730672756917176305067668035542444896101177345052548810184785328926774725935717835798651444434276670015032998880347558303319286200881282911325381616533722737115450145930916961537131913757215277371800137286603288955416677475076727218762015626703995539754204327293876900103418270235351535588655439248496351694601931248204077380369447463124307237054187328904109034473407477335224021673401354614398393792678003725062298647566228815811529059438151865772368557242422831023210133615068880091115381467321153495998199147333355475446963145531678026014756497790039247725373013240239473003905794012379955907671832113512400036807902933395046573776075048317495941003046821327774584992612213129564242223190535039070695528879063765565013918890756235608286091397401714963909916961850757546153547518865759973181514743245666894833798125866521515189091616177373928517078614016
  | 13 => 518234172026405255552493535844883061883637775106250854607949846323748038533172724172402419033600966813101390483466388354883379018477614034820755419195024084626133248165832707035904622372309724531209095382255191697551221137515862382035422817652504307698071660802370144232849494923646062942796680458576149091355815882074576471641411784702136867765973777233317300561855384160679211738617581000819007419751804238036743983241988005137870226273097659478225313594606483973034500232825407019410855546955944699643352886893336766238645080199297988103580483248113038108967381619232123251486084723443726678831704852862417474533199960082125356399965465659077517832213897820464762420691893262824564345544065233223852688208675237003402143556665250847651599085932384204954677229781076801910376828099394558437681207824205913169739382662056070475685082098052281145876116917164214954819757987485365372380938075589069890017078194070263933161019410215682672236386532456737942244473123635200
  | 14 => 522194440706576253345876355358312191289982124523691890192116741641976953985778728424413405967498779170445053357219631418993786719092896803631618043925682638972978488271854999170180795067191859157214035005927973113188159419698856372836167342172293308748403954352901852035642024370059304557233988891799014503343469488440893892973452815095130470299789726716411734651513348221529512507986199933857107770846917779942645743159118957217248367043905936319748237550094520674504208530837546834166925275516486044134775384991808184705966507606898412918594045916828375610659246423184062775112999150206172392431297837246097308511919411459658460916516275128388139287031639186433706843172649681552765665167176485407416810390904144294236366434040516739738455036275051236444679629608791186852451880823546275470766576036962084586009663349889486777984897170803007721972358521389546088941763660385929677807264976523178693594619299151020033656115128594915199395160328438284015166484040013151289690978936900875065247697241542565934354230159918183452136337095790645261574579360261746238075035455059100025373721570856630568171033987937658200940804173551819277637011822685739542270608413789928313531108409313472180603783050108319194119218680280975731375210496
  | 15 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101

-- Certificate component: SixTailBackward111101Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101

-- Certificate component: SixTailBackward111101Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101

-- Certificate component: SixTailBackward111101Steps2
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101

-- Certificate component: SixTailBackward111101Steps3
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step12 : preCheck K ((List.replicate N false ++ tail).getD 12 false) (Q 12) (Q 13) = true := by decide +kernel
theorem step13 : preCheck K ((List.replicate N false ++ tail).getD 13 false) (Q 13) (Q 14) = true := by decide +kernel
theorem step14 : preCheck K ((List.replicate N false ++ tail).getD 14 false) (Q 14) (Q 15) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101

-- Certificate component: SixTailBackward111101
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11
  · exact step12
  · exact step13
  · exact step14

/-- Uniform column exclusion, for every padding length at least 75. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 75 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111101

-- Certificate component: SixTailBackward111111Defs
/-! Generated exact predecessor sets for `0^2 111111` at width 6.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111111
open Rule30StripCertificates Rule30BackwardTube Rule30BackwardVacuum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 6
def N : Nat := 2
def tail : List Bool := [true,true,true,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 256
  | 2 => 1152921504875282432
  | 3 => 576469548530665600
  | 4 => 1099528405248
  | 5 => 35184908959752
  | 6 => 68719476736
  | 7 => 9223372039002259456
  | 8 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111111

-- Certificate component: SixTailBackward111111Steps0
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111111

-- Certificate component: SixTailBackward111111Steps1
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111111
open Rule30BackwardTube
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111111

-- Certificate component: SixTailBackward111111
namespace Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111111
open Rule30BackwardTube Rule30BackwardVacuum
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
/-! ## Predecessor-chain boundary states and `71 + d` white-padding exclusion for `111111` -/

/-- **Predecessor-Chain Boundary States and `71 + d` White-Padding Exclusion for `111111` (`c111111_endpoints_and_no_padding_at_71_plus`).** -/
theorem c111111_endpoints_and_no_padding_at_71_plus
    {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (d : Nat) :
    Q 0 = 0 ∧
    Q 8 = 1 ∧
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate (71 + d) false ++ tail) :=
  ⟨rfl, rfl, no_padding hlo hzero i (71 + d) (by omega)⟩

end Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward.C111111
