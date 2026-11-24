module
public import Ruliology.CellularAutomata.Rule30AlternatingArrivals
public meta import Lean.Elab.Term

/-!
# Every right half beside an alternating column enters one closed set by white sample 35, sharply

Let `F` be a right half of rule 30, of any support, finite or not, beside a column that alternates, black first (`Alt F T`), and number its
white ticks from 0. `closedSet` is the set of 777 windows of the first twelve cells of `Rule30AlternatingArrivals`. A half in it stays in
it, whatever lies beyond (`stays`).

* **Entry.** From sample 35 on the window is in the set (`uniform_entry`; for `drv altCol R` at every `R`, `every_half_enters`). Any white row
  is in it after 35 whole periods of two ticks (`white_entry`), and the single cell is in it from there if its centre eventually alternates
  (`singleton_enters`).
* **Sharp.** With black cells at sites 2, 7, 8, 11, 12, 14, 18 and 21 at the first black tick, no sample before 35 is in the set (`sharp`,
  `last_windows`).
* **The kicks from there.** From any kick at or after sample 35, the next two gaps are one of nine pairs (`nine_pairs`), so no right half
  kicks once in four from any tick on (`no_pure_four`); the gate reads none of the ten words of `clean_of_set` (`gate_words`).
* **Streams.** The kick, the net and the odd kicks are eventually periodic together, and an eventually periodic black net makes them so
  (`streams`). Nine nets at samples k to k + 8, with k at least 35, give the kick at k + 6 (`read_kick`).

The finite part is one table of sets of ages on spatial prefixes, 36 sets and 1,047 branches, walked once against itself with a white and
a black tick as the step. Every row at the start carries age zero, in the set or not; each checked step advances the age by one; and a row
that carries age 35 is in the set. The sharp half is checked by direct evolution, and `stays` rules out every earlier entry from its one
failure at sample 34.

Known. `Rule30PeriodTwoWidth13` (AIOvernight) has that every right half is eventually in the nine-pair gap language or kicks once in
four, by a rank certificate of a strip of thirteen columns, and excludes the fours on the single cell by its left half.
`Rule30PeriodTwoOnset` has closed sets of twenty windows on five cells and thirty-eight on six, from one full period on, for every history.
`Rule30AlternatingArrivals` has the 777 windows, their closure and decoders, and the same alternative. Here the alternative is excluded on
every half, from the right alone, and the time is exact.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30UniformEntry
open Rule30AlternatingArrivals Rule30AlternatingArrivalsTables Rule30Ether Rule30Jen
open Rule30PeriodTwoCoupled (altCol)
open Rule30TrappedRunMasks (Tree)
open Rule30DrivenPrefix (step)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private meta def masks : Array Nat := #[
  0x7ffffe, 0x1fffffffe, 0x3ffffffe, 0x7ffffffe, 0xffffffe, 0xfffffffe, 0x7fffffffe, 0xfffffe, 0x7fffffe,
  0x7ffe, 0x1fffffe, 0x3fffffe, 0xfffe, 0x7e, 0x2, 0x6, 0x3fffffffe, 0x1e, 0xffffffffe, 0x1fffffffff, 0xffe,
  0x3e, 0xffffe, 0x1ffffffe, 0x7fffe, 0xfe, 0xe, 0x3ffe, 0x1fffe, 0x3fffe, 0x1ffe, 0x3ffffe, 0x1ffffe, 0x3fe,
  0x7fe, 0x1fe]
private meta def branches : Array Nat := #[
  0x100050041002e0040003f000f000e0009003e003d0033003c0034003b003a0007000d003900040038000a003700350036000c000b000c000c000b000400080008003200090031000700300008002f000800070006002d002c0029002b00010005002a00050001000400280027002500260002000300020002002400010000,
  0x3400080013006100060012005f00590040005e005d005b005c000600560010005a00100055001000580054005700110056000f0006005500060010005300420052004e0051004f001000500010000600060005004d0047004c0049004b002a004a00050001004300010048002c002a00460045000300050005004400050043,
  0x120013000f0013008000130013007f006f0013007d0060007c006e007b0072007a0078006f0079001300560077007500760006005c0010007400120010007300100056007100700013000e006f0015001300120013006d006c0062006b0013006a00660069001400670068006700140014000f006500120064000800630008,
  0x10003004600a100a0009d009f00020004009e000400020017009c009b0099009a00170002001700980007009700940096009500070011001400160016009300160092000000160090007e008f0087008e008b008d0083008c00130013000f008a00890082000e0088007f0083000e0086008100850082007f008400830013,
  0xd00190010005500c000be000f00bf000f0011000200bd00bc00a800bb00b200ba0018000400b9000400b800b7000400b600b5000400b3001700b400b300b30004001700b100ae00b00018001800af0004001800ad00aa00ac0004001700ab00170003001700a90007001800a700a2000300a6000300a500a40003000100a3,
  0xe200df00e1000e001a00e0001a000f00d700de001a00dd001a00dc001a00db00da001a00d9001a00d8001a00d7001a001a000e00d500c100d400c200d300cc00d200d1002a0043001100d0001100cf00bf00ce001100cd0011000f00cb001000ca000f00c900c7001900c80019000d00c600c400c500190019001500c30019,
  0x7f0102008301010006001300cd001100fe009100fd00f500fc000e00fb00f9007100fa0071007f001300f8008200f7001300f60013000300f400d600f300e300f200eb00f1001a00f000d8001a00ef000f00ee00ed000f00ec000f000f00e4000f00ea00e9000f00e8000f00e7000e000f00e6000f00e500e4000f0040000f,
  0x6f006f006f0121006f01200012011f0012011e00120006011c0118011b0119011a00130101000f007f0013011700800116001a001a001301140108011301090112010b0111000f00ec0110010f001b0017010e0002010d0017010c00170002010a007f0101001a01050013010701040106010500130011008c007f01030100,
  0xa00100006014100010010013f00ff013e0129013d0132013c013a00fb013b0013011900fb0139013801350137007f013600150001001301340133000e00130013006f0131012f0130000e00fa0013012e012b012d000e012c0013006f00120071012a00710123012801150127011d01260125011900850124012201230011,
  0x8000b0017016100030017001c0015000f015e015d000f00ee000f015b0157015a000f015900130010015800100012015601540155000f001a00500153014d0152000f0005015100010150014f0017014e000200020026014c014b00440005014a01470149000500050148002a002a000601460145014201440010000a0143,
  0x182000f0181001100cd0100017f001500e0017e00e0017d00e0001a017b0160017a016f0179009b0178000b01770176001c000f01750170000801740004017301720171001d000f001d00040004000b0017016e016d016a001c016c016b001c00080017016901620168000b0167000b016601630165016400080163000b0008,
  0x401a2000b000201a0019d000f019f0043019e005c00050006019c019b0012019a000100060199000600010197018f019600ed01950194008c017d008501930192000f0191019001410010001000c2018e015c018d015f018c0185018b018a0044000f00050189000201880187001a0186000f000f001a0184017c01830180,
  0x1a401c201c101c0000b014e01bf01a401be00200004002001bc01b901bb0017000501ba0005002601b801a601b7001101b601b1001501b5001501b4001501b3001501b20015001101b001ab01af017d01ae001101ad000b001b01ac0007000b01aa001e01a701a9000a01a8001f01a7001f000a000101a501a401a300020003,
  0xd0061000d001301e001de000f01df000f000d01dd01da01db01dc01db00150005000f01d901a101d801cb01d7001501d601d001d5000201d4000201d3000201d2002601d101a401c4000201cf01cc01ce000201cd0002002701a40005000201ca01bd01c901c301c801c501c70001000201c600030001000101c400030026,
  0x202000e0201000f000f00ec004001ff004000e401fd019801fc01e101fb01ea01fa01ee01f901f7001a01f8006f01e601f601ef01f501f101f4000f01f3000601f2000d01df000d002101f0001200210010011f01ed01ec0116000f01eb007f0083000f01e901e501e801e70083001201e600130013001a01e4001301e301e2,
  0x222021b0221021e02200116007f021f008300110088021d021c01230001000e021a02190013008002180080008201330216021102150214001100e40105021300130212010100130210020e006f020f006f007f0013020d0082020c0013020b00130006020902070208000e01ff000f020602000205000e0204000f0203000f,
  0x242000400080004000802400008023f00080034023d023b023c001d0008001d009e001d02390238000e001a0237001a00d7023600d7023500d700d80233022f023202310119000f023000fa0011000e022e0228001a022d001a022c022b02290006022a000600500006011e0186001a02260140022501fe0224020a02230217,
  0x2620260001702610017000d025f025e001a001d025d024d025c025b01c40008025a0256025900170258016b0257000800170008025500080254001a00b60253001702520251024f00180250001f00180018024e00000022024c02480002024b01cc024a00020249000201cc0247023e00080246024502410064024400040243,
  0x2820234028102790280027b027f01ff027e000e027d000f027c000f00ef000f000f027a000f00e702780264027702670276000e02750270000102740001027302710272027100150015000e026f0003026e026c026a026d02300011026b0269026a00110011000d0268000d000d0011021c026600010265001000010263023a,
  0x2a2029f000802a1000802a0000a0009029e00000015000d029c0015001b029b0000029a0299029802980000000b000001410296004600020294029102930001026502920265000102900289028f00010001028e028d028b028c000101410001028a000100100265001202880287028402860006000b0285000b000600120050,
  0x2c202b602c102bf02c000030003026502be02bb02bd000302bc004602b202af000302ba000302b9000302b8000502b702b0004602b502a802b402b1001002b3001002b20005000302b002ae02af00050003004602ad02a902ac02ab0017009a001702aa001f00170008004602a70297001a02a602a5029d02a4000b02a3000e,
  0x1202e2001902e1001902e00019001100220013008c001102dc02cc02db02d302da02d7011602d9001a02d8028a011f02d6007f02d5001102d400130006006102d202d002d100130019001202cf001302ce0019001202cd0012001002cb029502ca02c3001a02c9026502c802c70003000202c6000302c502c4000302b20003,
  0x30202fd030102ff0300000e0015001302fe007f0101000e001302fc02fb0013006f008302f902f402f8000e00fa02f7001302f602f500130010001302f302f20119000e027100fa02f0028302ef02dd02ee02ea010902ed02ec01e6008c02eb0061011e02e902e702e8000f012c020b02e602de02e5000f02e402df001202e3,
  0x3220013000f00830320031e02f3031f008c01050081031d00820119031b02f1031a03050319030f0318031303170316010b020d031503140116000e008800120312031101190119031000130133007f030e030a030d030b030c00fa00130133008501ec0309030600400308007f03070012000f0105008c030402fa0303000e,
  0x342032f0341000e01ff0340033f033d033e007f0001000f033c0333033b0334033a0339000c00ce0338000c0337000c0336000c03350011000c000e000c00110332033100ec001102c403300003000f032e032c032d000e00e40119032b0329032a000e000f0082008a02ff0327032103260325000f01ff000f032400130323,
  0x40362036103590360035a035f000e035e0163035d035b035c000e0008001c001c00080008000a00170004035703560012000e0355035303540010000101410352034f035100040005035000050017034e034c034d0003000502b20003034b0010034a034903480007000100100005034602270345031c0344000e03430328,
  0x382037a0381000e000e0380037f037e011e0006037d037b0354037c001003540001002a037903580378000e000e037700d8037603750363037403720373000c000c00360371036b0370000a000a036f036e000a036d000a036c000a000a000b036a0367036900040002036800020004000403660365000a0364000a000b000a,
  0x3a2038d03a1000e000e03a0039f0398039e039b039d000e0013039c001302d4039a007f0399000e02d40012011903970134039603950013039403900393001e03920359039100b303590004001e038f038e001e001e000e038c0387038b000e000e038a00d803890388022900610012038603830385000e000e038400610015,
  0x3c20014000f03c103c003bd03bf000a03be000f0000001e002003bc00070020000503ba0017000a03b803b6000e03b7001a001503b503ac03b403ae03b3000e002303b203b10015002303b003af0023001a0023000103ad00100199000603ab0050001203a903a303a8000e000e03a703a603a502f300fb008103a401340119,
  0x3e2001103e1001103e003dc03df03de00e00188001a03dd017d001a03db0011001103da0011026d03d803d203d70011001003d6001003d5000503d4000503d30010034803d103cd03d00003000303cf000503ce0001026603cc03c803cb0017001703ca03c90003001702ac03c703c601cc001703c503c401c4001703c303bb,
  0x5011e0082011602f3040003ff00fa020c000e03fd03b903fc03f503fb03fa00110003023003f903f8001103f7000e001103f6001103dd03f403d903f303e5001103f203f103ed03f0001703ef0017001703ee0017010f03ec03e803eb03ea03ba0016001603e900020016000203e703e603500002000503e403e30011001a,
  0x130422001300150420041e000e041f00fa0213041d040d041c0419041b000e006f041a00130005041804110417000e04160009041504140009000e041300090412000e001a000904100235040f000e040e0026000201a40013040c01340013040a03aa0409000e000e0408040703fe040604010405000e0404040202fe0403,
  0x43903470438040b0437000e000e04360435042d0434042e0433000e00fb04320085043104300013006f042f0013001001310401042c0421042b0428042a00fb01190429007f01330427042504260013001301230424042304220013]
open Lean Elab Term in
private noncomputable def cert : Tree := by_elab
  liftM (makeTree masks branches 1047)

private def clocks : Nat := 2^37-4
private theorem valid : cert.valid = true := by decide +kernel
private theorem advance : walkAll cert clocks clocks false true = true := by decide +kernel
private theorem target : isTrap cert closedSet = true := by decide +kernel
private theorem start : cert.low.testBit 1 = true := by decide +kernel
private theorem finish : leaves (fun m => !m.testBit 36 || m.testBit 0) cert = true := by decide +kernel

/-- From an arbitrary white row, 35 complete white-to-white steps force entry. -/
theorem white_entry {F : Nat → Nat → Bool} {t : Nat} (hF : IsR30 F) (drive : Drive F false true t 35) :
    InTrap closedSet F (t+70) := by
  let x := code F t 82
  have f := fits_rows (L := 12) hF drive (fits_code F t 82) 35 (by decide)
  have last := free_march (x := x) (o := 1) (n := 35) valid advance (by decide) ((cert.bounds valid x 0 1).1 start)
  have inside := leaves_value finish (rows false true x 35) 0
  change (_ || _) = true at inside
  change (cert.value (rows false true x 35) 0).testBit 36 = true at last
  rw [last] at inside
  exact trap_of_bit valid target f (by decide) (by simpa using inside)

/-- Uniform deadline for every right half, with arbitrary eastern cells. -/
theorem uniform_entry {F : Nat → Nat → Bool} {T k : Nat} (hF : IsR30 F) (h : Alt F T) (age : 35 ≤ k) :
    InSet F T k := by
  have e : InSet F T 35 := by
    have e := white_entry hF (h.drive 0 35)
    simpa only [InSet, show T+2*0+1+70 = T+2*35+1 by omega] using e
  have later := stays hF h e (k-35)
  simpa only [show 35+(k-35)=k by omega] using later

theorem every_half_enters (R : Nat → Bool) : InSet (drv altCol R) 0 35 :=
  uniform_entry (drv_isR30 _ _) (alt_drv R) (by decide)

theorem singleton_enters {T : Nat} (h : AltCenter T) : InSet trueRight T 35 :=
  uniform_entry trueRight_isR30 h.alt (by decide)

theorem gate_words {F : Nat → Nat → Bool} {T : Nat} (rule : IsR30 F) (h : Alt F T) :
    ∀ w ∈ banned, ∀ i, ¬ Spells (fun j => gate F T (35+j)) i w :=
  clean_of_set rule h (uniform_entry rule h (by decide))

def gapPairs : List (Nat × Nat) :=
  [(2,2),(2,4),(2,5),(3,3),(3,5),(4,5),(5,2),(5,3),(5,5)]

private def pairWord (a b : Nat) : List Bool :=
  (List.range (a+b+1)).map fun j => decide (j=0 ∨ j=a ∨ j=a+b)

/-- Every kick from index 35 has two successive returns forming one of the nine
pairs. This theorem only takes the right half and its alternating boundary. -/
theorem nine_pairs {F : Nat → Nat → Bool} {T k : Nat} (rule : IsR30 F) (h : Alt F T)
    (age : 35 ≤ k) (pulse : gate F T k = true) :
    ∃ a b, NextKick F T k a ∧ NextKick F T (k+a) b ∧ (a,b) ∈ gapPairs := by
  obtain ⟨a,al,au,first⟩ := next_kick rule h (uniform_entry rule h age) pulse
  obtain ⟨b,bl,bu,second⟩ := next_kick rule h (uniform_entry rule h (k := k+a) (by omega)) first.2.1
  refine ⟨a,b,first,second,?_⟩
  apply Classical.byContradiction
  intro absent
  have classify : ∀ x y : Fin 6, 2 ≤ x.val → 2 ≤ y.val →
      (x.val,y.val) ∉ gapPairs → pairWord x.val y.val ∈ banned := by decide +kernel
  have bad := classify ⟨a,by omega⟩ ⟨b,by omega⟩ al bl absent
  apply clean_of_set rule h (uniform_entry rule h age) _ bad 0
  intro j hj
  have bound : j < a+b+1 := by simpa [pairWord] using hj
  simp [pairWord,List.getD_eq_getElem?_getD,bound]
  by_cases zero : j=0
  · simp [zero,pulse]
  by_cases mid : j=a
  · simp [mid,first.2.1]
  by_cases last : j=a+b
  · simp [last,← Nat.add_assoc,second.2.1]
  have quiet : gate F T (k+j) = false := by
    by_cases left : j<a
    · exact first.2.2 j (by omega) left
    · have e := second.2.2 (j-a) (by omega) (by omega)
      simpa only [show k+a+(j-a)=k+j by omega] using e
  simp [quiet,zero,mid,last]

/-- Two consecutive gaps of four are forbidden after the deadline, so an eventual
pure-four gate is impossible even with an infinite right half. -/
theorem no_pure_four {F : Nat → Nat → Bool} {T : Nat} (rule : IsR30 F) (h : Alt F T) :
    ¬ ∃ φ N, ∀ k, N ≤ k → gate F T k = decide ((k+φ)%4 = 0) := by
  rintro ⟨φ,N,four⟩
  let base := 4*(N+35+φ)-φ
  let word := [true,false,false,false,true,false,false,false,true]
  apply gate_words rule h word (by decide) (base-35)
  intro j hj
  change gate F T (35+(base-35+j)) = word.getD j false
  have start : 35 ≤ base ∧ N ≤ base := by dsimp [base]; omega
  rw [four _ (by omega)]
  have phase : (35+(base-35+j)+φ)%4 = j%4 := by dsimp [base] at *; omega
  rw [phase]
  exact (by decide : ∀ i : Fin 9, decide (i.val%4=0) = word.getD i.val false) ⟨j,hj⟩

theorem read_kick {F : Nat → Nat → Bool} {T k : Nat} (rule : IsR30 F) (h : Alt F T) (age : 35 ≤ k) :
    gate F T (k+6) = decode (fun i => net F T (k+i)) :=
  kick_of_white_nets rule h (uniform_entry rule h age)

theorem streams {F : Nat → Nat → Bool} {T : Nat} (rule : IsR30 F) (h : Alt F T) :
    (EventuallyPeriodic (gate F T) ↔ EventuallyPeriodic (net F T)) ∧
    (EventuallyPeriodic (net F T) ↔ EventuallyPeriodic (oddKick F T)) ∧
    (EventuallyPeriodic (blackNet F T) → EventuallyPeriodic (gate F T)) :=
  periodic_together rule h (uniform_entry (k := 35) rule h (by decide))

private theorem seed_window (x k : Nat) :
    code (seedRun x) (0+2*k+1) 12 = (rows false true (step true x) k) % 4096 := by
  have rule : IsR30 (seedRun x) := drv_isR30 _ _
  have clock := alt_drv (fun p => x.testBit (p-1))
  have white : Fits (seedRun x) 1 (step true x) (12+2*k) := by
    apply fits_step rule (t := 0) (clock 0).1
    intro i _
    rw [seedRun, drv_init _ _ _ (by omega), Nat.add_sub_cancel]
  have fit := fits_rows rule (t := 1) (n := k) (L := 12) (clock.drive 0 k) white k (Nat.le_refl k)
  simpa only [show 0+2*k+1 = 1+2*k by omega] using (code_of_fits (n := 12) fit (by omega)).symm

/-- Both terminal projections occur on physical finite starts. -/
theorem last_windows :
    code (seedRun 1191106) (0+2*34+1) 12 = 3508 ∧
    code (seedRun 141962434) (0+2*34+1) 12 = 2484 := by
  rw [seed_window 1191106 34, seed_window 141962434 34]
  decide +kernel

/-- Sites 2, 7, 8, 11, 12, 14, 18 and 21 black on the initial black tick attain the
deadline. Closure rules out every earlier entry from the single failure at index 34. -/
theorem sharp : (∀ k, k < 35 → ¬ InSet (seedRun 1191106) 0 k) ∧ InSet (seedRun 1191106) 0 35 := by
  have rule : IsR30 (seedRun 1191106) := drv_isR30 _ _
  have clock : Alt (seedRun 1191106) 0 := alt_drv _
  have outside : ¬ InSet (seedRun 1191106) 0 34 := by
    unfold InSet InTrap
    rw [last_windows.1]
    decide +kernel
  refine ⟨?_, uniform_entry rule clock (by decide)⟩
  intro k hk s
  have later := stays rule clock s (34-k)
  exact outside (by simpa only [show k+(34-k)=34 by omega] using later)

end Ruliology.CellularAutomata.Rule30UniformEntry
