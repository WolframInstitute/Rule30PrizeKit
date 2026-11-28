module

public import Ruliology.CellularAutomata.Rule30Certificates.FallResidueStrip

/-!
# Rank certificates for `Rule30FallResidues` at modulus 3

For the strip of `Rule30Certificates.FallResidueStrip` with a calendar of 3 slots: the assignments that survive at
each width from three to six, and a rank certificate for each one ruled out. The kernel checks the rank tables and
the coverage of the assignments. None survives at width six (`good3`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30FallResidues
set_option maxRecDepth 80000
set_option maxHeartbeats 0

private def rest3 : List (List Nat) := [[0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 2], [0, 2, 0], [0, 2, 1], [0, 2, 2]]
private def group3_0 : List Certificate := [
  ⟨[0, 1, 0], #[0x4083004146, 0xc00810c4146, 0x410850c4006], #[0xd8, 0x1c1, 0xa8, 0x1e0, 0x150, 0x28, 0x0]⟩,
  ⟨[0, 1, 1], #[0x1086004146, 0x40810c4146, 0x410820c4006], #[0xf8, 0x1d9, 0x151, 0x1e0, 0x150, 0x28, 0x0]⟩,
]
private theorem group3_0_ok : group3_0.all (check 3 3) = true := by decide +kernel
private def certs3 := group3_0
private theorem valid3 : certs3.all (check 3 3) = true := by exact group3_0_ok
private theorem cover3 : ruledOut 3 (pairs 3) rest3 = certs3.map Certificate.labels := by decide +kernel
private theorem class3 : Classifies 3 3 rest3 :=
  classify_step (by decide) (by decide) (pairs_classify 3) valid3 cover3

private def rest4 : List (List Nat) := [[0, 0, 0, 0], [0, 0, 0, 2], [0, 0, 2, 0], [0, 0, 2, 1], [0, 0, 2, 2]]
private def group4_0 : List Certificate := [
  ⟨[0, 0, 0, 1], #[0x1890000421452081081870c7, 0x145103002041145103000107, 0x4108218200010a0c9187], #[0x1b1, 0x109, 0x152, 0x188, 0xa8, 0x61, 0x98, 0x2, 0xa, 0x110, 0x0]⟩,
  ⟨[0, 0, 1, 2], #[0x410820c20000451040c4, 0xc30410020820c3041000104, 0x410820820000410c3104], #[0x1b9, 0x151, 0x152, 0xe1, 0x2, 0x0]⟩,
  ⟨[0, 1, 2, 0], #[0x421040020c5042104000146, 0x104042186000104143186, 0xc20440020450c2104002046], #[0xe9, 0xf8, 0x150, 0x1c8, 0x151, 0x21, 0x1]⟩,
  ⟨[0, 2, 0, 1], #[0x1860c40020451861080070c7, 0x411010020851861030001c7, 0xc40421850001081c70c7], #[0x1a9, 0x172, 0x152, 0x88, 0x151, 0x0, 0x79, 0x2, 0x0]⟩,
  ⟨[0, 2, 1, 0], #[0x1021460020411021460070c8, 0x410410021481061430001c8, 0xc70421470001471840c8], #[0x1a9, 0x172, 0x150, 0x88, 0x178, 0xa8, 0x1c0, 0x30, 0x0]⟩,
  ⟨[0, 2, 1, 1], #[0x410860040c3041086004146, 0xc30810040850c4081000146, 0x850c40860000850c1086], #[0x1a9, 0xd9, 0xa8, 0xe1, 0x150, 0x101, 0x0]⟩,
  ⟨[0, 2, 1, 2], #[0x1020c40020411821490080c7, 0x41041002107208143000187, 0x1470421040001471860c7], #[0x1a9, 0x172, 0x150, 0x88, 0x15a, 0xa8, 0x99, 0x0, 0x69, 0x0]⟩,
  ⟨[0, 2, 2, 0], #[0x145104001043145104000086, 0xc3041045000103082186, 0x1040411450821071860c6], #[0x1e9, 0x152, 0x1a1, 0x41, 0x151, 0x19, 0x2, 0x0]⟩,
  ⟨[0, 2, 2, 1], #[0x1450c30010441450c3000086, 0xc30410440000c3082186, 0xc30411440820c7186106], #[0x1e9, 0x152, 0x1a1, 0x151, 0x1, 0x19, 0x2, 0x0]⟩,
  ⟨[0, 2, 2, 2], #[0x104104001043186145000087, 0xc3041107000143082187, 0x801470411040821471860c7], #[0x1e9, 0x152, 0x1a1, 0x41, 0x15a, 0x151, 0x99, 0x0]⟩,
]
private theorem group4_0_ok : group4_0.all (check 4 3) = true := by decide +kernel
private def certs4 := group4_0
private theorem valid4 : certs4.all (check 4 3) = true := by exact group4_0_ok
private theorem cover4 : ruledOut 3 (rest3) rest4 = certs4.map Certificate.labels := by decide +kernel
private theorem class4 : Classifies 4 3 rest4 :=
  classify_step (by decide) (by decide) class3 valid4 cover4

private def rest5 : List (List Nat) := [[0, 0, 0, 0, 2], [0, 0, 0, 2, 0], [0, 0, 0, 2, 1], [0, 0, 0, 2, 2]]
private def group5_0 : List Certificate := [
  ⟨[0, 0, 0, 0, 0], #[0x2070860c71041450850c30012070860c71041470850c3006, 0xc30820000410c30820001440c30820070410c3082000106, 0x411450c300008610a0c40000411472460000881070c6], #[0x1a1, 0x101, 0x151, 0x69, 0x12, 0x10a, 0x0, 0x150, 0x18, 0x80, 0x100]⟩,
]
private theorem group5_0_ok : group5_0.all (check 5 3) = true := by decide +kernel
private def certs5 := group5_0
private theorem valid5 : certs5.all (check 5 3) = true := by exact group5_0_ok
private theorem cover5 : ruledOut 3 (rest4) rest5 = certs5.map Certificate.labels := by decide +kernel
private theorem class5 : Classifies 5 3 rest5 :=
  classify_step (by decide) (by decide) class4 valid5 cover5

private def rest6 : List (List Nat) := []
private def group6_0 : List Certificate := [
  ⟨[0, 0, 0, 0, 2, 0], #[0x2081c71451452081c20820822081c71451451041040410002081c71451452081c20820822061c6145145106104041003, 0x820820820820410410000001041041051040410410000c30820820820820411c10031881041041051040410410000c3, 0x410411451450000000c30c30410411052080001c908a0820410411452080001c90ca2080410411052080001c9086083], #[0x82, 0x1a2, 0x73, 0x2, 0xa3, 0x152, 0x24, 0x151, 0x19, 0x0, 0x100]⟩,
  ⟨[0, 0, 0, 0, 2, 1], #[0x410411480881490890000001010411482081491890c30c604104114808814908914b28a1440811482881491870c3006, 0x2490852080850410810030c51c70851c80850410410001042490852080850410810030c51c70851c8085041041000106, 0x410410c30830000001040840410410c81430000861090840410410c814300008a1041490410410c8083000086109106], #[0x82, 0x1ba, 0xa8, 0x102, 0x1a, 0x98, 0x3, 0x23, 0x152, 0x6a, 0x101, 0x10]⟩,
  ⟨[0, 0, 0, 0, 2, 2], #[0x24920b0820821861860000001c71c714514518618604100024920a08208224620628a20a2432031451c7106104041003, 0x1861861451450410410000001041041051040410410000821861861451450412010021c90c30c30c50c3041041000083, 0x4104114524900020b08c0820410411051c700020b08608204104114524900020b08c0820410410c324b00020a086083], #[0x82, 0x1a2, 0x12, 0x4, 0xa3, 0x152, 0x6a, 0xcb, 0xa8, 0x19, 0xc, 0x0, 0x100]⟩,
]
private theorem group6_0_ok : group6_0.all (check 6 3) = true := by decide +kernel
private def certs6 := group6_0
private theorem valid6 : certs6.all (check 6 3) = true := by exact group6_0_ok
private theorem cover6 : ruledOut 3 (rest5) rest6 = certs6.map Certificate.labels := by decide +kernel
private theorem class6 : Classifies 6 3 rest6 :=
  classify_step (by decide) (by decide) class5 valid6 cover6

theorem good3 {a : Nat → Nat} (ha : Valid 6 3 a) : Good 6 3 a :=
  of_empty class6 ha
end Ruliology.CellularAutomata.Rule30FallResidues
