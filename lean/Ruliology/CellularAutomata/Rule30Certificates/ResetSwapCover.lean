module
public import Ruliology.CellularAutomata.Rule30ResetSwapCore

/-! Kernel-checked prefix cover for the first six/ten reset swap: 1272 leaves and at most 24 further gaps. -/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResetSwap.Certificate
open Ruliology.CellularAutomata.Rule30ResetSwap

set_option maxRecDepth 16000
set_option maxHeartbeats 16000000

-- Each leaf supplies a candidate synchronization depth to the kernel-checked verifier.
def coversss : Tree := (.fork (.fork (.fork (.hit 39) (.hit 39)) (.hit 39)) (.fork (.hit 39) (.hit 39)))
theorem coversss_ok : valid coversss (35,16907173822) = true :=
  by decide +kernel

def coversslsssss : Tree := (.fork (.fork (.fork (.fork (.hit 77) (.hit 77)) (.hit 77)) (.fork (.hit 77) (.hit 77))) (.fork (.fork (.hit 77) (.hit 77)) (.hit 77)))
theorem coversslsssss_ok : valid coversslsssss (69,290463017799644020670) = true :=
  by decide +kernel

def coversslsssslsssss : Tree := (.fork (.fork (.fork (.hit 105) (.hit 105)) (.hit 105)) (.fork (.hit 105) (.hit 105)))
theorem coversslsssslsssss_ok : valid coversslsssslsssss (103,4990116648587747780144926752702) = true :=
  by decide +kernel

def coversslsssslssssls : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 127) (.hit 127)) (.hit 127)) (.fork (.hit 127) (.hit 127))) (.fork (.fork (.hit 127) (.hit 127)) (.hit 127))) (.fork (.fork (.fork (.fork (.hit 131) (.hit 131)) (.hit 131)) (.fork (.hit 131) (.hit 131))) (.fork (.fork (.hit 130) (.hit 130)) (.hit 130))))
theorem coversslsssslssssls_ok : valid coversslsssslssssls (113,5111086734367895777008865438007230) = true :=
  by decide +kernel

def coversslsssslssssll : Tree := (.fork (.fork (.hit 114) (.hit 114)) (.hit 114))
theorem coversslsssslssssll_ok : valid coversslsssslssssll (117,82995539612390310204966310376308670) = true :=
  by decide +kernel

def coversslsssslssssl : Tree := .fork coversslsssslssssls coversslsssslssssll
theorem coversslsssslssssl_ok : valid coversslsssslssssl (107,81049152662281511869947119075262) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslssssls_ok, coversslsssslssssll_ok⟩

def coversslsssslssss : Tree := .fork coversslsssslsssss coversslsssslssssl
theorem coversslsssslssss_ok : valid coversslsssslssss (97,77970572703358849345201831870) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslsssss_ok, coversslsssslssssl_ok⟩

def coversslsssslsssl : Tree := (.fork (.fork (.fork (.fork (.hit 114) (.hit 114)) (.fork (.hit 114) (.hit 114))) (.fork (.fork (.hit 115) (.hit 115)) (.hit 115))) (.fork (.fork (.hit 108) (.hit 108)) (.hit 108)))
theorem coversslsssslsssl_ok : valid coversslsssslsssl (101,1266393010417323913248361086910) = true :=
  by decide +kernel

def coversslsssslsss : Tree := .fork coversslsssslssss coversslsssslsssl
theorem coversslsssslsss_ok : valid coversslsssslsss (91,1218290267665272301456129982) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslssss_ok, coversslsssslsssl_ok⟩

def coversslsssslsslsss : Tree := (.fork (.fork (.hit 114) (.hit 114)) (.fork (.hit 114) (.hit 114)))
theorem coversslsssslsslsss_ok : valid coversslsssslsslsss (113,5109879742829592531240838791888830) = true :=
  by decide +kernel

def coversslsssslsslsslss : Tree := (.fork (.fork (.fork (.fork (.fork (.fork (.hit 149) (.hit 149)) (.hit 149)) (.fork (.hit 149) (.hit 149))) (.fork (.fork (.hit 152) (.hit 152)) (.fork (.hit 152) (.hit 152)))) (.fork (.fork (.hit 146) (.hit 146)) (.fork (.hit 146) (.hit 146)))) (.fork (.fork (.hit 135) (.hit 135)) (.hit 135)))
theorem coversslsssslsslsslss_ok : valid coversslsssslsslsslss (129,334882295770946537494605601591841980350) = true :=
  by decide +kernel

def coversslsssslsslsslsl : Tree := (.fork (.fork (.fork (.hit 137) (.hit 137)) (.hit 137)) (.fork (.hit 137) (.hit 137)))
theorem coversslsssslsslsslsl_ok : valid coversslsssslsslsslsl (133,5439117799585023489445224713068365152190) = true :=
  by decide +kernel

def coversslsssslsslssls : Tree := .fork coversslsssslsslsslss coversslsssslsslsslsl
theorem coversslsssslsslssls_ok : valid coversslsssslsslssls (123,5233752816287401014461450642316525502) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslsslsslss_ok, coversslsssslsslsslsl_ok⟩

def coversslsssslsslssll : Tree := (.fork (.fork (.hit 123) (.hit 123)) (.hit 123))
theorem coversslsssslsslssll_ok : valid coversslsssslsslssll (127,84987432563382353388689874259137200062) = true :=
  by decide +kernel

def coversslsssslsslssl : Tree := .fork coversslsssslsslssls coversslsssslsslssll
theorem coversslsssslsslssl_ok : valid coversslsssslsslssl (117,82994332620852006959198283730190270) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslsslssls_ok, coversslsssslsslssll_ok⟩

def coversslsssslsslss : Tree := .fork coversslsssslsslsss coversslsssslsslssl
theorem coversslsssslsslss_ok : valid coversslsssslsslss (107,79842161123978266101920472956862) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslsslsss_ok, coversslsssslsslssl_ok⟩

def coversslsssslsslsl : Tree := (.fork (.fork (.hit 109) (.hit 109)) (.hit 109))
theorem coversslsssslsslsl_ok : valid coversslsssslsslsl (111,1296786737343078491538755550117822) = true :=
  by decide +kernel

def coversslsssslssls : Tree := .fork coversslsssslsslss coversslsssslsslsl
theorem coversslsssslssls_ok : valid coversslsssslssls (101,1247823909828043209124874223550) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslsslss_ok, coversslsssslsslsl_ok⟩

def coversslsssslssll : Tree := (.fork (.fork (.fork (.hit 108) (.hit 108)) (.hit 108)) (.fork (.hit 108) (.hit 108)))
theorem coversslsssslssll_ok : valid coversslsssslssll (105,20262582913251484231575422304190) = true :=
  by decide +kernel

def coversslsssslssl : Tree := .fork coversslsssslssls coversslsssslssll
theorem coversslsssslssl_ok : valid coversslsssslssl (95,19787390856945976424942993342) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslssls_ok, coversslsssslssll_ok⟩

def coversslsssslss : Tree := .fork coversslsssslsss coversslsssslssl
theorem coversslsssslss_ok : valid coversslsssslss (85,19035854607560160147603390) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslsss_ok, coversslsssslssl_ok⟩

def coversslsssslsl : Tree := (.fork (.fork (.fork (.hit 94) (.hit 94)) (.hit 94)) (.fork (.hit 94) (.hit 94)))
theorem coversslsssslsl_ok : valid coversslsssslsl (89,309178051315071162077085630) = true :=
  by decide +kernel

def coversslssssls : Tree := .fork coversslsssslss coversslsssslsl
theorem coversslssssls_ok : valid coversslssssls (79,297504403533407939657662) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssslss_ok, coversslsssslsl_ok⟩

def coversslssssll : Tree := (.fork (.fork (.fork (.fork (.hit 94) (.hit 94)) (.hit 94)) (.fork (.hit 94) (.hit 94))) (.fork (.fork (.hit 94) (.hit 94)) (.fork (.hit 94) (.hit 94))))
theorem coversslssssll_ok : valid coversslssssll (83,4830976227088267344805822) = true :=
  by decide +kernel

def coversslssssl : Tree := .fork coversslssssls coversslssssll
theorem coversslssssl_ok : valid coversslssssl (73,4717681595489936408510) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslssssls_ok, coversslssssll_ok⟩

def coversslssss : Tree := .fork coversslsssss coversslssssl
theorem coversslssss_ok : valid coversslssss (63,4538484657145970622) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssss_ok, coversslssssl_ok⟩

def coversslsssls : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 91) (.hit 91)) (.fork (.hit 91) (.hit 91))) (.fork (.fork (.hit 95) (.hit 95)) (.fork (.hit 95) (.hit 95)))) (.fork (.fork (.fork (.hit 94) (.hit 94)) (.hit 94)) (.fork (.hit 94) (.hit 94)))) (.fork (.fork (.hit 82) (.hit 82)) (.hit 82)))
theorem coversslsssls_ok : valid coversslsssls (73,4648506305213525589950) = true :=
  by decide +kernel

def coversslsssll : Tree := (.fork (.fork (.hit 78) (.hit 78)) (.fork (.hit 78) (.hit 78)))
theorem coversslsssll_ok : valid coversslsssll (77,75484003548258203795390) = true :=
  by decide +kernel

def coversslsssl : Tree := .fork coversslsssls coversslsssll
theorem coversslsssl_ok : valid coversslsssl (67,73713774933556789182) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsssls_ok, coversslsssll_ok⟩

def coversslsss : Tree := .fork coversslssss coversslsssl
theorem coversslsss_ok : valid coversslsss (57,70913826794438590) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslssss_ok, coversslsssl_ok⟩

def coversslsslss : Tree := (.fork (.fork (.fork (.fork (.hit 85) (.hit 85)) (.fork (.hit 85) (.hit 85))) (.fork (.fork (.fork (.hit 92) (.hit 92)) (.hit 92)) (.fork (.hit 92) (.hit 92)))) (.fork (.fork (.fork (.hit 86) (.hit 86)) (.hit 86)) (.fork (.hit 86) (.hit 86))))
theorem coversslsslss_ok : valid coversslsslss (73,4647425441302956670910) = true :=
  by decide +kernel

def coversslsslsl : Tree := (.fork (.fork (.fork (.hit 83) (.hit 83)) (.fork (.hit 83) (.hit 83))) (.fork (.fork (.fork (.fork (.fork (.hit 101) (.hit 101)) (.hit 101)) (.fork (.hit 101) (.hit 101))) (.fork (.fork (.hit 101) (.hit 101)) (.hit 101))) (.fork (.fork (.hit 94) (.hit 94)) (.hit 94))))
theorem coversslsslsl_ok : valid coversslsslsl (77,75482922684347634876350) = true :=
  by decide +kernel

def coversslssls : Tree := .fork coversslsslss coversslsslsl
theorem coversslssls_ok : valid coversslssls (67,72632911022987870142) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsslss_ok, coversslsslsl_ok⟩

def coversslssll : Tree := (.fork (.hit 65) (.hit 65))
theorem coversslssll_ok : valid coversslssll (71,1179437555445560967102) = true :=
  by decide +kernel

def coversslssl : Tree := .fork coversslssls coversslssll
theorem coversslssl_ok : valid coversslssl (61,1151777737363357630) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslssls_ok, coversslssll_ok⟩

def coversslss : Tree := .fork coversslsss coversslssl
theorem coversslss_ok : valid coversslss (51,1108032570195902) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsss_ok, coversslssl_ok⟩

def coversslslsss : Tree := (.fork (.fork (.fork (.hit 76) (.hit 76)) (.hit 76)) (.fork (.hit 76) (.hit 76)))
theorem coversslslsss_ok : valid coversslslsss (73,4647408552804354031550) = true :=
  by decide +kernel

def coversslslssls : Tree := (.fork (.fork (.fork (.fork (.hit 92) (.hit 92)) (.hit 92)) (.fork (.hit 92) (.hit 92))) (.fork (.fork (.hit 89) (.hit 89)) (.hit 89)))
theorem coversslslssls_ok : valid coversslslssls (83,4760070456802537084223422) = true :=
  by decide +kernel

def coversslslsslls : Tree := (.fork (.fork (.hit 94) (.hit 94)) (.fork (.hit 94) (.hit 94)))
theorem coversslslsslls_ok : valid coversslslsslls (93,4874313271864528852800700350) = true :=
  by decide +kernel

def coversslslsslll : Tree := (.fork (.fork (.fork (.fork (.fork (.fork (.hit 120) (.hit 120)) (.hit 120)) (.fork (.hit 120) (.hit 120))) (.fork (.fork (.hit 120) (.hit 120)) (.fork (.hit 120) (.hit 120)))) (.fork (.fork (.hit 109) (.hit 109)) (.hit 109))) (.fork (.fork (.hit 104) (.hit 104)) (.hit 104)))
theorem coversslslsslll_ok : valid coversslslsslll (97,79150715628987345346748153790) = true :=
  by decide +kernel

def coversslslssll : Tree := .fork coversslslsslls coversslslsslll
theorem coversslslssll_ok : valid coversslslssll (87,77295619633680287566593982) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslslsslls_ok, coversslslsslll_ok⟩

def coversslslssl : Tree := .fork coversslslssls coversslslssll
theorem coversslslssl_ok : valid coversslslssl (77,75482905795849032236990) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslslssls_ok, coversslslssll_ok⟩

def coversslslss : Tree := .fork coversslslsss coversslslssl
theorem coversslslss_ok : valid coversslslss (67,72616022524385230782) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslslsss_ok, coversslslssl_ok⟩

def coversslslsl : Tree := (.fork (.fork (.fork (.fork (.hit 81) (.hit 81)) (.hit 81)) (.fork (.hit 81) (.hit 81))) (.fork (.fork (.fork (.hit 83) (.hit 83)) (.hit 83)) (.fork (.hit 83) (.hit 83))))
theorem coversslslsl_ok : valid coversslslsl (71,1179420666946958327742) = true :=
  by decide +kernel

def coversslsls : Tree := .fork coversslslss coversslslsl
theorem coversslsls_ok : valid coversslsls (61,1134889238760718270) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslslss_ok, coversslslsl_ok⟩

def coversslslls : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 88) (.hit 88)) (.hit 88)) (.fork (.hit 88) (.hit 88))) (.fork (.fork (.fork (.fork (.hit 98) (.hit 98)) (.hit 98)) (.fork (.hit 98) (.hit 98))) (.fork (.fork (.hit 93) (.hit 93)) (.hit 93)))) (.fork (.fork (.hit 79) (.hit 79)) (.hit 79)))
theorem coversslslls_ok : valid coversslslls (71,1162126844377855623102) = true :=
  by decide +kernel

def coversslslll : Tree := (.fork (.fork (.fork (.fork (.hit 83) (.hit 83)) (.hit 83)) (.fork (.hit 83) (.hit 83))) (.fork (.fork (.hit 85) (.hit 85)) (.fork (.hit 85) (.hit 85))))
theorem coversslslll_ok : valid coversslslll (75,18871001155139025174462) = true :=
  by decide +kernel

def coversslsll : Tree := .fork coversslslls coversslslll
theorem coversslsll_ok : valid coversslsll (65,18428711807863422910) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslslls_ok, coversslslll_ok⟩

def coversslsl : Tree := .fork coversslsls coversslsll
theorem coversslsl_ok : valid coversslsl (55,17996531172835262) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslsls_ok, coversslsll_ok⟩

def coverssls : Tree := .fork coversslss coversslsl
theorem coverssls_ok : valid coverssls (45,17317035442110) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslss_ok, coversslsl_ok⟩

def coverssllsss : Tree := (.fork (.fork (.fork (.fork (.hit 76) (.hit 76)) (.hit 76)) (.fork (.hit 76) (.hit 76))) (.fork (.fork (.hit 73) (.hit 73)) (.hit 73)))
theorem coverssllsss_ok : valid coverssllsss (67,72615758641594564542) = true :=
  by decide +kernel

def coverssllsslsss : Tree := (.fork (.fork (.fork (.fork (.hit 99) (.hit 99)) (.hit 99)) (.fork (.hit 99) (.hit 99))) (.fork (.fork (.fork (.hit 103) (.hit 103)) (.hit 103)) (.fork (.hit 103) (.hit 103))))
theorem coverssllsslsss_ok : valid coverssllsslsss (89,304572566916322267047591870) = true :=
  by decide +kernel

def coverssllsslssls : Tree := (.fork (.fork (.hit 99) (.hit 99)) (.fork (.hit 99) (.hit 99)))
theorem coverssllsslssls_ok : valid coverssllsslssls (99,311955977457010806472902115262) = true :=
  by decide +kernel

def coverssllsslssll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 117) (.hit 117)) (.hit 117)) (.fork (.hit 117) (.hit 117))) (.fork (.fork (.hit 118) (.hit 118)) (.hit 118))) (.fork (.fork (.fork (.hit 117) (.hit 117)) (.hit 117)) (.fork (.hit 117) (.hit 117))))
theorem coverssllsslssll_ok : valid coverssllsslssll (103,5065645728312871062085539135422) = true :=
  by decide +kernel

def coverssllsslssl : Tree := .fork coverssllsslssls coverssllsslssll
theorem coverssllsslssl_ok : valid coverssllsslssl (93,4946847714236498297919307710) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllsslssls_ok, coverssllsslssll_ok⟩

def coverssllsslss : Tree := .fork coverssllsslsss coverssllsslssl
theorem coverssllsslss_ok : valid coverssllsslss (83,4758963651894231720460222) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllsslsss_ok, coverssllsslssl_ok⟩

def coverssllsslsls : Tree := (.fork (.fork (.fork (.fork (.hit 105) (.hit 105)) (.fork (.hit 105) (.hit 105))) (.fork (.fork (.fork (.hit 112) (.hit 112)) (.hit 112)) (.fork (.hit 112) (.hit 112)))) (.fork (.fork (.hit 99) (.hit 99)) (.hit 99)))
theorem coverssllsslsls_ok : valid coverssllsslsls (93,4874312165059620547436937150) = true :=
  by decide +kernel

def coverssllsslsll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 111) (.hit 111)) (.hit 111)) (.fork (.hit 111) (.hit 111))) (.fork (.fork (.hit 114) (.hit 114)) (.fork (.hit 114) (.hit 114)))) (.fork (.fork (.hit 103) (.hit 103)) (.hit 103)))
theorem coverssllsslsll_ok : valid coverssllsslsll (97,79150714522182437041384390590) = true :=
  by decide +kernel

def coverssllsslsl : Tree := .fork coverssllsslsls coverssllsslsll
theorem coverssllsslsl_ok : valid coverssllsslsl (87,77294512828771982202830782) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllsslsls_ok, coverssllsslsll_ok⟩

def coverssllssls : Tree := .fork coverssllsslss coverssllsslsl
theorem coverssllssls_ok : valid coverssllssls (77,74376100887543668473790) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllsslss_ok, coverssllsslsl_ok⟩

def coverssllssll : Tree := (.fork (.fork (.fork (.hit 85) (.hit 85)) (.hit 85)) (.fork (.hit 85) (.hit 85)))
theorem coverssllssll_ok : valid coverssllssll (81,1207744056776258519760830) = true :=
  by decide +kernel

def coverssllssl : Tree := .fork coverssllssls coverssllssll
theorem coverssllssl_ok : valid coverssllssl (71,1179420403064167661502) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllssls_ok, coverssllssll_ok⟩

def coverssllss : Tree := .fork coverssllsss coverssllssl
theorem coverssllss_ok : valid coverssllss (61,1134625355970052030) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllsss_ok, coverssllssl_ok⟩

def coverssllsl : Tree := (.fork (.fork (.fork (.hit 69) (.hit 69)) (.hit 69)) (.fork (.hit 69) (.hit 69)))
theorem coverssllsl_ok : valid coverssllsl (65,18428447925072756670) = true :=
  by decide +kernel

def coversslls : Tree := .fork coverssllss coverssllsl
theorem coversslls_ok : valid coversslls (55,17732648382169022) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllss_ok, coverssllsl_ok⟩

def coversslllssss : Tree := (.fork (.fork (.fork (.fork (.fork (.fork (.hit 104) (.hit 104)) (.hit 104)) (.fork (.hit 104) (.hit 104))) (.fork (.fork (.hit 103) (.hit 103)) (.hit 103))) (.fork (.fork (.hit 97) (.hit 97)) (.hit 97))) (.fork (.fork (.hit 92) (.hit 92)) (.hit 92)))
theorem coversslllssss_ok : valid coversslllssss (83,4758946087855684975525822) = true :=
  by decide +kernel

def coversslllsssl : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 103) (.hit 103)) (.hit 103)) (.fork (.hit 103) (.hit 103))) (.fork (.fork (.hit 101) (.hit 101)) (.hit 101))) (.fork (.fork (.fork (.hit 101) (.hit 101)) (.hit 101)) (.fork (.hit 101) (.hit 101))))
theorem coversslllsssl_ok : valid coversslllsssl (87,77294495264733435457896382) = true :=
  by decide +kernel

def coversslllsss : Tree := .fork coversslllssss coversslllsssl
theorem coversslllsss_ok : valid coversslllsss (77,74358536848996923539390) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllssss_ok, coversslllsssl_ok⟩

def coversslllssl : Tree := (.fork (.fork (.fork (.fork (.hit 92) (.hit 92)) (.hit 92)) (.fork (.hit 92) (.hit 92))) (.fork (.fork (.hit 89) (.hit 89)) (.hit 89)))
theorem coversslllssl_ok : valid coversslllssl (81,1207726492737711774826430) = true :=
  by decide +kernel

def coversslllss : Tree := .fork coversslllsss coversslllssl
theorem coversslllss_ok : valid coversslllss (71,1161856364517422727102) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllsss_ok, coversslllssl_ok⟩

def coversslllslsss : Tree := (.fork (.fork (.fork (.hit 96) (.hit 96)) (.hit 96)) (.fork (.hit 96) (.hit 96)))
theorem coversslllslsss_ok : valid coversslllslsss (93,4873161070665382524671164350) = true :=
  by decide +kernel

def coversslllslssls : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 118) (.hit 118)) (.hit 118)) (.fork (.hit 118) (.hit 118))) (.fork (.fork (.hit 115) (.hit 115)) (.hit 115))) (.fork (.fork (.hit 114) (.hit 114)) (.fork (.hit 114) (.hit 114))))
theorem coversslllslssls_ok : valid coversslllslssls (103,4991295639312177129818343538622) = true :=
  by decide +kernel

def coversslllslssll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 122) (.hit 122)) (.hit 122)) (.fork (.hit 122) (.hit 122))) (.fork (.fork (.hit 120) (.hit 120)) (.hit 120))) (.fork (.fork (.fork (.fork (.hit 125) (.hit 125)) (.hit 125)) (.fork (.hit 125) (.hit 125))) (.fork (.fork (.hit 125) (.hit 125)) (.hit 125))))
theorem coversslllslssll_ok : valid coversslllslssll (107,81050331653005941219620535861182) = true :=
  by decide +kernel

def coversslllslssl : Tree := .fork coversslllslssls coversslllslssll
theorem coversslllslssl_ok : valid coversslllslssl (97,79149563427788199018618617790) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllslssls_ok, coversslllslssll_ok⟩

def coversslllslss : Tree := .fork coversslllslsss coversslllslssl
theorem coversslllslss_ok : valid coversslllslss (87,76143418434533959437057982) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllslsss_ok, coversslllslssl_ok⟩

def coversslllslsl : Tree := (.fork (.fork (.fork (.hit 93) (.hit 93)) (.hit 93)) (.fork (.hit 93) (.hit 93)))
theorem coversslllslsl_ok : valid coversslllslsl (91,1236712205264577967154986942) = true :=
  by decide +kernel

def coversslllsls : Tree := .fork coversslllslss coversslllslsl
theorem coversslllsls_ok : valid coversslllsls (81,1190017618426950605275070) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllslss_ok, coversslllslsl_ok⟩

def coversslllsll : Tree := (.fork (.fork (.fork (.fork (.hit 93) (.hit 93)) (.hit 93)) (.fork (.hit 93) (.hit 93))) (.fork (.fork (.fork (.fork (.hit 104) (.hit 104)) (.hit 104)) (.fork (.hit 104) (.hit 104))) (.fork (.fork (.hit 105) (.hit 105)) (.fork (.hit 105) (.hit 105)))))
theorem coversslllsll_ok : valid coversslllsll (85,19323904912646388225867710) = true :=
  by decide +kernel

def coversslllsl : Tree := .fork coversslllsls coversslllsll
theorem coversslllsl_ok : valid coversslllsl (75,18870730675278592278462) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllsls_ok, coversslllsll_ok⟩

def coverssllls : Tree := .fork coversslllss coversslllsl
theorem coverssllls_ok : valid coverssllls (65,18158231947430526910) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllss_ok, coversslllsl_ok⟩

def coverssllllss : Tree := (.fork (.fork (.fork (.fork (.hit 92) (.hit 92)) (.hit 92)) (.fork (.hit 92) (.hit 92))) (.fork (.fork (.fork (.hit 95) (.hit 95)) (.hit 95)) (.fork (.hit 95) (.hit 95))))
theorem coverssllllss_ok : valid coverssllllss (81,1189740917265844962000830) = true :=
  by decide +kernel

def coverssllllsls : Tree := (.fork (.fork (.fork (.fork (.hit 102) (.hit 102)) (.hit 102)) (.fork (.hit 102) (.hit 102))) (.fork (.fork (.hit 100) (.hit 100)) (.hit 100)))
theorem coverssllllsls_ok : valid coverssllllsls (91,1218578041269197423891120062) = true :=
  by decide +kernel

def coverssllllslls : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 116) (.hit 116)) (.hit 116)) (.fork (.hit 116) (.hit 116))) (.fork (.fork (.hit 113) (.hit 113)) (.hit 113))) (.fork (.fork (.hit 108) (.hit 108)) (.hit 108)))
theorem coverssllllslls_ok : valid coverssllllslls (101,1247824197601647134247309213630) = true :=
  by decide +kernel

def coverssllllslll : Tree := (.fork (.fork (.fork (.fork (.hit 113) (.hit 113)) (.hit 113)) (.fork (.hit 113) (.hit 113))) (.fork (.fork (.fork (.fork (.hit 124) (.hit 124)) (.hit 124)) (.fork (.hit 124) (.hit 124))) (.fork (.fork (.hit 122) (.hit 122)) (.hit 122))))
theorem coverssllllslll_ok : valid coverssllllslll (105,20262583201025088156697857294270) = true :=
  by decide +kernel

def coverssllllsll : Tree := .fork coverssllllslls coverssllllslll
theorem coverssllllsll_ok : valid coverssllllsll (95,19787678630549901547377983422) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllllslls_ok, coverssllllslll_ok⟩

def coverssllllsl : Tree := .fork coverssllllsls coverssllllsll
theorem coverssllllsl_ok : valid coverssllllsl (85,19323628211485282582593470) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllllsls_ok, coverssllllsll_ok⟩

def coversslllls : Tree := .fork coverssllllss coverssllllsl
theorem coversslllls_ok : valid coversslllls (75,18594029514172949004222) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllllss_ok, coverssllllsl_ok⟩

def coversslllllssss : Tree := (.fork (.fork (.fork (.fork (.hit 116) (.hit 116)) (.fork (.hit 116) (.hit 116))) (.fork (.fork (.hit 116) (.hit 116)) (.hit 116))) (.fork (.fork (.hit 111) (.hit 111)) (.hit 111)))
theorem coversslllllssss_ok : valid coversslllllssss (103,4990116653019362733088648921022) = true :=
  by decide +kernel

def coversslllllsssl : Tree := (.fork (.fork (.fork (.fork (.hit 118) (.hit 118)) (.hit 118)) (.fork (.hit 118) (.hit 118))) (.fork (.fork (.hit 116) (.hit 116)) (.hit 116)))
theorem coversslllllsssl_ok : valid coversslllllsssl (107,81049152666713126822890841243582) = true :=
  by decide +kernel

def coversslllllsss : Tree := .fork coversslllllssss coversslllllsssl
theorem coversslllllsss_ok : valid coversslllllsss (97,77970577134973802288924000190) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllssss_ok, coversslllllsssl_ok⟩

def coversslllllsslss : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 127) (.hit 127)) (.hit 127)) (.fork (.hit 127) (.hit 127))) (.fork (.fork (.hit 126) (.hit 126)) (.hit 126))) (.fork (.fork (.fork (.fork (.hit 132) (.hit 132)) (.hit 132)) (.fork (.hit 132) (.hit 132))) (.fork (.fork (.hit 130) (.hit 130)) (.hit 130))))
theorem coversslllllsslss_ok : valid coversslllllsslss (113,5109898311934613426897906000920510) = true :=
  by decide +kernel

def coversslllllsslslssssss : Tree := (.fork (.fork (.fork (.fork (.fork (.fork (.hit 174) (.hit 174)) (.hit 174)) (.fork (.hit 174) (.hit 174))) (.fork (.fork (.hit 174) (.hit 174)) (.hit 174))) (.fork (.fork (.hit 165) (.hit 165)) (.hit 165))) (.fork (.fork (.hit 159) (.hit 159)) (.hit 159)))
theorem coversslllllsslslssssss_ok : valid coversslllllsslslssssss (153,5618371869700887875297708955092514739261996990) = true :=
  by decide +kernel

def coversslllllsslslsssssl : Tree := (.fork (.fork (.fork (.hit 159) (.hit 159)) (.hit 159)) (.fork (.hit 159) (.hit 159)))
theorem coversslllllsslslsssssl_ok : valid coversslllllsslslsssssl (157,91253233432058480738794867122062222922226794430) = true :=
  by decide +kernel

def coversslllllsslslsssss : Tree := .fork coversslllllsslslssssss coversslllllsslslsssssl
theorem coversslllllsslslsssss_ok : valid coversslllllsslslsssss (147,87787060465293336196850823475721085778853822) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslslssssss_ok, coversslllllsslslsssssl_ok⟩

def coversslllllsslslssssl : Tree := (.fork (.fork (.hit 150) (.hit 150)) (.hit 150))
theorem coversslllllsslslssssl_ok : valid coversslllllsslslssssl (151,1425831772377130724688993919834622776137678782) = true :=
  by decide +kernel

def coversslllllsslslssss : Tree := .fork coversslllllsslslsssss coversslllllsslslssssl
theorem coversslllllsslslssss_ok : valid coversslllllsslslssss (141,1371672820987171523399915169208684943179710) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslslsssss_ok, coversslllllsslslssssl_ok⟩

def coversslllllsslslsssl : Tree := (.fork (.fork (.fork (.hit 151) (.hit 151)) (.fork (.hit 151) (.hit 151))) (.fork (.fork (.hit 156) (.hit 156)) (.fork (.hit 156) (.hit 156))))
theorem coversslllllsslslsssl_ok : valid coversslllllsslslsssl (145,22278621444609630718589651049816523855036350) = true :=
  by decide +kernel

def coversslllllsslslsss : Tree := .fork coversslllllsslslssss coversslllllsslslsssl
theorem coversslllllsslslsss_ok : valid coversslllllsslslsss (135,21432389044887700377244726919428680122302) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslslssss_ok, coversslllllsslslsssl_ok⟩

def coversslllllsslslssl : Tree := (.fork (.fork (.hit 138) (.hit 138)) (.hit 138))
theorem coversslllllsslslssl_ok : valid coversslllllsslslssl (139,348103461288988625302084350053926163120062) = true :=
  by decide +kernel

def coversslllllsslslss : Tree := .fork coversslllllsslslsss coversslllllsslslssl
theorem coversslllllsslslss_ok : valid coversslllllsslslss (129,334882295789515642515501258659051012030) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslslsss_ok, coversslllllsslslssl_ok⟩

def coversslllllsslslsl : Tree := (.fork (.fork (.fork (.hit 140) (.hit 140)) (.fork (.hit 140) (.hit 140))) (.fork (.fork (.hit 142) (.hit 142)) (.hit 142)))
theorem coversslllllsslslsl_ok : valid coversslllllsslslsl (133,5439117799603592594466120370135574183870) = true :=
  by decide +kernel

def coversslllllsslsls : Tree := .fork coversslllllsslslss coversslllllsslslsl
theorem coversslllllsslsls_ok : valid coversslllllsslsls (123,5233752834856506035357107709525557182) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslslss_ok, coversslllllsslslsl_ok⟩

def coversslllllsslsllss : Tree := (.fork (.fork (.fork (.fork (.fork (.fork (.hit 162) (.hit 162)) (.hit 162)) (.fork (.hit 162) (.hit 162))) (.fork (.fork (.hit 160) (.hit 160)) (.hit 160))) (.fork (.fork (.hit 155) (.hit 155)) (.fork (.hit 155) (.hit 155)))) (.fork (.fork (.hit 150) (.hit 150)) (.fork (.hit 150) (.hit 150))))
theorem coversslllllsslsllss_ok : valid coversslllllsslsllss (139,342919472105427453397759502518832819273662) = true :=
  by decide +kernel

def coversslllllsslsllsl : Tree := (.fork (.fork (.fork (.fork (.hit 154) (.hit 154)) (.hit 154)) (.fork (.hit 154) (.hit 154))) (.fork (.fork (.hit 149) (.hit 149)) (.hit 149)))
theorem coversslllllsslsllsl_ok : valid coversslllllsslsllsl (143,5569656628011042252195193472670792547237822) = true :=
  by decide +kernel

def coversslllllsslslls : Tree := .fork coversslllllsslsllss coversslllllsslsllsl
theorem coversslllllsslslls_ok : valid coversslllllsslslls (133,5359364119856497642091891946518753509310) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslsllss_ok, coversslllllsslsllsl_ok⟩

def coversslllllsslslll : Tree := (.fork (.fork (.fork (.hit 139) (.hit 139)) (.hit 139)) (.fork (.hit 139) (.hit 139)))
theorem coversslllllsslslll_ok : valid coversslllllsslslll (137,87027132180881728873301797730143124258750) = true :=
  by decide +kernel

def coversslllllsslsll : Tree := .fork coversslllllsslslls coversslllllsslslll
theorem coversslllllsslsll_ok : valid coversslllllsslsll (127,84987432581951458409585531326346231742) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslslls_ok, coversslllllsslslll_ok⟩

def coversslllllsslsl : Tree := .fork coversslllllsslsls coversslllllsslsll
theorem coversslllllsslsl_ok : valid coversslllllsslsl (117,82994351189957027854855350939221950) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslsls_ok, coversslllllsslsll_ok⟩

def coversslllllssls : Tree := .fork coversslllllsslss coversslllllsslsl
theorem coversslllllssls_ok : valid coversslllllssls (107,79860730228999161758987681988542) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsslss_ok, coversslllllsslsl_ok⟩

def coversslllllssll : Tree := (.fork (.fork (.hit 109) (.hit 109)) (.hit 109))
theorem coversslllllssll_ok : valid coversslllllssll (111,1296805306448099387195822759149502) = true :=
  by decide +kernel

def coversslllllssl : Tree := .fork coversslllllssls coversslllllssll
theorem coversslllllssl_ok : valid coversslllllssl (101,1266393014848938866192083255230) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllssls_ok, coversslllllssll_ok⟩

def coversslllllss : Tree := .fork coversslllllsss coversslllllssl
theorem coversslllllss_ok : valid coversslllllss (91,1218294699280225245178298302) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsss_ok, coversslllllssl_ok⟩

def coversslllllslss : Tree := (.fork (.fork (.fork (.hit 112) (.hit 112)) (.hit 112)) (.fork (.fork (.fork (.fork (.hit 128) (.hit 128)) (.hit 128)) (.fork (.hit 128) (.hit 128))) (.fork (.fork (.hit 124) (.hit 124)) (.hit 124))))
theorem coversslllllslss_ok : valid coversslllllslss (107,79842161128409881054864195125182) = true :=
  by decide +kernel

def coversslllllslslss : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 142) (.hit 142)) (.fork (.hit 142) (.hit 142))) (.fork (.fork (.hit 146) (.hit 146)) (.fork (.hit 146) (.hit 146)))) (.fork (.fork (.hit 140) (.hit 140)) (.fork (.hit 140) (.hit 140)))) (.fork (.fork (.hit 130) (.hit 130)) (.hit 130)))
theorem coversslllllslslss_ok : valid coversslllllslslss (123,5232535871711186345850966750961532862) = true :=
  by decide +kernel

def coversslllllslslsl : Tree := (.fork (.fork (.fork (.fork (.hit 138) (.hit 138)) (.hit 138)) (.fork (.hit 138) (.hit 138))) (.fork (.fork (.hit 134) (.hit 134)) (.hit 134)))
theorem coversslllllslslsl_ok : valid coversslllllslslsl (127,84986215618806138720079390367782207422) = true :=
  by decide +kernel

def coversslllllslsls : Tree := .fork coversslllllslslss coversslllllslslsl
theorem coversslllllslsls_ok : valid coversslllllslsls (117,81777388044637338348714392375197630) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllslslss_ok, coversslllllslslsl_ok⟩

def coversslllllslsll : Tree := (.fork (.fork (.fork (.fork (.hit 129) (.hit 129)) (.hit 129)) (.fork (.hit 129) (.hit 129))) (.fork (.fork (.hit 129) (.hit 129)) (.hit 129)))
theorem coversslllllslsll_ok : valid coversslllllslsll (121,1327928634092995969196033511388020670) = true :=
  by decide +kernel

def coversslllllslsl : Tree := .fork coversslllllslsls coversslllllslsll
theorem coversslllllslsl_ok : valid coversslllllslsl (111,1296786737347510106491699272286142) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllslsls_ok, coversslllllslsll_ok⟩

def coversslllllsls : Tree := .fork coversslllllslss coversslllllslsl
theorem coversslllllsls_ok : valid coversslllllsls (101,1247823914259658162068596391870) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllslss_ok, coversslllllslsl_ok⟩

def coversslllllsll : Tree := (.fork (.fork (.fork (.hit 111) (.hit 111)) (.fork (.hit 111) (.hit 111))) (.fork (.fork (.fork (.hit 117) (.hit 117)) (.hit 117)) (.fork (.hit 117) (.hit 117))))
theorem coversslllllsll_ok : valid coversslllllsll (105,20262582917683099184519144472510) = true :=
  by decide +kernel

def coversslllllsl : Tree := .fork coversslllllsls coversslllllsll
theorem coversslllllsl_ok : valid coversslllllsl (95,19787395288560929368665161662) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllsls_ok, coversslllllsll_ok⟩

def coverssllllls : Tree := .fork coversslllllss coversslllllsl
theorem coverssllllls_ok : valid coverssllllls (85,19040286222513103869771710) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllllss_ok, coversslllllsl_ok⟩

def coverssllllll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 103) (.hit 103)) (.hit 103)) (.fork (.hit 103) (.hit 103))) (.fork (.fork (.hit 106) (.hit 106)) (.fork (.hit 106) (.hit 106)))) (.fork (.fork (.fork (.hit 101) (.hit 101)) (.hit 101)) (.fork (.hit 101) (.hit 101))))
theorem coverssllllll_ok : valid coverssllllll (89,309182482930024105799253950) = true :=
  by decide +kernel

def coversslllll : Tree := .fork coverssllllls coverssllllll
theorem coversslllll_ok : valid coversslllll (79,301936018486351661825982) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllllls_ok, coverssllllll_ok⟩

def coverssllll : Tree := .fork coversslllls coversslllll
theorem coverssllll_ok : valid coverssllll (69,294859393053073801150) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslllls_ok, coversslllll_ok⟩

def coversslll : Tree := .fork coverssllls coverssllll
theorem coversslll_ok : valid coversslll (59,287948626024398782) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssllls_ok, coverssllll_ok⟩

def coverssll : Tree := .fork coversslls coversslll
theorem coverssll_ok : valid coverssll (49,281199826108350) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversslls_ok, coversslll_ok⟩

def coverssl : Tree := .fork coverssls coverssll
theorem coverssl_ok : valid coverssl (39,274605211582) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverssls_ok, coverssll_ok⟩

def coverss : Tree := .fork coversss coverssl
theorem coverss_ok : valid coverss (29,264175550) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversss_ok, coverssl_ok⟩

def coverslsssssss : Tree := (.fork (.fork (.fork (.hit 82) (.hit 82)) (.fork (.hit 82) (.hit 82))) (.fork (.fork (.fork (.hit 91) (.hit 91)) (.fork (.hit 91) (.hit 91))) (.fork (.fork (.fork (.hit 97) (.hit 97)) (.hit 97)) (.fork (.hit 97) (.hit 97)))))
theorem coverslsssssss_ok : valid coverslsssssss (75,18589633138915492691902) = true :=
  by decide +kernel

def coverslssssssl : Tree := (.fork (.fork (.hit 79) (.hit 79)) (.fork (.hit 79) (.hit 79)))
theorem coverslssssssl_ok : valid coverslssssssl (79,301931622111094205513662) = true :=
  by decide +kernel

def coverslssssss : Tree := .fork coverslsssssss coverslssssssl
theorem coverslssssss_ok : valid coverslssssss (69,290463017795617488830) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsssssss_ok, coverslssssssl_ok⟩

def coverslssssslss : Tree := (.fork (.fork (.fork (.hit 89) (.hit 89)) (.hit 89)) (.fork (.hit 89) (.hit 89)))
theorem coverslssssslss_ok : valid coverslssssslss (85,19035854607560156121071550) = true :=
  by decide +kernel

def coverslssssslslss : Tree := (.fork (.fork (.fork (.fork (.hit 114) (.hit 114)) (.fork (.hit 114) (.hit 114))) (.fork (.fork (.hit 115) (.hit 115)) (.hit 115))) (.fork (.fork (.hit 111) (.hit 111)) (.fork (.hit 111) (.hit 111))))
theorem coverslssssslslss_ok : valid coverslssssslslss (101,1247533767631335698118918209470) = true :=
  by decide +kernel

def coverslssssslslsl : Tree := (.fork (.fork (.fork (.fork (.hit 113) (.hit 113)) (.hit 113)) (.fork (.hit 113) (.hit 113))) (.fork (.fork (.fork (.hit 118) (.hit 118)) (.hit 118)) (.fork (.hit 118) (.hit 118))))
theorem coverslssssslslsl_ok : valid coverslssssslslsl (105,20262292771054776720569466290110) = true :=
  by decide +kernel

def coverslssssslsls : Tree := .fork coverslssssslslss coverslssssslslsl
theorem coverslssssslsls_ok : valid coverslssssslsls (95,19497248660238465418986979262) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssssslslss_ok, coverslssssslslsl_ok⟩

def coverslssssslsll : Tree := (.fork (.fork (.hit 97) (.hit 97)) (.hit 97))
theorem coverslssssslsll_ok : valid coverslssssslsll (99,316602858088729731394776793022) = true :=
  by decide +kernel

def coverslssssslsl : Tree := .fork coverslssssslsls coverslssssslsll
theorem coverslssssslsl_ok : valid coverslssssslsl (89,309178051315071158050553790) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssssslsls_ok, coverslssssslsll_ok⟩

def coverslsssssls : Tree := .fork coverslssssslss coverslssssslsl
theorem coverslsssssls_ok : valid coverslsssssls (79,297504403533403913125822) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssssslss_ok, coverslssssslsl_ok⟩

def coverslsssssll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 99) (.hit 99)) (.hit 99)) (.fork (.hit 99) (.hit 99))) (.fork (.fork (.fork (.hit 103) (.hit 103)) (.hit 103)) (.fork (.hit 103) (.hit 103)))) (.fork (.fork (.hit 93) (.hit 93)) (.fork (.hit 93) (.hit 93))))
theorem coverslsssssll_ok : valid coverslsssssll (83,4830976227088263318273982) = true :=
  by decide +kernel

def coverslsssssl : Tree := .fork coverslsssssls coverslsssssll
theorem coverslsssssl_ok : valid coverslsssssl (73,4717681595485909876670) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsssssls_ok, coverslsssssll_ok⟩

def coverslsssss : Tree := .fork coverslssssss coverslsssssl
theorem coverslsssss_ok : valid coverslsssss (63,4538484653119438782) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssssss_ok, coverslsssssl_ok⟩

def coverslssssls : Tree := (.fork (.fork (.fork (.hit 80) (.hit 80)) (.fork (.hit 80) (.hit 80))) (.fork (.fork (.fork (.fork (.fork (.hit 98) (.hit 98)) (.hit 98)) (.fork (.hit 98) (.hit 98))) (.fork (.fork (.hit 96) (.hit 96)) (.hit 96))) (.fork (.fork (.hit 89) (.hit 89)) (.hit 89))))
theorem coverslssssls_ok : valid coverslssssls (73,4648506305209499058110) = true :=
  by decide +kernel

def coverslsssslls : Tree := (.fork (.fork (.hit 83) (.hit 83)) (.fork (.hit 83) (.hit 83)))
theorem coverslsssslls_ok : valid coverslsssslls (83,4760071554554942229249982) = true :=
  by decide +kernel

def coverslssssllls : Tree := (.fork (.fork (.fork (.fork (.hit 101) (.hit 101)) (.hit 101)) (.fork (.hit 101) (.hit 101))) (.fork (.fork (.hit 103) (.hit 103)) (.fork (.hit 103) (.hit 103))))
theorem coverslssssllls_ok : valid coverslssssllls (93,4874313272962281257945726910) = true :=
  by decide +kernel

def coverslssssllll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 114) (.hit 114)) (.hit 114)) (.fork (.hit 114) (.hit 114))) (.fork (.fork (.hit 109) (.hit 109)) (.hit 109))) (.fork (.fork (.hit 103) (.hit 103)) (.hit 103)))
theorem coverslssssllll_ok : valid coverslssssllll (97,79150715630085097751893180350) = true :=
  by decide +kernel

def coverslsssslll : Tree := .fork coverslssssllls coverslssssllll
theorem coverslsssslll_ok : valid coverslsssslll (87,77295620731432692711620542) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssssllls_ok, coverslssssllll_ok⟩

def coverslssssll : Tree := .fork coverslsssslls coverslsssslll
theorem coverslssssll_ok : valid coverslssssll (77,75484003548254177263550) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsssslls_ok, coverslsssslll_ok⟩

def coverslssssl : Tree := .fork coverslssssls coverslssssll
theorem coverslssssl_ok : valid coverslssssl (67,73713774929530257342) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssssls_ok, coverslssssll_ok⟩

def coverslssss : Tree := .fork coverslsssss coverslssssl
theorem coverslssss_ok : valid coverslssss (57,70913822767906750) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsssss_ok, coverslssssl_ok⟩

def coverslssslssss : Tree := (.fork (.fork (.fork (.fork (.hit 95) (.hit 95)) (.hit 95)) (.fork (.hit 95) (.hit 95))) (.fork (.fork (.hit 91) (.hit 91)) (.hit 91)))
theorem coverslssslssss_ok : valid coverslssslssss (85,19035784351405969141333950) = true :=
  by decide +kernel

def coverslssslsssl : Tree := (.fork (.fork (.fork (.hit 95) (.hit 95)) (.fork (.hit 95) (.hit 95))) (.fork (.fork (.fork (.hit 101) (.hit 101)) (.hit 101)) (.fork (.hit 101) (.hit 101))))
theorem coverslssslsssl_ok : valid coverslssslsssl (89,309177981058916971070816190) = true :=
  by decide +kernel

def coverslssslsss : Tree := .fork coverslssslssss coverslssslsssl
theorem coverslssslsss_ok : valid coverslssslsss (79,297434147379216933388222) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssslssss_ok, coverslssslsssl_ok⟩

def coverslssslssl : Tree := (.fork (.fork (.hit 82) (.hit 82)) (.hit 82))
theorem coverslssslssl_ok : valid coverslssslssl (83,4830905970934076338536382) = true :=
  by decide +kernel

def coverslssslss : Tree := .fork coverslssslsss coverslssslssl
theorem coverslssslss_ok : valid coverslssslss (73,4647425441298930139070) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssslsss_ok, coverslssslssl_ok⟩

def coverslssslsl : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 91) (.hit 91)) (.hit 91)) (.fork (.hit 91) (.hit 91))) (.fork (.fork (.hit 90) (.hit 90)) (.hit 90))) (.fork (.fork (.hit 85) (.hit 85)) (.hit 85)))
theorem coverslssslsl_ok : valid coverslssslsl (77,75482922684343608344510) = true :=
  by decide +kernel

def coverslsssls : Tree := .fork coverslssslss coverslssslsl
theorem coverslsssls_ok : valid coverslsssls (67,72632911018961338302) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssslss_ok, coverslssslsl_ok⟩

def coverslsssll : Tree := (.fork (.fork (.fork (.hit 78) (.hit 78)) (.fork (.hit 78) (.hit 78))) (.fork (.fork (.hit 79) (.hit 79)) (.hit 79)))
theorem coverslsssll_ok : valid coverslsssll (71,1179437555441534435262) = true :=
  by decide +kernel

def coverslsssl : Tree := .fork coverslsssls coverslsssll
theorem coverslsssl_ok : valid coverslsssl (61,1151777733336825790) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsssls_ok, coverslsssll_ok⟩

def coverslsss : Tree := .fork coverslssss coverslsssl
theorem coverslsss_ok : valid coverslsss (51,1108028543664062) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssss_ok, coverslsssl_ok⟩

def coverslsslsss : Tree := (.fork (.fork (.hit 73) (.hit 73)) (.fork (.hit 73) (.hit 73)))
theorem coverslsslsss_ok : valid coverslsslsss (73,4647408552800327499710) = true :=
  by decide +kernel

def coverslsslsslssssss : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 128) (.hit 128)) (.hit 128)) (.fork (.hit 128) (.hit 128))) (.fork (.fork (.hit 125) (.hit 125)) (.hit 125))) (.fork (.fork (.fork (.hit 126) (.hit 126)) (.hit 126)) (.fork (.hit 126) (.hit 126))))
theorem coverslsslsslssssss_ok : valid coverslsslsslssssss (113,5109879448083018229889243170144190) = true :=
  by decide +kernel

def coverslsslsslsssssl : Tree := (.fork (.fork (.fork (.hit 120) (.hit 120)) (.hit 120)) (.fork (.hit 120) (.hit 120)))
theorem coverslsslsslsssssl_ok : valid coverslsslsslsssssl (117,82994332326105432657846688108445630) = true :=
  by decide +kernel

def coverslsslsslsssss : Tree := .fork coverslsslsslssssss coverslsslsslsssssl
theorem coverslsslsslsssss_ok : valid coverslsslsslsssss (107,79841866377403964750324851212222) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslsslssssss_ok, coverslsslsslsssssl_ok⟩

def coverslsslsslssssls : Tree := (.fork (.fork (.fork (.fork (.hit 126) (.hit 126)) (.hit 126)) (.fork (.hit 126) (.hit 126))) (.fork (.fork (.hit 124) (.hit 124)) (.hit 124)))
theorem coverslsslsslssssls_ok : valid coverslsslsslssssls (117,81777387749886332432409853031284670) = true :=
  by decide +kernel

def coverslsslsslssssll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 135) (.hit 135)) (.hit 135)) (.fork (.hit 135) (.hit 135))) (.fork (.fork (.hit 134) (.hit 134)) (.hit 134))) (.fork (.fork (.hit 127) (.hit 127)) (.hit 127)))
theorem coverslsslsslssssll_ok : valid coverslsslsslssssll (121,1327928633798244963279728972044107710) = true :=
  by decide +kernel

def coverslsslsslssssl : Tree := .fork coverslsslsslssssls coverslsslsslssssll
theorem coverslsslsslssssl_ok : valid coverslsslsslssssl (111,1296786442596504190187159928373182) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslsslssssls_ok, coverslsslsslssssll_ok⟩

def coverslsslsslssss : Tree := .fork coverslsslsslsssss coverslsslsslssssl
theorem coverslsslsslssss_ok : valid coverslsslsslssss (101,1247529163253741857529252478910) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslsslsssss_ok, coverslsslsslssssl_ok⟩

def coverslsslsslsssl : Tree := (.fork (.fork (.fork (.fork (.hit 116) (.hit 116)) (.hit 116)) (.fork (.hit 116) (.hit 116))) (.fork (.fork (.hit 115) (.hit 115)) (.fork (.hit 115) (.hit 115))))
theorem coverslsslsslsssl_ok : valid coverslsslsslsssl (105,20262288166677182879979800559550) = true :=
  by decide +kernel

def coverslsslsslsss : Tree := .fork coverslsslsslssss coverslsslsslsssl
theorem coverslsslsslsss_ok : valid coverslsslsslsss (95,19492644282644624829321248702) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslsslssss_ok, coverslsslsslsssl_ok⟩

def coverslsslsslssl : Tree := (.fork (.fork (.fork (.hit 106) (.hit 106)) (.fork (.hit 106) (.hit 106))) (.fork (.fork (.fork (.hit 112) (.hit 112)) (.hit 112)) (.fork (.hit 112) (.hit 112))))
theorem coverslsslsslssl_ok : valid coverslsslsslssl (99,316598253711135890805111062462) = true :=
  by decide +kernel

def coverslsslsslss : Tree := .fork coverslsslsslsss coverslsslsslssl
theorem coverslsslsslss_ok : valid coverslsslsslss (89,304573673721230568384823230) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslsslsss_ok, coverslsslsslssl_ok⟩

def coverslsslsslsl : Tree := (.fork (.fork (.fork (.hit 98) (.hit 98)) (.hit 98)) (.fork (.hit 98) (.hit 98)))
theorem coverslsslsslsl_ok : valid coverslsslsslsl (93,4946848821041406599256539070) = true :=
  by decide +kernel

def coverslsslssls : Tree := .fork coverslsslsslss coverslsslsslsl
theorem coverslsslssls_ok : valid coverslsslssls (83,4760070456802533057691582) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslsslss_ok, coverslsslsslsl_ok⟩

def coverslsslssll : Tree := (.fork (.fork (.fork (.hit 91) (.hit 91)) (.hit 91)) (.fork (.hit 91) (.hit 91)))
theorem coverslsslssll_ok : valid coverslsslssll (87,77295619633680283540062142) = true :=
  by decide +kernel

def coverslsslssl : Tree := .fork coverslsslssls coverslsslssll
theorem coverslsslssl_ok : valid coverslsslssl (77,75482905795845005705150) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslssls_ok, coverslsslssll_ok⟩

def coverslsslss : Tree := .fork coverslsslsss coverslsslssl
theorem coverslsslss_ok : valid coverslsslss (67,72616022520358698942) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslsss_ok, coverslsslssl_ok⟩

def coverslsslslss : Tree := (.fork (.fork (.fork (.fork (.hit 95) (.hit 95)) (.fork (.hit 95) (.hit 95))) (.fork (.fork (.hit 98) (.hit 98)) (.hit 98))) (.fork (.fork (.fork (.fork (.hit 102) (.hit 102)) (.hit 102)) (.fork (.hit 102) (.hit 102))) (.fork (.fork (.hit 104) (.hit 104)) (.fork (.hit 104) (.hit 104)))))
theorem coverslsslslss_ok : valid coverslsslslss (83,4758963652158110484594622) = true :=
  by decide +kernel

def coverslsslslsl : Tree := (.fork (.fork (.fork (.hit 93) (.hit 93)) (.fork (.hit 93) (.hit 93))) (.fork (.fork (.hit 96) (.hit 96)) (.hit 96)))
theorem coverslsslslsl_ok : valid coverslsslslsl (87,77294512829035860966965182) = true :=
  by decide +kernel

def coverslsslsls : Tree := .fork coverslsslslss coverslsslslsl
theorem coverslsslsls_ok : valid coverslsslsls (77,74376101151422432608190) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslslss_ok, coverslsslslsl_ok⟩

def coverslsslsll : Tree := (.fork (.fork (.fork (.fork (.hit 93) (.hit 93)) (.fork (.hit 93) (.hit 93))) (.fork (.fork (.hit 98) (.hit 98)) (.fork (.hit 98) (.hit 98)))) (.fork (.fork (.hit 88) (.hit 88)) (.hit 88)))
theorem coverslsslsll_ok : valid coverslsslsll (81,1207744057040137283895230) = true :=
  by decide +kernel

def coverslsslsl : Tree := .fork coverslsslsls coverslsslsll
theorem coverslsslsl_ok : valid coverslsslsl (71,1179420666942931795902) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslsls_ok, coverslsslsll_ok⟩

def coverslssls : Tree := .fork coverslsslss coverslsslsl
theorem coverslssls_ok : valid coverslssls (61,1134889234734186430) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsslss_ok, coverslsslsl_ok⟩

def coverslssll : Tree := (.fork (.fork (.fork (.hit 70) (.hit 70)) (.hit 70)) (.fork (.fork (.fork (.hit 79) (.hit 79)) (.hit 79)) (.fork (.hit 79) (.hit 79))))
theorem coverslssll_ok : valid coverslssll (65,18428711803836891070) = true :=
  by decide +kernel

def coverslssl : Tree := .fork coverslssls coverslssll
theorem coverslssl_ok : valid coverslssl (55,17996527146303422) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslssls_ok, coverslssll_ok⟩

def coverslss : Tree := .fork coverslsss coverslssl
theorem coverslss_ok : valid coverslss (45,17313008910270) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsss_ok, coverslssl_ok⟩

def coverslslss : Tree := (.fork (.fork (.fork (.hit 68) (.hit 68)) (.fork (.hit 68) (.hit 68))) (.fork (.fork (.fork (.hit 77) (.hit 77)) (.fork (.hit 77) (.hit 77))) (.fork (.fork (.fork (.hit 84) (.hit 84)) (.hit 84)) (.fork (.hit 84) (.hit 84)))))
theorem coverslslss_ok : valid coverslslss (61,1134625351943520190) = true :=
  by decide +kernel

def coverslslslss : Tree := (.fork (.fork (.fork (.fork (.hit 85) (.hit 85)) (.hit 85)) (.fork (.hit 85) (.hit 85))) (.fork (.fork (.fork (.fork (.hit 98) (.hit 98)) (.hit 98)) (.fork (.hit 98) (.hit 98))) (.fork (.fork (.hit 94) (.hit 94)) (.hit 94))))
theorem coverslslslss_ok : valid coverslslslss (77,74358807064970539237310) = true :=
  by decide +kernel

def coverslslslsl : Tree := (.fork (.fork (.fork (.fork (.hit 91) (.hit 91)) (.hit 91)) (.fork (.hit 91) (.hit 91))) (.fork (.fork (.hit 89) (.hit 89)) (.hit 89)))
theorem coverslslslsl_ok : valid coverslslslsl (81,1207726762953685390524350) = true :=
  by decide +kernel

def coverslslsls : Tree := .fork coverslslslss coverslslslsl
theorem coverslslsls_ok : valid coverslslsls (71,1162126580491038425022) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslslslss_ok, coverslslslsl_ok⟩

def coverslslsllss : Tree := (.fork (.fork (.fork (.fork (.hit 98) (.hit 98)) (.hit 98)) (.fork (.hit 98) (.hit 98))) (.fork (.fork (.fork (.fork (.fork (.hit 112) (.hit 112)) (.hit 112)) (.fork (.hit 112) (.hit 112))) (.fork (.fork (.hit 112) (.hit 112)) (.hit 112))) (.fork (.fork (.hit 103) (.hit 103)) (.hit 103))))
theorem coverslslsllss_ok : valid coverslslsllss (87,76143418704749933052755902) = true :=
  by decide +kernel

def coverslslsllsl : Tree := (.fork (.fork (.fork (.hit 98) (.hit 98)) (.fork (.hit 98) (.hit 98))) (.fork (.fork (.fork (.fork (.fork (.hit 117) (.hit 117)) (.hit 117)) (.fork (.hit 117) (.hit 117))) (.fork (.fork (.hit 118) (.hit 118)) (.fork (.hit 118) (.hit 118)))) (.fork (.fork (.hit 108) (.hit 108)) (.hit 108))))
theorem coverslslsllsl_ok : valid coverslslsllsl (91,1236712205534793940770684862) = true :=
  by decide +kernel

def coverslslslls : Tree := .fork coverslslsllss coverslslsllsl
theorem coverslslslls_ok : valid coverslslslls (81,1190017888642924220972990) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslslsllss_ok, coverslslsllsl_ok⟩

def coverslslslll : Tree := (.fork (.fork (.hit 85) (.hit 85)) (.fork (.hit 85) (.hit 85)))
theorem coverslslslll_ok : valid coverslslslll (85,19323905182862361841565630) = true :=
  by decide +kernel

def coverslslsll : Tree := .fork coverslslslls coverslslslll
theorem coverslslsll_ok : valid coverslslsll (75,18871000891252207976382) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslslslls_ok, coverslslslll_ok⟩

def coverslslsl : Tree := .fork coverslslsls coverslslsll
theorem coverslslsl_ok : valid coverslslsl (65,18428447921046224830) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslslsls_ok, coverslslsll_ok⟩

def coverslsls : Tree := .fork coverslslss coverslslsl
theorem coverslsls_ok : valid coverslsls (55,17732644355637182) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslslss_ok, coverslslsl_ok⟩

def coverslsll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 75) (.hit 75)) (.hit 75)) (.fork (.hit 75) (.hit 75))) (.fork (.fork (.fork (.fork (.hit 86) (.hit 86)) (.hit 86)) (.fork (.hit 86) (.hit 86))) (.fork (.fork (.hit 81) (.hit 81)) (.hit 81)))) (.fork (.fork (.hit 66) (.hit 66)) (.hit 66)))
theorem coverslsll_ok : valid coverslsll (59,287948621997866942) = true :=
  by decide +kernel

def coverslsl : Tree := .fork coverslsls coverslsll
theorem coverslsl_ok : valid coverslsl (49,281195799576510) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslsls_ok, coverslsll_ok⟩

def coversls : Tree := .fork coverslss coverslsl
theorem coversls_ok : valid coversls (39,270578679742) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslss_ok, coverslsl_ok⟩

def coversllssssssss : Tree := (.fork (.fork (.fork (.hit 94) (.hit 94)) (.hit 94)) (.fork (.hit 94) (.hit 94)))
theorem coversllssssssss_ok : valid coversllssssssss (91,1218290197391961605887950782) = true :=
  by decide +kernel

def coversllsssssssl : Tree := (.fork (.fork (.fork (.fork (.hit 107) (.hit 107)) (.fork (.hit 107) (.hit 107))) (.fork (.fork (.hit 110) (.hit 110)) (.hit 110))) (.fork (.fork (.fork (.hit 108) (.hit 108)) (.hit 108)) (.fork (.hit 108) (.hit 108))))
theorem coversllsssssssl_ok : valid coversllsssssssl (95,19787390786672665729374814142) = true :=
  by decide +kernel

def coversllsssssss : Tree := .fork coversllssssssss coversllsssssssl
theorem coversllsssssss_ok : valid coversllsssssss (85,19035784334249464579424190) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversllssssssss_ok, coversllsssssssl_ok⟩

def coversllssssssl : Tree := (.fork (.fork (.hit 86) (.hit 86)) (.hit 86))
theorem coversllssssssl_ok : valid coversllssssssl (89,309177981041760466508906430) = true :=
  by decide +kernel

def coversllssssss : Tree := .fork coversllsssssss coversllssssssl
theorem coversllssssss_ok : valid coversllssssss (79,297434130222712371478462) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversllsssssss_ok, coversllssssssl_ok⟩

def coversllsssssl : Tree := (.fork (.fork (.fork (.hit 89) (.hit 89)) (.fork (.hit 89) (.hit 89))) (.fork (.fork (.hit 92) (.hit 92)) (.hit 92)))
theorem coversllsssssl_ok : valid coversllsssssl (83,4830905953777571776626622) = true :=
  by decide +kernel

def coversllsssss : Tree := .fork coversllssssss coversllsssssl
theorem coversllsssss_ok : valid coversllsssss (73,4647408284794368229310) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversllssssss_ok, coversllsssssl_ok⟩

def coversllssssl : Tree := (.fork (.fork (.hit 77) (.hit 77)) (.fork (.hit 77) (.hit 77)))
theorem coversllssssl_ok : valid coversllssssl (77,75482905527839046434750) = true :=
  by decide +kernel

def coversllssss : Tree := .fork coversllsssss coversllssssl
theorem coversllssss_ok : valid coversllssss (67,72615754514399428542) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversllsssss_ok, coversllssssl_ok⟩

def coversllsssl : Tree := (.fork (.fork (.hit 72) (.hit 72)) (.fork (.hit 72) (.hit 72)))
theorem coversllsssl_ok : valid coversllsssl (71,1179420398936972525502) = true :=
  by decide +kernel

def coversllsss : Tree := .fork coversllssss coversllsssl
theorem coversllsss_ok : valid coversllsss (61,1134621228774916030) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversllssss_ok, coversllsssl_ok⟩

def coversllssl : Tree := (.fork (.fork (.fork (.fork (.hit 77) (.hit 77)) (.fork (.hit 77) (.hit 77))) (.fork (.fork (.fork (.hit 86) (.hit 86)) (.hit 86)) (.fork (.hit 86) (.hit 86)))) (.fork (.fork (.hit 74) (.hit 74)) (.hit 74)))
theorem coversllssl_ok : valid coversllssl (65,18428443797877620670) = true :=
  by decide +kernel

def coversllss : Tree := .fork coversllsss coversllssl
theorem coversllss_ok : valid coversllss (55,17728521187033022) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversllsss_ok, coversllssl_ok⟩

def coversllsl : Tree := (.fork (.hit 54) (.hit 54))
theorem coversllsl_ok : valid coversllsl (59,287944498829262782) = true :=
  by decide +kernel

def coverslls : Tree := .fork coversllss coversllsl
theorem coverslls_ok : valid coverslls (49,277072630972350) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversllss_ok, coversllsl_ok⟩

def coverslll : Tree := (.fork (.fork (.fork (.hit 59) (.hit 59)) (.fork (.hit 59) (.hit 59))) (.fork (.fork (.fork (.hit 70) (.hit 70)) (.fork (.hit 70) (.hit 70))) (.fork (.fork (.fork (.hit 78) (.hit 78)) (.hit 78)) (.fork (.hit 78) (.hit 78)))))
theorem coverslll_ok : valid coverslll (53,4499197281632190) = true :=
  by decide +kernel

def coversll : Tree := .fork coverslls coverslll
theorem coversll_ok : valid coversll (43,4393747283902) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverslls_ok, coverslll_ok⟩

def coversl : Tree := .fork coversls coversll
theorem coversl_ok : valid coversl (33,4290707390) = true :=
  Bool.and_eq_true_iff.mpr ⟨coversls_ok, coversll_ok⟩

def covers : Tree := .fork coverss coversl
theorem covers_ok : valid covers (23,4128702) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverss_ok, coversl_ok⟩

def coverlsssssss : Tree := (.fork (.fork (.fork (.hit 75) (.hit 75)) (.fork (.hit 75) (.hit 75))) (.fork (.fork (.fork (.fork (.fork (.hit 95) (.hit 95)) (.hit 95)) (.fork (.hit 95) (.hit 95))) (.fork (.fork (.hit 91) (.hit 91)) (.hit 91))) (.fork (.fork (.hit 85) (.hit 85)) (.hit 85))))
theorem coverlsssssss_ok : valid coverlsssssss (69,290463017795554574270) = true :=
  by decide +kernel

def coverlssssssl : Tree := (.fork (.fork (.hit 73) (.hit 73)) (.fork (.hit 73) (.hit 73)))
theorem coverlssssssl_ok : valid coverlssssssl (73,4717681595485846962110) = true :=
  by decide +kernel

def coverlssssss : Tree := .fork coverlsssssss coverlssssssl
theorem coverlssssss_ok : valid coverlssssss (63,4538484653056524222) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlsssssss_ok, coverlssssssl_ok⟩

def coverlsssssl : Tree := (.fork (.fork (.fork (.hit 72) (.hit 72)) (.hit 72)) (.fork (.hit 72) (.hit 72)))
theorem coverlsssssl_ok : valid coverlsssssl (67,73713774929467342782) = true :=
  by decide +kernel

def coverlsssss : Tree := .fork coverlssssss coverlsssssl
theorem coverlsssss_ok : valid coverlsssss (57,70913822704992190) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlssssss_ok, coverlsssssl_ok⟩

def coverlssssls : Tree := (.fork (.fork (.fork (.fork (.hit 75) (.hit 75)) (.hit 75)) (.fork (.hit 75) (.hit 75))) (.fork (.fork (.hit 78) (.hit 78)) (.fork (.hit 78) (.hit 78))))
theorem coverlssssls_ok : valid coverlssssls (67,72632911018898423742) = true :=
  by decide +kernel

def coverlssssllsss : Tree := (.fork (.fork (.fork (.fork (.hit 101) (.hit 101)) (.fork (.hit 101) (.hit 101))) (.fork (.fork (.fork (.hit 110) (.hit 110)) (.hit 110)) (.fork (.hit 110) (.hit 110)))) (.fork (.fork (.fork (.hit 103) (.hit 103)) (.hit 103)) (.fork (.hit 103) (.hit 103))))
theorem coverlssssllsss_ok : valid coverlssssllsss (89,304572566933474644351451070) = true :=
  by decide +kernel

def coverlssssllssl : Tree := (.fork (.fork (.fork (.hit 100) (.hit 100)) (.fork (.hit 100) (.hit 100))) (.fork (.fork (.fork (.hit 110) (.hit 110)) (.fork (.hit 110) (.hit 110))) (.fork (.fork (.fork (.hit 115) (.hit 115)) (.hit 115)) (.fork (.hit 115) (.hit 115)))))
theorem coverlssssllssl_ok : valid coverlssssllssl (93,4946847714253650675223166910) = true :=
  by decide +kernel

def coverlssssllss : Tree := .fork coverlssssllsss coverlssssllssl
theorem coverlssssllss_ok : valid coverlssssllss (83,4758963669046609024319422) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlssssllsss_ok, coverlssssllssl_ok⟩

def coverlssssllsl : Tree := (.fork (.fork (.fork (.fork (.hit 95) (.hit 95)) (.hit 95)) (.fork (.hit 95) (.hit 95))) (.fork (.fork (.fork (.hit 103) (.hit 103)) (.fork (.hit 103) (.hit 103))) (.fork (.fork (.hit 106) (.hit 106)) (.hit 106))))
theorem coverlssssllsl_ok : valid coverlssssllsl (87,77294512845924359506689982) = true :=
  by decide +kernel

def coverlsssslls : Tree := .fork coverlssssllss coverlssssllsl
theorem coverlsssslls_ok : valid coverlsssslls (77,74376118039920972332990) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlssssllss_ok, coverlssssllsl_ok⟩

def coverlsssslll : Tree := (.fork (.fork (.fork (.hit 84) (.hit 84)) (.hit 84)) (.fork (.hit 84) (.hit 84)))
theorem coverlsssslll_ok : valid coverlsssslll (81,1207744073928635823620030) = true :=
  by decide +kernel

def coverlssssll : Tree := .fork coverlsssslls coverlsssslll
theorem coverlssssll_ok : valid coverlssssll (71,1179437555441471520702) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlsssslls_ok, coverlsssslll_ok⟩

def coverlssssl : Tree := .fork coverlssssls coverlssssll
theorem coverlssssl_ok : valid coverlssssl (61,1151777733273911230) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlssssls_ok, coverlssssll_ok⟩

def coverlssss : Tree := .fork coverlsssss coverlssssl
theorem coverlssss_ok : valid coverlssss (51,1108028480749502) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlsssss_ok, coverlssssl_ok⟩

def coverlsssl : Tree := (.fork (.fork (.fork (.hit 60) (.hit 60)) (.hit 60)) (.fork (.hit 60) (.hit 60)))
theorem coverlsssl_ok : valid coverlsssl (55,17996527083388862) = true :=
  by decide +kernel

def coverlsss : Tree := .fork coverlssss coverlsssl
theorem coverlsss_ok : valid coverlsss (45,17312945995710) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlssss_ok, coverlsssl_ok⟩

def coverlsslss : Tree := (.fork (.fork (.fork (.fork (.hit 70) (.hit 70)) (.hit 70)) (.fork (.hit 70) (.hit 70))) (.fork (.fork (.hit 67) (.hit 67)) (.hit 67)))
theorem coverlsslss_ok : valid coverlsslss (61,1134625351880605630) = true :=
  by decide +kernel

def coverlsslsls : Tree := (.fork (.fork (.fork (.fork (.hit 79) (.hit 79)) (.hit 79)) (.fork (.hit 79) (.hit 79))) (.fork (.fork (.hit 81) (.hit 81)) (.fork (.hit 81) (.hit 81))))
theorem coverlsslsls_ok : valid coverlsslsls (71,1162126580490975510462) = true :=
  by decide +kernel

def coverlsslslls : Tree := (.fork (.fork (.fork (.hit 85) (.hit 85)) (.hit 85)) (.fork (.hit 85) (.hit 85)))
theorem coverlsslslls_ok : valid coverlsslslls (81,1190017888642924158058430) = true :=
  by decide +kernel

def coverlsslslll : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 101) (.hit 101)) (.hit 101)) (.fork (.hit 101) (.hit 101))) (.fork (.fork (.hit 101) (.hit 101)) (.fork (.hit 101) (.hit 101)))) (.fork (.fork (.hit 91) (.hit 91)) (.hit 91)))
theorem coverlsslslll_ok : valid coverlsslslll (85,19323905182862361778651070) = true :=
  by decide +kernel

def coverlsslsll : Tree := .fork coverlsslslls coverlsslslll
theorem coverlsslsll_ok : valid coverlsslsll (75,18871000891252145061822) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlsslslls_ok, coverlsslslll_ok⟩

def coverlsslsl : Tree := .fork coverlsslsls coverlsslsll
theorem coverlsslsl_ok : valid coverlsslsl (65,18428447920983310270) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlsslsls_ok, coverlsslsll_ok⟩

def coverlssls : Tree := .fork coverlsslss coverlsslsl
theorem coverlssls_ok : valid coverlssls (55,17732644292722622) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlsslss_ok, coverlsslsl_ok⟩

def coverlsslls : Tree := (.fork (.fork (.fork (.hit 68) (.hit 68)) (.hit 68)) (.fork (.hit 68) (.hit 68)))
theorem coverlsslls_ok : valid coverlsslls (65,18158231943341080510) = true :=
  by decide +kernel

def coverlssllls : Tree := (.fork (.fork (.fork (.fork (.hit 83) (.hit 83)) (.hit 83)) (.fork (.hit 83) (.hit 83))) (.fork (.fork (.fork (.hit 92) (.hit 92)) (.fork (.hit 92) (.hit 92))) (.fork (.fork (.hit 93) (.hit 93)) (.hit 93))))
theorem coverlssllls_ok : valid coverlssllls (75,18594029514168859557822) = true :=
  by decide +kernel

def coverlssllll : Tree := (.fork (.fork (.fork (.hit 83) (.hit 83)) (.hit 83)) (.fork (.hit 83) (.hit 83)))
theorem coverlssllll_ok : valid coverlssllll (79,301936018486347572379582) = true :=
  by decide +kernel

def coverlsslll : Tree := .fork coverlssllls coverlssllll
theorem coverlsslll_ok : valid coverlsslll (69,294859393048984354750) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlssllls_ok, coverlssllll_ok⟩

def coverlssll : Tree := .fork coverlsslls coverlsslll
theorem coverlssll_ok : valid coverlssll (59,287948621934952382) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlsslls_ok, coverlsslll_ok⟩

def coverlssl : Tree := .fork coverlssls coverlssll
theorem coverlssl_ok : valid coverlssl (49,281195736661950) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlssls_ok, coverlssll_ok⟩

def coverlss : Tree := .fork coverlsss coverlssl
theorem coverlss_ok : valid coverlss (39,270515765182) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlsss_ok, coverlssl_ok⟩

def coverlsl : Tree := (.fork (.hit 36) (.hit 36))
theorem coverlsl_ok : valid coverlsl (43,4393684369342) = true :=
  by decide +kernel

def coverls : Tree := .fork coverlss coverlsl
theorem coverls_ok : valid coverls (33,4227792830) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlss_ok, coverlsl_ok⟩

def coverllsss : Tree := (.fork (.fork (.fork (.hit 61) (.hit 61)) (.fork (.hit 61) (.hit 61))) (.fork (.fork (.hit 66) (.hit 66)) (.fork (.hit 66) (.hit 66))))
theorem coverllsss_ok : valid coverllsss (55,17728456699609022) = true :=
  by decide +kernel

def coverllsslssss : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 97) (.hit 97)) (.hit 97)) (.fork (.hit 97) (.hit 97))) (.fork (.fork (.hit 96) (.hit 96)) (.hit 96))) (.fork (.fork (.hit 93) (.hit 93)) (.fork (.hit 93) (.hit 93))))
theorem coverllsslssss_ok : valid coverllsslssss (83,4758946087851493292965822) = true :=
  by decide +kernel

def coverllsslsssl : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 101) (.hit 101)) (.hit 101)) (.fork (.hit 101) (.hit 101))) (.fork (.fork (.hit 100) (.hit 100)) (.hit 100))) (.fork (.fork (.fork (.hit 99) (.hit 99)) (.hit 99)) (.fork (.hit 99) (.hit 99))))
theorem coverllsslsssl_ok : valid coverllsslsssl (87,77294495264729243775336382) = true :=
  by decide +kernel

def coverllsslsss : Tree := .fork coverllsslssss coverllsslsssl
theorem coverllsslsss_ok : valid coverllsslsss (77,74358536844805240979390) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverllsslssss_ok, coverllsslsssl_ok⟩

def coverllsslssl : Tree := (.fork (.fork (.fork (.hit 86) (.hit 86)) (.hit 86)) (.fork (.hit 86) (.hit 86)))
theorem coverllsslssl_ok : valid coverllsslssl (81,1207726492733520092266430) = true :=
  by decide +kernel

def coverllsslss : Tree := .fork coverllsslsss coverllsslssl
theorem coverllsslss_ok : valid coverllsslss (71,1161856360325740167102) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverllsslsss_ok, coverllsslssl_ok⟩

def coverllsslsl : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 89) (.hit 89)) (.hit 89)) (.fork (.hit 89) (.hit 89))) (.fork (.fork (.hit 88) (.hit 88)) (.hit 88))) (.fork (.fork (.fork (.hit 90) (.hit 90)) (.hit 90)) (.fork (.hit 90) (.hit 90))))
theorem coverllsslsl_ok : valid coverllsslsl (75,18870730671086909718462) = true :=
  by decide +kernel

def coverllssls : Tree := .fork coverllsslss coverllsslsl
theorem coverllssls_ok : valid coverllssls (65,18158227755747966910) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverllsslss_ok, coverllsslsl_ok⟩

def coverllssll : Tree := (.fork (.fork (.fork (.hit 72) (.hit 72)) (.hit 72)) (.fork (.hit 72) (.hit 72)))
theorem coverllssll_ok : valid coverllssll (69,294859388861391241150) = true :=
  by decide +kernel

def coverllssl : Tree := .fork coverllssls coverllssll
theorem coverllssl_ok : valid coverllssl (59,287944434341838782) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverllssls_ok, coverllssll_ok⟩

def coverllss : Tree := .fork coverllsss coverllssl
theorem coverllss_ok : valid coverllss (49,277008143548350) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverllsss_ok, coverllssl_ok⟩

def coverllsl : Tree := (.fork (.fork (.fork (.hit 59) (.hit 59)) (.fork (.hit 59) (.hit 59))) (.fork (.fork (.fork (.hit 66) (.hit 66)) (.hit 66)) (.fork (.hit 66) (.hit 66))))
theorem coverllsl_ok : valid coverllsl (53,4499132794208190) = true :=
  by decide +kernel

def coverlls : Tree := .fork coverllss coverllsl
theorem coverlls_ok : valid coverlls (43,4329259859902) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverllss_ok, coverllsl_ok⟩

def coverlllss : Tree := (.fork (.fork (.fork (.fork (.hit 67) (.hit 67)) (.hit 67)) (.fork (.hit 67) (.hit 67))) (.fork (.fork (.hit 66) (.hit 66)) (.hit 66)))
theorem coverlllss_ok : valid coverlllss (59,283656338993512382) = true :=
  by decide +kernel

def coverlllslsss : Tree := (.fork (.fork (.fork (.fork (.hit 91) (.hit 91)) (.hit 91)) (.fork (.hit 91) (.hit 91))) (.fork (.fork (.hit 88) (.hit 88)) (.hit 88)))
theorem coverlllslsss_ok : valid coverlllslsss (81,1189736589517915655438270) = true :=
  by decide +kernel

def coverlllslsslss : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 115) (.hit 115)) (.fork (.hit 115) (.hit 115))) (.fork (.fork (.hit 120) (.hit 120)) (.fork (.hit 120) (.hit 120)))) (.fork (.fork (.hit 110) (.hit 110)) (.hit 110))) (.fork (.fork (.hit 105) (.hit 105)) (.hit 105)))
theorem coverlllslsslss_ok : valid coverlllslsslss (97,77970860472635026538330259390) = true :=
  by decide +kernel

def coverlllslsslsl : Tree := (.fork (.fork (.fork (.hit 106) (.hit 106)) (.hit 106)) (.fork (.hit 106) (.hit 106)))
theorem coverlllslsslsl_ok : valid coverlllslsslsl (101,1266393298186600090441489514430) = true :=
  by decide +kernel

def coverlllslssls : Tree := .fork coverlllslsslss coverlllslsslsl
theorem coverlllslssls_ok : valid coverlllslssls (91,1218578036941449494584557502) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlllslsslss_ok, coverlllslsslsl_ok⟩

def coverlllslssll : Tree := (.fork (.fork (.hit 96) (.hit 96)) (.fork (.hit 96) (.hit 96)))
theorem coverlllslssll_ok : valid coverlllslssll (95,19787678626222153618071420862) = true :=
  by decide +kernel

def coverlllslssl : Tree := .fork coverlllslssls coverlllslssll
theorem coverlllslssl_ok : valid coverlllslssl (85,19323623883737353276030910) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlllslssls_ok, coverlllslssll_ok⟩

def coverlllslss : Tree := .fork coverlllslsss coverlllslssl
theorem coverlllslss_ok : valid coverlllslss (75,18589701766243642441662) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlllslsss_ok, coverlllslssl_ok⟩

def coverlllslsl : Tree := (.fork (.hit 74) (.hit 74))
theorem coverlllslsl_ok : valid coverlllslsl (79,301931690738422355263422) = true :=
  by decide +kernel

def coverlllsls : Tree := .fork coverlllslss coverlllslsl
theorem coverlllsls_ok : valid coverlllsls (69,290531645123767238590) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlllslss_ok, coverlllslsl_ok⟩

def coverlllsll : Tree := (.fork (.fork (.fork (.fork (.hit 81) (.hit 81)) (.hit 81)) (.fork (.hit 81) (.hit 81))) (.fork (.fork (.fork (.fork (.hit 96) (.hit 96)) (.fork (.hit 96) (.hit 96))) (.fork (.fork (.hit 99) (.hit 99)) (.fork (.hit 99) (.hit 99)))) (.fork (.fork (.hit 91) (.hit 91)) (.hit 91))))
theorem coverlllsll_ok : valid coverlllsll (73,4717750222814059626430) = true :=
  by decide +kernel

def coverlllsl : Tree := .fork coverlllsls coverlllsll
theorem coverlllsl_ok : valid coverlllsl (63,4607111981269188542) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlllsls_ok, coverlllsll_ok⟩

def coverllls : Tree := .fork coverlllss coverlllsl
theorem coverllls_ok : valid coverllls (53,4433162096541630) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlllss_ok, coverlllsl_ok⟩

def coverllllss : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 83) (.hit 83)) (.hit 83)) (.fork (.hit 83) (.hit 83))) (.fork (.fork (.fork (.hit 87) (.hit 87)) (.hit 87)) (.fork (.hit 87) (.hit 87)))) (.fork (.fork (.hit 77) (.hit 77)) (.hit 77)))
theorem coverllllss_ok : valid coverllllss (69,290464091129356681150) = true :=
  by decide +kernel

def coverllllsl : Tree := (.fork (.fork (.fork (.fork (.fork (.hit 87) (.hit 87)) (.hit 87)) (.fork (.hit 87) (.hit 87))) (.fork (.fork (.hit 86) (.hit 86)) (.hit 86))) (.fork (.fork (.hit 83) (.hit 83)) (.fork (.hit 83) (.hit 83))))
theorem coverllllsl_ok : valid coverllllsl (73,4717682668819649068990) = true :=
  by decide +kernel

def coverlllls : Tree := .fork coverllllss coverllllsl
theorem coverlllls_ok : valid coverlllls (63,4539557986858631102) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverllllss_ok, coverllllsl_ok⟩

def coverlllll : Tree := (.fork (.fork (.fork (.hit 69) (.hit 69)) (.hit 69)) (.fork (.hit 69) (.hit 69)))
theorem coverlllll_ok : valid coverlllll (67,73714848263269449662) = true :=
  by decide +kernel

def coverllll : Tree := .fork coverlllls coverlllll
theorem coverllll_ok : valid coverllll (57,71987156507099070) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlllls_ok, coverlllll_ok⟩

def coverlll : Tree := .fork coverllls coverllll
theorem coverlll_ok : valid coverlll (47,70299957526462) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverllls_ok, coverllll_ok⟩

def coverll : Tree := .fork coverlls coverlll
theorem coverll_ok : valid coverll (37,68652302270) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverlls_ok, coverlll_ok⟩

def coverl : Tree := .fork coverls coverll
theorem coverl_ok : valid coverl (27,67043262) = true :=
  Bool.and_eq_true_iff.mpr ⟨coverls_ok, coverll_ok⟩

def cover : Tree := .fork covers coverl
theorem cover_ok : valid cover (17,65470) = true :=
  Bool.and_eq_true_iff.mpr ⟨covers_ok, coverl_ok⟩

end Ruliology.CellularAutomata.Rule30ResetSwap.Certificate
