module

public import Ruliology.CellularAutomata.Rule30Period21Profiles

/-! Saved-orbit certificate. No Nodup or minimal preperiod claim is made. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Certificates.TrapPeriod21
open Ruliology.CellularAutomata.Rule30Period21Profiles

def head : State := (1198372, 1591590)
def entry : State := (1022062, 192419)

theorem reach : advance step 1967 head = entry := by decide +kernel

theorem block_000 : SafePath step head 128 (1022062, 192419) (163429, 1780529) :=
  checkPath_sound step head 128 (1022062, 192419) (163429, 1780529) (by decide +kernel)

theorem block_001 : SafePath step head 128 (163429, 1780529) (686292, 241479) :=
  checkPath_sound step head 128 (163429, 1780529) (686292, 241479) (by decide +kernel)

theorem block_002 : SafePath step head 128 (686292, 241479) (1498661, 1796918) :=
  checkPath_sound step head 128 (686292, 241479) (1498661, 1796918) (by decide +kernel)

theorem block_003 : SafePath step head 128 (1498661, 1796918) (1108474, 1092620) :=
  checkPath_sound step head 128 (1498661, 1796918) (1108474, 1092620) (by decide +kernel)

theorem block_004 : SafePath step head 128 (1108474, 1092620) (1836823, 1571346) :=
  checkPath_sound step head 128 (1108474, 1092620) (1836823, 1571346) (by decide +kernel)

theorem block_005 : SafePath step head 128 (1836823, 1571346) (1621376, 558847) :=
  checkPath_sound step head 128 (1836823, 1571346) (1621376, 558847) (by decide +kernel)

theorem block_006 : SafePath step head 128 (1621376, 558847) (984547, 123965) :=
  checkPath_sound step head 128 (1621376, 558847) (984547, 123965) (by decide +kernel)

theorem block_007 : SafePath step head 128 (984547, 123965) (456411, 1266537) :=
  checkPath_sound step head 128 (984547, 123965) (456411, 1266537) (by decide +kernel)

theorem block_008 : SafePath step head 128 (456411, 1266537) (1488717, 1101926) :=
  checkPath_sound step head 128 (456411, 1266537) (1488717, 1101926) (by decide +kernel)

theorem block_009 : SafePath step head 128 (1488717, 1101926) (1836398, 1571252) :=
  checkPath_sound step head 128 (1488717, 1101926) (1836398, 1571252) (by decide +kernel)

theorem block_010 : SafePath step head 128 (1836398, 1571252) (39240, 2018383) :=
  checkPath_sound step head 128 (1836398, 1571252) (39240, 2018383) (by decide +kernel)

theorem block_011 : SafePath step head 128 (39240, 2018383) (1642096, 910430) :=
  checkPath_sound step head 128 (39240, 2018383) (1642096, 910430) (by decide +kernel)

theorem block_012 : SafePath step head 128 (1642096, 910430) (1377857, 1178238) :=
  checkPath_sound step head 128 (1642096, 910430) (1377857, 1178238) (by decide +kernel)

theorem block_013 : SafePath step head 128 (1377857, 1178238) (958574, 671651) :=
  checkPath_sound step head 128 (1377857, 1178238) (958574, 671651) (by decide +kernel)

theorem block_014 : SafePath step head 128 (958574, 671651) (681104, 722078) :=
  checkPath_sound step head 128 (958574, 671651) (681104, 722078) (by decide +kernel)

theorem block_015 : SafePath step head 128 (681104, 722078) (1457918, 1780266) :=
  checkPath_sound step head 128 (681104, 722078) (1457918, 1780266) (by decide +kernel)

theorem block_016 : SafePath step head 128 (1457918, 1780266) (386791, 309808) :=
  checkPath_sound step head 128 (1457918, 1780266) (386791, 309808) (by decide +kernel)

theorem block_017 : SafePath step head 128 (386791, 309808) (271547, 1541289) :=
  checkPath_sound step head 128 (386791, 309808) (271547, 1541289) (by decide +kernel)

theorem block_018 : SafePath step head 128 (271547, 1541289) (1977870, 773099) :=
  checkPath_sound step head 128 (271547, 1541289) (1977870, 773099) (by decide +kernel)

theorem block_019 : SafePath step head 128 (1977870, 773099) (1977691, 767592) :=
  checkPath_sound step head 128 (1977870, 773099) (1977691, 767592) (by decide +kernel)

theorem block_020 : SafePath step head 128 (1977691, 767592) (1086020, 1970806) :=
  checkPath_sound step head 128 (1977691, 767592) (1086020, 1970806) (by decide +kernel)

theorem block_021 : SafePath step head 128 (1086020, 1970806) (1316541, 498388) :=
  checkPath_sound step head 128 (1086020, 1970806) (1316541, 498388) (by decide +kernel)

theorem block_022 : SafePath step head 128 (1316541, 498388) (1044910, 23587) :=
  checkPath_sound step head 128 (1316541, 498388) (1044910, 23587) (by decide +kernel)

theorem block_023 : SafePath step head 128 (1044910, 23587) (435295, 296000) :=
  checkPath_sound step head 128 (1044910, 23587) (435295, 296000) (by decide +kernel)

theorem block_024 : SafePath step head 128 (435295, 296000) (251379, 1598493) :=
  checkPath_sound step head 128 (435295, 296000) (251379, 1598493) (by decide +kernel)

theorem block_025 : SafePath step head 128 (251379, 1598493) (933966, 687968) :=
  checkPath_sound step head 128 (251379, 1598493) (933966, 687968) (by decide +kernel)

theorem block_026 : SafePath step head 128 (933966, 687968) (1411942, 454075) :=
  checkPath_sound step head 128 (933966, 687968) (1411942, 454075) (by decide +kernel)

theorem block_027 : SafePath step head 128 (1411942, 454075) (949667, 207165) :=
  checkPath_sound step head 128 (1411942, 454075) (949667, 207165) (by decide +kernel)

theorem block_028 : SafePath step head 128 (949667, 207165) (81984, 1867391) :=
  checkPath_sound step head 128 (949667, 207165) (81984, 1867391) (by decide +kernel)

theorem block_029 : SafePath step head 128 (81984, 1867391) (191033, 172846) :=
  checkPath_sound step head 128 (81984, 1867391) (191033, 172846) (by decide +kernel)

theorem block_030 : SafePath step head 128 (191033, 172846) (1990553, 16588) :=
  checkPath_sound step head 128 (191033, 172846) (1990553, 16588) (by decide +kernel)

theorem block_031 : SafePath step head 128 (1990553, 16588) (861156, 81223) :=
  checkPath_sound step head 128 (1990553, 16588) (861156, 81223) (by decide +kernel)

theorem block_032 : SafePath step head 128 (861156, 81223) (990955, 1436489) :=
  checkPath_sound step head 128 (861156, 81223) (990955, 1436489) (by decide +kernel)

theorem block_033 : SafePath step head 128 (990955, 1436489) (1779763, 626653) :=
  checkPath_sound step head 128 (990955, 1436489) (1779763, 626653) (by decide +kernel)

theorem block_034 : SafePath step head 128 (1779763, 626653) (572882, 824642) :=
  checkPath_sound step head 128 (1779763, 626653) (572882, 824642) (by decide +kernel)

theorem block_035 : SafePath step head 128 (572882, 824642) (1203139, 157816) :=
  checkPath_sound step head 128 (572882, 824642) (1203139, 157816) (by decide +kernel)

theorem block_036 : SafePath step head 128 (1203139, 157816) (740317, 877206) :=
  checkPath_sound step head 128 (1203139, 157816) (740317, 877206) (by decide +kernel)

theorem block_037 : SafePath step head 128 (740317, 877206) (1439302, 268915) :=
  checkPath_sound step head 128 (740317, 877206) (1439302, 268915) (by decide +kernel)

theorem block_038 : SafePath step head 128 (1439302, 268915) (1752502, 820954) :=
  checkPath_sound step head 128 (1439302, 268915) (1752502, 820954) (by decide +kernel)

theorem block_039 : SafePath step head 128 (1752502, 820954) (1114578, 1703256) :=
  checkPath_sound step head 128 (1752502, 820954) (1114578, 1703256) (by decide +kernel)

theorem block_040 : SafePath step head 128 (1114578, 1703256) (2025408, 308606) :=
  checkPath_sound step head 128 (1114578, 1703256) (2025408, 308606) (by decide +kernel)

theorem block_041 : SafePath step head 128 (2025408, 308606) (281547, 460810) :=
  checkPath_sound step head 128 (2025408, 308606) (281547, 460810) (by decide +kernel)

theorem block_042 : SafePath step head 128 (281547, 460810) (1362426, 487762) :=
  checkPath_sound step head 128 (281547, 460810) (1362426, 487762) (by decide +kernel)

theorem block_043 : SafePath step head 128 (1362426, 487762) (1086318, 1610314) :=
  checkPath_sound step head 128 (1362426, 487762) (1086318, 1610314) (by decide +kernel)

theorem block_044 : SafePath step head 128 (1086318, 1610314) (101980, 2024343) :=
  checkPath_sound step head 128 (1086318, 1610314) (101980, 2024343) (by decide +kernel)

theorem block_045 : SafePath step head 128 (101980, 2024343) (325150, 1528779) :=
  checkPath_sound step head 128 (101980, 2024343) (325150, 1528779) (by decide +kernel)

theorem block_046 : SafePath step head 128 (325150, 1528779) (237695, 1589077) :=
  checkPath_sound step head 128 (325150, 1528779) (237695, 1589077) (by decide +kernel)

theorem block_047 : SafePath step head 128 (237695, 1589077) (1611417, 582889) :=
  checkPath_sound step head 128 (237695, 1589077) (1611417, 582889) (by decide +kernel)

theorem block_048 : SafePath step head 128 (1611417, 582889) (1034901, 1404133) :=
  checkPath_sound step head 128 (1611417, 582889) (1034901, 1404133) (by decide +kernel)

theorem block_049 : SafePath step head 128 (1034901, 1404133) (1682906, 952683) :=
  checkPath_sound step head 128 (1034901, 1404133) (1682906, 952683) (by decide +kernel)

theorem block_050 : SafePath step head 128 (1682906, 952683) (1454949, 1826116) :=
  checkPath_sound step head 128 (1682906, 952683) (1454949, 1826116) (by decide +kernel)

theorem block_051 : SafePath step head 128 (1454949, 1826116) (458477, 1715017) :=
  checkPath_sound step head 128 (1454949, 1826116) (458477, 1715017) (by decide +kernel)

theorem block_052 : SafePath step head 128 (458477, 1715017) (228683, 1681677) :=
  checkPath_sound step head 128 (458477, 1715017) (228683, 1681677) (by decide +kernel)

theorem block_053 : SafePath step head 128 (228683, 1681677) (1339637, 285860) :=
  checkPath_sound step head 128 (228683, 1681677) (1339637, 285860) (by decide +kernel)

theorem block_054 : SafePath step head 128 (1339637, 285860) (571052, 839863) :=
  checkPath_sound step head 128 (1339637, 285860) (571052, 839863) (by decide +kernel)

theorem block_055 : SafePath step head 128 (571052, 839863) (284789, 487193) :=
  checkPath_sound step head 128 (571052, 839863) (284789, 487193) (by decide +kernel)

theorem block_056 : SafePath step head 128 (284789, 487193) (1879848, 1517006) :=
  checkPath_sound step head 128 (284789, 487193) (1879848, 1517006) (by decide +kernel)

theorem block_057 : SafePath step head 128 (1879848, 1517006) (922322, 246299) :=
  checkPath_sound step head 128 (1879848, 1517006) (922322, 246299) (by decide +kernel)

theorem block_058 : SafePath step head 128 (922322, 246299) (2028805, 219588) :=
  checkPath_sound step head 128 (922322, 246299) (2028805, 219588) (by decide +kernel)

theorem block_059 : SafePath step head 128 (2028805, 219588) (1809002, 191282) :=
  checkPath_sound step head 128 (2028805, 219588) (1809002, 191282) (by decide +kernel)

theorem block_060 : SafePath step head 128 (1809002, 191282) (2086079, 1393792) :=
  checkPath_sound step head 128 (1809002, 191282) (2086079, 1393792) (by decide +kernel)

theorem block_061 : SafePath step head 128 (2086079, 1393792) (299372, 317879) :=
  checkPath_sound step head 128 (2086079, 1393792) (299372, 317879) (by decide +kernel)

theorem block_062 : SafePath step head 128 (299372, 317879) (1133233, 1862878) :=
  checkPath_sound step head 128 (299372, 317879) (1133233, 1862878) (by decide +kernel)

theorem block_063 : SafePath step head 128 (1133233, 1862878) (939054, 202275) :=
  checkPath_sound step head 128 (1133233, 1862878) (939054, 202275) (by decide +kernel)

theorem block_064 : SafePath step head 128 (939054, 202275) (807328, 1514559) :=
  checkPath_sound step head 128 (939054, 202275) (807328, 1514559) (by decide +kernel)

theorem block_065 : SafePath step head 128 (807328, 1514559) (698770, 183963) :=
  checkPath_sound step head 128 (807328, 1514559) (698770, 183963) (by decide +kernel)

theorem block_066 : SafePath step head 128 (698770, 183963) (1231228, 1798406) :=
  checkPath_sound step head 128 (698770, 183963) (1231228, 1798406) (by decide +kernel)

theorem block_067 : SafePath step head 128 (1231228, 1798406) (271242, 276722) :=
  checkPath_sound step head 128 (1231228, 1798406) (271242, 276722) (by decide +kernel)

theorem block_068 : SafePath step head 128 (271242, 276722) (83822, 1994827) :=
  checkPath_sound step head 128 (271242, 276722) (83822, 1994827) (by decide +kernel)

theorem block_069 : SafePath step head 128 (83822, 1994827) (607602, 817435) :=
  checkPath_sound step head 128 (83822, 1994827) (607602, 817435) (by decide +kernel)

theorem block_070 : SafePath step head 128 (607602, 817435) (1537408, 349951) :=
  checkPath_sound step head 128 (607602, 817435) (1537408, 349951) (by decide +kernel)

theorem block_071 : SafePath step head 128 (1537408, 349951) (898713, 599278) :=
  checkPath_sound step head 128 (1537408, 349951) (898713, 599278) (by decide +kernel)

theorem block_072 : SafePath step head 128 (898713, 599278) (1589877, 947109) :=
  checkPath_sound step head 128 (898713, 599278) (1589877, 947109) (by decide +kernel)

theorem block_073 : SafePath step head 128 (1589877, 947109) (595081, 595470) :=
  checkPath_sound step head 128 (1589877, 947109) (595081, 595470) (by decide +kernel)

theorem block_074 : SafePath step head 128 (595081, 595470) (1223608, 1781038) :=
  checkPath_sound step head 128 (595081, 595470) (1223608, 1781038) (by decide +kernel)

theorem block_075 : SafePath step head 128 (1223608, 1781038) (1172408, 2014508) :=
  checkPath_sound step head 128 (1223608, 1781038) (1172408, 2014508) (by decide +kernel)

theorem block_076 : SafePath step head 128 (1172408, 2014508) (1674324, 980839) :=
  checkPath_sound step head 128 (1172408, 2014508) (1674324, 980839) (by decide +kernel)

theorem block_077 : SafePath step head 128 (1674324, 980839) (209909, 1677401) :=
  checkPath_sound step head 128 (1674324, 980839) (209909, 1677401) (by decide +kernel)

theorem block_078 : SafePath step head 128 (209909, 1677401) (153936, 1589535) :=
  checkPath_sound step head 128 (209909, 1677401) (153936, 1589535) (by decide +kernel)

theorem block_079 : SafePath step head 128 (153936, 1589535) (158817, 1288121) :=
  checkPath_sound step head 128 (153936, 1589535) (158817, 1288121) (by decide +kernel)

theorem block_080 : SafePath step head 128 (158817, 1288121) (278759, 425797) :=
  checkPath_sound step head 128 (158817, 1288121) (278759, 425797) (by decide +kernel)

theorem block_081 : SafePath step head 128 (278759, 425797) (320262, 1489403) :=
  checkPath_sound step head 128 (278759, 425797) (320262, 1489403) (by decide +kernel)

theorem block_082 : SafePath step head 128 (320262, 1489403) (289775, 460874) :=
  checkPath_sound step head 128 (320262, 1489403) (289775, 460874) (by decide +kernel)

theorem block_083 : SafePath step head 128 (289775, 460874) (824640, 451711) :=
  checkPath_sound step head 128 (289775, 460874) (824640, 451711) (by decide +kernel)

theorem block_084 : SafePath step head 128 (824640, 451711) (1554395, 1103170) :=
  checkPath_sound step head 128 (824640, 451711) (1554395, 1103170) (by decide +kernel)

theorem block_085 : SafePath step head 128 (1554395, 1103170) (573514, 948338) :=
  checkPath_sound step head 128 (1554395, 1103170) (573514, 948338) (by decide +kernel)

theorem block_086 : SafePath step head 128 (573514, 948338) (1409224, 1507144) :=
  checkPath_sound step head 128 (573514, 948338) (1409224, 1507144) (by decide +kernel)

theorem block_087 : SafePath step head 128 (1409224, 1507144) (551801, 805289) :=
  checkPath_sound step head 128 (1409224, 1507144) (551801, 805289) (by decide +kernel)

theorem block_088 : SafePath step head 128 (551801, 805289) (606510, 946467) :=
  checkPath_sound step head 128 (551801, 805289) (606510, 946467) (by decide +kernel)

theorem block_089 : SafePath step head 128 (606510, 946467) (616657, 937822) :=
  checkPath_sound step head 128 (606510, 946467) (616657, 937822) (by decide +kernel)

theorem block_090 : SafePath step head 128 (616657, 937822) (803907, 1468025) :=
  checkPath_sound step head 128 (616657, 937822) (803907, 1468025) (by decide +kernel)

theorem block_091 : SafePath step head 128 (803907, 1468025) (1434855, 439877) :=
  checkPath_sound step head 128 (803907, 1468025) (1434855, 439877) (by decide +kernel)

theorem block_092 : SafePath step head 128 (1434855, 439877) (830504, 403343) :=
  checkPath_sound step head 128 (1434855, 439877) (830504, 403343) (by decide +kernel)

theorem block_093 : SafePath step head 128 (830504, 403343) (682174, 542848) :=
  checkPath_sound step head 128 (830504, 403343) (682174, 542848) (by decide +kernel)

theorem block_094 : SafePath step head 128 (682174, 542848) (2046915, 1420664) :=
  checkPath_sound step head 128 (682174, 542848) (2046915, 1420664) (by decide +kernel)

theorem block_095 : SafePath step head 128 (2046915, 1420664) (31429, 2075781) :=
  checkPath_sound step head 128 (2046915, 1420664) (31429, 2075781) (by decide +kernel)

theorem block_096 : SafePath step head 128 (31429, 2075781) (813259, 1548425) :=
  checkPath_sound step head 128 (31429, 2075781) (813259, 1548425) (by decide +kernel)

theorem block_097 : SafePath step head 128 (813259, 1548425) (1001080, 160687) :=
  checkPath_sound step head 128 (813259, 1548425) (1001080, 160687) (by decide +kernel)

theorem block_098 : SafePath step head 128 (1001080, 160687) (1651847, 885989) :=
  checkPath_sound step head 128 (1001080, 160687) (1651847, 885989) (by decide +kernel)

theorem block_099 : SafePath step head 128 (1651847, 885989) (621232, 590558) :=
  checkPath_sound step head 128 (1651847, 885989) (621232, 590558) (by decide +kernel)

theorem block_100 : SafePath step head 128 (621232, 590558) (1498358, 1742672) :=
  checkPath_sound step head 128 (621232, 590558) (1498358, 1742672) (by decide +kernel)

theorem block_101 : SafePath step head 128 (1498358, 1742672) (1726508, 749367) :=
  checkPath_sound step head 128 (1498358, 1742672) (1726508, 749367) (by decide +kernel)

theorem block_102 : SafePath step head 128 (1726508, 749367) (1088367, 2018720) :=
  checkPath_sound step head 128 (1726508, 749367) (1088367, 2018720) (by decide +kernel)

theorem block_103 : SafePath step head 128 (1088367, 2018720) (759937, 191729) :=
  checkPath_sound step head 128 (1088367, 2018720) (759937, 191729) (by decide +kernel)

theorem block_104 : SafePath step head 128 (759937, 191729) (37472, 2016191) :=
  checkPath_sound step head 128 (759937, 191729) (37472, 2016191) (by decide +kernel)

theorem block_105 : SafePath step head 128 (37472, 2016191) (698277, 735876) :=
  checkPath_sound step head 128 (37472, 2016191) (698277, 735876) (by decide +kernel)

theorem block_106 : SafePath step head 128 (698277, 735876) (733300, 909063) :=
  checkPath_sound step head 128 (698277, 735876) (733300, 909063) (by decide +kernel)

theorem block_107 : SafePath step head 128 (733300, 909063) (638996, 1146647) :=
  checkPath_sound step head 128 (733300, 909063) (638996, 1146647) (by decide +kernel)

theorem block_108 : SafePath step head 128 (638996, 1146647) (961683, 668888) :=
  checkPath_sound step head 128 (638996, 1146647) (961683, 668888) (by decide +kernel)

theorem block_109 : SafePath step head 128 (961683, 668888) (508929, 1402877) :=
  checkPath_sound step head 128 (961683, 668888) (508929, 1402877) (by decide +kernel)

theorem block_110 : SafePath step head 128 (508929, 1402877) (1621345, 841121) :=
  checkPath_sound step head 128 (508929, 1402877) (1621345, 841121) (by decide +kernel)

theorem block_111 : SafePath step head 128 (1621345, 841121) (516345, 1228301) :=
  checkPath_sound step head 128 (1621345, 841121) (516345, 1228301) (by decide +kernel)

theorem block_112 : SafePath step head 128 (516345, 1228301) (1003179, 29837) :=
  checkPath_sound step head 128 (516345, 1228301) (1003179, 29837) (by decide +kernel)

theorem block_113 : SafePath step head 128 (1003179, 29837) (2081279, 1408002) :=
  checkPath_sound step head 128 (1003179, 29837) (2081279, 1408002) (by decide +kernel)

theorem block_114 : SafePath step head 128 (2081279, 1408002) (1225902, 141099) :=
  checkPath_sound step head 128 (2081279, 1408002) (1225902, 141099) (by decide +kernel)

theorem block_115 : SafePath step head 128 (1225902, 141099) (1280248, 183983) :=
  checkPath_sound step head 128 (1225902, 141099) (1280248, 183983) (by decide +kernel)

theorem block_116 : SafePath step head 128 (1280248, 183983) (1480604, 1708052) :=
  checkPath_sound step head 128 (1280248, 183983) (1480604, 1708052) (by decide +kernel)

theorem block_117 : SafePath step head 128 (1480604, 1708052) (1632349, 1092678) :=
  checkPath_sound step head 128 (1480604, 1708052) (1632349, 1092678) (by decide +kernel)

theorem block_118 : SafePath step head 128 (1632349, 1092678) (211857, 1583841) :=
  checkPath_sound step head 128 (1632349, 1092678) (211857, 1583841) (by decide +kernel)

theorem block_119 : SafePath step head 128 (211857, 1583841) (341933, 1167413) :=
  checkPath_sound step head 128 (211857, 1583841) (341933, 1167413) (by decide +kernel)

theorem block_120 : SafePath step head 128 (341933, 1167413) (1204164, 1283428) :=
  checkPath_sound step head 128 (341933, 1167413) (1204164, 1283428) (by decide +kernel)

theorem block_121 : SafePath step head 128 (1204164, 1283428) (1385103, 376053) :=
  checkPath_sound step head 128 (1204164, 1283428) (1385103, 376053) (by decide +kernel)

theorem block_122 : SafePath step head 128 (1385103, 376053) (673392, 553820) :=
  checkPath_sound step head 128 (1385103, 376053) (673392, 553820) (by decide +kernel)

theorem block_123 : SafePath step head 128 (673392, 553820) (1196972, 1867046) :=
  checkPath_sound step head 128 (673392, 553820) (1196972, 1867046) (by decide +kernel)

theorem block_124 : SafePath step head 128 (1196972, 1867046) (1624018, 1011739) :=
  checkPath_sound step head 128 (1196972, 1867046) (1624018, 1011739) (by decide +kernel)

theorem block_125 : SafePath step head 128 (1624018, 1011739) (432358, 1102011) :=
  checkPath_sound step head 128 (1624018, 1011739) (432358, 1102011) (by decide +kernel)

theorem block_126 : SafePath step head 128 (432358, 1102011) (1636804, 1003894) :=
  checkPath_sound step head 128 (432358, 1102011) (1636804, 1003894) (by decide +kernel)

theorem block_127 : SafePath step head 128 (1636804, 1003894) (473323, 1158829) :=
  checkPath_sound step head 128 (1636804, 1003894) (473323, 1158829) (by decide +kernel)

theorem block_128 : SafePath step head 128 (473323, 1158829) (409499, 1805005) :=
  checkPath_sound step head 128 (473323, 1158829) (409499, 1805005) (by decide +kernel)

theorem block_129 : SafePath step head 128 (409499, 1805005) (1219459, 1610488) :=
  checkPath_sound step head 128 (409499, 1805005) (1219459, 1610488) (by decide +kernel)

theorem block_130 : SafePath step head 128 (1219459, 1610488) (814967, 1548369) :=
  checkPath_sound step head 128 (1219459, 1610488) (814967, 1548369) (by decide +kernel)

theorem block_131 : SafePath step head 128 (814967, 1548369) (935175, 684538) :=
  checkPath_sound step head 128 (814967, 1548369) (935175, 684538) (by decide +kernel)

theorem block_132 : SafePath step head 128 (935175, 684538) (516831, 1096513) :=
  checkPath_sound step head 128 (935175, 684538) (516831, 1096513) (by decide +kernel)

theorem block_133 : SafePath step head 128 (516831, 1096513) (2005977, 59724) :=
  checkPath_sound step head 128 (516831, 1096513) (2005977, 59724) (by decide +kernel)

theorem block_134 : SafePath step head 128 (2005977, 59724) (1831616, 531327) :=
  checkPath_sound step head 128 (2005977, 59724) (1831616, 531327) (by decide +kernel)

theorem block_135 : SafePath step head 128 (1831616, 531327) (1488953, 1084462) :=
  checkPath_sound step head 128 (1831616, 531327) (1488953, 1084462) (by decide +kernel)

theorem block_136 : SafePath step head 128 (1488953, 1084462) (727352, 650636) :=
  checkPath_sound step head 128 (1488953, 1084462) (727352, 650636) (by decide +kernel)

theorem block_137 : SafePath step head 128 (727352, 650636) (1064817, 2086174) :=
  checkPath_sound step head 128 (727352, 650636) (1064817, 2086174) (by decide +kernel)

theorem block_138 : SafePath step head 128 (1064817, 2086174) (196838, 1965755) :=
  checkPath_sound step head 128 (1064817, 2086174) (196838, 1965755) (by decide +kernel)

theorem block_139 : SafePath step head 128 (196838, 1965755) (162725, 1245873) :=
  checkPath_sound step head 128 (196838, 1965755) (162725, 1245873) (by decide +kernel)

theorem block_140 : SafePath step head 128 (162725, 1245873) (310015, 1495573) :=
  checkPath_sound step head 128 (162725, 1245873) (310015, 1495573) (by decide +kernel)

theorem block_141 : SafePath step head 128 (310015, 1495573) (1709390, 255050) :=
  checkPath_sound step head 128 (310015, 1495573) (1709390, 255050) (by decide +kernel)

theorem block_142 : SafePath step head 128 (1709390, 255050) (689217, 583550) :=
  checkPath_sound step head 128 (1709390, 255050) (689217, 583550) (by decide +kernel)

theorem block_143 : SafePath step head 128 (689217, 583550) (1980358, 251258) :=
  checkPath_sound step head 128 (689217, 583550) (1980358, 251258) (by decide +kernel)

theorem block_144 : SafePath step head 128 (1980358, 251258) (1452170, 1814754) :=
  checkPath_sound step head 128 (1980358, 251258) (1452170, 1814754) (by decide +kernel)

theorem block_145 : SafePath step head 128 (1452170, 1814754) (1807712, 574911) :=
  checkPath_sound step head 128 (1452170, 1814754) (1807712, 574911) (by decide +kernel)

theorem block_146 : SafePath step head 128 (1807712, 574911) (1079022, 2038432) :=
  checkPath_sound step head 128 (1807712, 574911) (1079022, 2038432) (by decide +kernel)

theorem block_147 : SafePath step head 128 (1079022, 2038432) (243081, 186092) :=
  checkPath_sound step head 128 (1079022, 2038432) (243081, 186092) (by decide +kernel)

theorem block_148 : SafePath step head 128 (243081, 186092) (1861196, 506486) :=
  checkPath_sound step head 128 (243081, 186092) (1861196, 506486) (by decide +kernel)

theorem block_149 : SafePath step head 128 (1861196, 506486) (1308234, 1579874) :=
  checkPath_sound step head 128 (1861196, 506486) (1308234, 1579874) (by decide +kernel)

theorem block_150 : SafePath step head 128 (1308234, 1579874) (209011, 1957469) :=
  checkPath_sound step head 128 (1308234, 1579874) (209011, 1957469) (by decide +kernel)

theorem block_151 : SafePath step head 128 (209011, 1957469) (441570, 295074) :=
  checkPath_sound step head 128 (209011, 1957469) (441570, 295074) (by decide +kernel)

theorem block_152 : SafePath step head 128 (441570, 295074) (1437067, 276105) :=
  checkPath_sound step head 128 (441570, 295074) (1437067, 276105) (by decide +kernel)

theorem block_153 : SafePath step head 128 (1437067, 276105) (1244651, 1266738) :=
  checkPath_sound step head 128 (1437067, 276105) (1244651, 1266738) (by decide +kernel)

theorem block_154 : SafePath step head 128 (1244651, 1266738) (780538, 544300) :=
  checkPath_sound step head 128 (1244651, 1266738) (780538, 544300) (by decide +kernel)

theorem block_155 : SafePath step head 128 (780538, 544300) (1922304, 627199) :=
  checkPath_sound step head 128 (780538, 544300) (1922304, 627199) (by decide +kernel)

theorem block_156 : SafePath step head 128 (1922304, 627199) (741890, 549880) :=
  checkPath_sound step head 128 (1922304, 627199) (741890, 549880) (by decide +kernel)

theorem block_157 : SafePath step head 128 (741890, 549880) (1024992, 1390655) :=
  checkPath_sound step head 128 (741890, 549880) (1024992, 1390655) (by decide +kernel)

theorem block_158 : SafePath step head 128 (1024992, 1390655) (2046636, 101558) :=
  checkPath_sound step head 128 (1024992, 1390655) (2046636, 101558) (by decide +kernel)

theorem block_159 : SafePath step head 128 (2046636, 101558) (1572600, 1092096) :=
  checkPath_sound step head 128 (2046636, 101558) (1572600, 1092096) (by decide +kernel)

theorem block_160 : SafePath step head 128 (1572600, 1092096) (1241391, 220597) :=
  checkPath_sound step head 128 (1572600, 1092096) (1241391, 220597) (by decide +kernel)

theorem block_161 : SafePath step head 128 (1241391, 220597) (1323263, 1547778) :=
  checkPath_sound step head 128 (1241391, 220597) (1323263, 1547778) (by decide +kernel)

theorem block_162 : SafePath step head 128 (1323263, 1547778) (385031, 442362) :=
  checkPath_sound step head 128 (1323263, 1547778) (385031, 442362) (by decide +kernel)

theorem block_163 : SafePath step head 128 (385031, 442362) (9345, 2065657) :=
  checkPath_sound step head 128 (385031, 442362) (9345, 2065657) (by decide +kernel)

theorem block_164 : SafePath step head 128 (9345, 2065657) (1404167, 412144) :=
  checkPath_sound step head 128 (9345, 2065657) (1404167, 412144) (by decide +kernel)

theorem block_165 : SafePath step head 128 (1404167, 412144) (1617521, 838561) :=
  checkPath_sound step head 128 (1404167, 412144) (1617521, 838561) (by decide +kernel)

theorem block_166 : SafePath step head 128 (1617521, 838561) (170839, 1632661) :=
  checkPath_sound step head 128 (1617521, 838561) (170839, 1632661) (by decide +kernel)

theorem block_167 : SafePath step head 128 (170839, 1632661) (267692, 464584) :=
  checkPath_sound step head 128 (170839, 1632661) (267692, 464584) (by decide +kernel)

theorem block_168 : SafePath step head 128 (267692, 464584) (1570051, 1054978) :=
  checkPath_sound step head 128 (267692, 464584) (1570051, 1054978) (by decide +kernel)

theorem block_169 : SafePath step head 128 (1570051, 1054978) (1181781, 1298198) :=
  checkPath_sound step head 128 (1570051, 1054978) (1181781, 1298198) (by decide +kernel)

theorem block_170 : SafePath step head 128 (1181781, 1298198) (1700172, 874854) :=
  checkPath_sound step head 128 (1181781, 1298198) (1700172, 874854) (by decide +kernel)

theorem block_171 : SafePath step head 128 (1700172, 874854) (79462, 1940411) :=
  checkPath_sound step head 128 (1700172, 874854) (79462, 1940411) (by decide +kernel)

theorem block_172 : SafePath step head 128 (79462, 1940411) (1444350, 1829930) :=
  checkPath_sound step head 128 (79462, 1940411) (1444350, 1829930) (by decide +kernel)

theorem block_173 : SafePath step head 128 (1444350, 1829930) (238339, 179704) :=
  checkPath_sound step head 128 (1444350, 1829930) (238339, 179704) (by decide +kernel)

theorem block_174 : SafePath step head 128 (238339, 179704) (1112373, 1969188) :=
  checkPath_sound step head 128 (238339, 179704) (1112373, 1969188) (by decide +kernel)

theorem block_175 : SafePath step head 128 (1112373, 1969188) (1269312, 1927804) :=
  checkPath_sound step head 128 (1112373, 1969188) (1269312, 1927804) (by decide +kernel)

theorem block_176 : SafePath step head 128 (1269312, 1927804) (1714834, 795330) :=
  checkPath_sound step head 128 (1269312, 1927804) (1714834, 795330) (by decide +kernel)

theorem block_177 : SafePath step head 128 (1714834, 795330) (1865480, 1549792) :=
  checkPath_sound step head 128 (1714834, 795330) (1865480, 1549792) (by decide +kernel)

theorem block_178 : SafePath step head 128 (1865480, 1549792) (395352, 1248879) :=
  checkPath_sound step head 128 (1865480, 1549792) (395352, 1248879) (by decide +kernel)

theorem block_179 : SafePath step head 128 (395352, 1248879) (997536, 110143) :=
  checkPath_sound step head 128 (395352, 1248879) (997536, 110143) (by decide +kernel)

theorem block_180 : SafePath step head 128 (997536, 110143) (427432, 1369743) :=
  checkPath_sound step head 128 (997536, 110143) (427432, 1369743) (by decide +kernel)

theorem block_181 : SafePath step head 128 (427432, 1369743) (1948366, 1475444) :=
  checkPath_sound step head 128 (427432, 1369743) (1948366, 1475444) (by decide +kernel)

theorem block_182 : SafePath step head 128 (1948366, 1475444) (1828975, 544677) :=
  checkPath_sound step head 128 (1948366, 1475444) (1828975, 544677) (by decide +kernel)

theorem block_183 : SafePath step head 128 (1828975, 544677) (72346, 1697987) :=
  checkPath_sound step head 128 (1828975, 544677) (72346, 1697987) (by decide +kernel)

theorem block_184 : SafePath step head 128 (72346, 1697987) (1515166, 1425556) :=
  checkPath_sound step head 128 (72346, 1697987) (1515166, 1425556) (by decide +kernel)

theorem block_185 : SafePath step head 128 (1515166, 1425556) (212356, 1672935) :=
  checkPath_sound step head 128 (1515166, 1425556) (212356, 1672935) (by decide +kernel)

theorem block_186 : SafePath step head 128 (212356, 1672935) (263285, 517713) :=
  checkPath_sound step head 128 (212356, 1672935) (263285, 517713) (by decide +kernel)

theorem block_187 : SafePath step head 128 (263285, 517713) (801751, 494917) :=
  checkPath_sound step head 128 (263285, 517713) (801751, 494917) (by decide +kernel)

theorem block_188 : SafePath step head 128 (801751, 494917) (590418, 909915) :=
  checkPath_sound step head 128 (801751, 494917) (590418, 909915) (by decide +kernel)

theorem block_189 : SafePath step head 128 (590418, 909915) (626748, 958376) :=
  checkPath_sound step head 128 (590418, 909915) (626748, 958376) (by decide +kernel)

theorem block_190 : SafePath step head 128 (626748, 958376) (2083264, 29054) :=
  checkPath_sound step head 128 (626748, 958376) (2083264, 29054) (by decide +kernel)

theorem block_191 : SafePath step head 128 (2083264, 29054) (922618, 776204) :=
  checkPath_sound step head 128 (2083264, 29054) (922618, 776204) (by decide +kernel)

theorem block_192 : SafePath step head 128 (922618, 776204) (422124, 1072695) :=
  checkPath_sound step head 128 (922618, 776204) (422124, 1072695) (by decide +kernel)

theorem block_193 : SafePath step head 128 (422124, 1072695) (575842, 1011123) :=
  checkPath_sound step head 128 (422124, 1072695) (575842, 1011123) (by decide +kernel)

theorem block_194 : SafePath step head 128 (575842, 1011123) (1756310, 750811) :=
  checkPath_sound step head 128 (575842, 1011123) (1756310, 750811) (by decide +kernel)

theorem block_195 : SafePath step head 128 (1756310, 750811) (2094232, 22254) :=
  checkPath_sound step head 128 (1756310, 750811) (2094232, 22254) (by decide +kernel)

theorem block_196 : SafePath step head 128 (2094232, 22254) (597695, 627840) :=
  checkPath_sound step head 128 (2094232, 22254) (597695, 627840) (by decide +kernel)

theorem block_197 : SafePath step head 128 (597695, 627840) (1479784, 1107724) :=
  checkPath_sound step head 128 (597695, 627840) (1479784, 1107724) (by decide +kernel)

theorem block_198 : SafePath step head 128 (1479784, 1107724) (1562103, 1074202) :=
  checkPath_sound step head 128 (1479784, 1107724) (1562103, 1074202) (by decide +kernel)

theorem block_199 : SafePath step head 128 (1562103, 1074202) (2030980, 657127) :=
  checkPath_sound step head 128 (1562103, 1074202) (2030980, 657127) (by decide +kernel)

theorem block_200 : SafePath step head 128 (2030980, 657127) (355687, 411909) :=
  checkPath_sound step head 128 (2030980, 657127) (355687, 411909) (by decide +kernel)

theorem block_201 : SafePath step head 128 (355687, 411909) (137242, 258027) :=
  checkPath_sound step head 128 (355687, 411909) (137242, 258027) (by decide +kernel)

theorem block_202 : SafePath step head 128 (137242, 258027) (1103947, 1994354) :=
  checkPath_sound step head 128 (137242, 258027) (1103947, 1994354) (by decide +kernel)

theorem block_203 : SafePath step head 128 (1103947, 1994354) (1797730, 150450) :=
  checkPath_sound step head 128 (1103947, 1994354) (1797730, 150450) (by decide +kernel)

theorem block_204 : SafePath step head 128 (1797730, 150450) (1019528, 188655) :=
  checkPath_sound step head 128 (1797730, 150450) (1019528, 188655) (by decide +kernel)

theorem block_205 : SafePath step head 73 (1019528, 188655) (1022062, 192419) :=
  checkPath_sound step head 73 (1019528, 188655) (1022062, 192419) (by decide +kernel)

theorem join_00_000 : SafePath step head 256 (1022062, 192419) (686292, 241479) :=
  block_000.trans block_001

theorem join_00_001 : SafePath step head 256 (686292, 241479) (1108474, 1092620) :=
  block_002.trans block_003

theorem join_00_002 : SafePath step head 256 (1108474, 1092620) (1621376, 558847) :=
  block_004.trans block_005

theorem join_00_003 : SafePath step head 256 (1621376, 558847) (456411, 1266537) :=
  block_006.trans block_007

theorem join_00_004 : SafePath step head 256 (456411, 1266537) (1836398, 1571252) :=
  block_008.trans block_009

theorem join_00_005 : SafePath step head 256 (1836398, 1571252) (1642096, 910430) :=
  block_010.trans block_011

theorem join_00_006 : SafePath step head 256 (1642096, 910430) (958574, 671651) :=
  block_012.trans block_013

theorem join_00_007 : SafePath step head 256 (958574, 671651) (1457918, 1780266) :=
  block_014.trans block_015

theorem join_00_008 : SafePath step head 256 (1457918, 1780266) (271547, 1541289) :=
  block_016.trans block_017

theorem join_00_009 : SafePath step head 256 (271547, 1541289) (1977691, 767592) :=
  block_018.trans block_019

theorem join_00_010 : SafePath step head 256 (1977691, 767592) (1316541, 498388) :=
  block_020.trans block_021

theorem join_00_011 : SafePath step head 256 (1316541, 498388) (435295, 296000) :=
  block_022.trans block_023

theorem join_00_012 : SafePath step head 256 (435295, 296000) (933966, 687968) :=
  block_024.trans block_025

theorem join_00_013 : SafePath step head 256 (933966, 687968) (949667, 207165) :=
  block_026.trans block_027

theorem join_00_014 : SafePath step head 256 (949667, 207165) (191033, 172846) :=
  block_028.trans block_029

theorem join_00_015 : SafePath step head 256 (191033, 172846) (861156, 81223) :=
  block_030.trans block_031

theorem join_00_016 : SafePath step head 256 (861156, 81223) (1779763, 626653) :=
  block_032.trans block_033

theorem join_00_017 : SafePath step head 256 (1779763, 626653) (1203139, 157816) :=
  block_034.trans block_035

theorem join_00_018 : SafePath step head 256 (1203139, 157816) (1439302, 268915) :=
  block_036.trans block_037

theorem join_00_019 : SafePath step head 256 (1439302, 268915) (1114578, 1703256) :=
  block_038.trans block_039

theorem join_00_020 : SafePath step head 256 (1114578, 1703256) (281547, 460810) :=
  block_040.trans block_041

theorem join_00_021 : SafePath step head 256 (281547, 460810) (1086318, 1610314) :=
  block_042.trans block_043

theorem join_00_022 : SafePath step head 256 (1086318, 1610314) (325150, 1528779) :=
  block_044.trans block_045

theorem join_00_023 : SafePath step head 256 (325150, 1528779) (1611417, 582889) :=
  block_046.trans block_047

theorem join_00_024 : SafePath step head 256 (1611417, 582889) (1682906, 952683) :=
  block_048.trans block_049

theorem join_00_025 : SafePath step head 256 (1682906, 952683) (458477, 1715017) :=
  block_050.trans block_051

theorem join_00_026 : SafePath step head 256 (458477, 1715017) (1339637, 285860) :=
  block_052.trans block_053

theorem join_00_027 : SafePath step head 256 (1339637, 285860) (284789, 487193) :=
  block_054.trans block_055

theorem join_00_028 : SafePath step head 256 (284789, 487193) (922322, 246299) :=
  block_056.trans block_057

theorem join_00_029 : SafePath step head 256 (922322, 246299) (1809002, 191282) :=
  block_058.trans block_059

theorem join_00_030 : SafePath step head 256 (1809002, 191282) (299372, 317879) :=
  block_060.trans block_061

theorem join_00_031 : SafePath step head 256 (299372, 317879) (939054, 202275) :=
  block_062.trans block_063

theorem join_00_032 : SafePath step head 256 (939054, 202275) (698770, 183963) :=
  block_064.trans block_065

theorem join_00_033 : SafePath step head 256 (698770, 183963) (271242, 276722) :=
  block_066.trans block_067

theorem join_00_034 : SafePath step head 256 (271242, 276722) (607602, 817435) :=
  block_068.trans block_069

theorem join_00_035 : SafePath step head 256 (607602, 817435) (898713, 599278) :=
  block_070.trans block_071

theorem join_00_036 : SafePath step head 256 (898713, 599278) (595081, 595470) :=
  block_072.trans block_073

theorem join_00_037 : SafePath step head 256 (595081, 595470) (1172408, 2014508) :=
  block_074.trans block_075

theorem join_00_038 : SafePath step head 256 (1172408, 2014508) (209909, 1677401) :=
  block_076.trans block_077

theorem join_00_039 : SafePath step head 256 (209909, 1677401) (158817, 1288121) :=
  block_078.trans block_079

theorem join_00_040 : SafePath step head 256 (158817, 1288121) (320262, 1489403) :=
  block_080.trans block_081

theorem join_00_041 : SafePath step head 256 (320262, 1489403) (824640, 451711) :=
  block_082.trans block_083

theorem join_00_042 : SafePath step head 256 (824640, 451711) (573514, 948338) :=
  block_084.trans block_085

theorem join_00_043 : SafePath step head 256 (573514, 948338) (551801, 805289) :=
  block_086.trans block_087

theorem join_00_044 : SafePath step head 256 (551801, 805289) (616657, 937822) :=
  block_088.trans block_089

theorem join_00_045 : SafePath step head 256 (616657, 937822) (1434855, 439877) :=
  block_090.trans block_091

theorem join_00_046 : SafePath step head 256 (1434855, 439877) (682174, 542848) :=
  block_092.trans block_093

theorem join_00_047 : SafePath step head 256 (682174, 542848) (31429, 2075781) :=
  block_094.trans block_095

theorem join_00_048 : SafePath step head 256 (31429, 2075781) (1001080, 160687) :=
  block_096.trans block_097

theorem join_00_049 : SafePath step head 256 (1001080, 160687) (621232, 590558) :=
  block_098.trans block_099

theorem join_00_050 : SafePath step head 256 (621232, 590558) (1726508, 749367) :=
  block_100.trans block_101

theorem join_00_051 : SafePath step head 256 (1726508, 749367) (759937, 191729) :=
  block_102.trans block_103

theorem join_00_052 : SafePath step head 256 (759937, 191729) (698277, 735876) :=
  block_104.trans block_105

theorem join_00_053 : SafePath step head 256 (698277, 735876) (638996, 1146647) :=
  block_106.trans block_107

theorem join_00_054 : SafePath step head 256 (638996, 1146647) (508929, 1402877) :=
  block_108.trans block_109

theorem join_00_055 : SafePath step head 256 (508929, 1402877) (516345, 1228301) :=
  block_110.trans block_111

theorem join_00_056 : SafePath step head 256 (516345, 1228301) (2081279, 1408002) :=
  block_112.trans block_113

theorem join_00_057 : SafePath step head 256 (2081279, 1408002) (1280248, 183983) :=
  block_114.trans block_115

theorem join_00_058 : SafePath step head 256 (1280248, 183983) (1632349, 1092678) :=
  block_116.trans block_117

theorem join_00_059 : SafePath step head 256 (1632349, 1092678) (341933, 1167413) :=
  block_118.trans block_119

theorem join_00_060 : SafePath step head 256 (341933, 1167413) (1385103, 376053) :=
  block_120.trans block_121

theorem join_00_061 : SafePath step head 256 (1385103, 376053) (1196972, 1867046) :=
  block_122.trans block_123

theorem join_00_062 : SafePath step head 256 (1196972, 1867046) (432358, 1102011) :=
  block_124.trans block_125

theorem join_00_063 : SafePath step head 256 (432358, 1102011) (473323, 1158829) :=
  block_126.trans block_127

theorem join_00_064 : SafePath step head 256 (473323, 1158829) (1219459, 1610488) :=
  block_128.trans block_129

theorem join_00_065 : SafePath step head 256 (1219459, 1610488) (935175, 684538) :=
  block_130.trans block_131

theorem join_00_066 : SafePath step head 256 (935175, 684538) (2005977, 59724) :=
  block_132.trans block_133

theorem join_00_067 : SafePath step head 256 (2005977, 59724) (1488953, 1084462) :=
  block_134.trans block_135

theorem join_00_068 : SafePath step head 256 (1488953, 1084462) (1064817, 2086174) :=
  block_136.trans block_137

theorem join_00_069 : SafePath step head 256 (1064817, 2086174) (162725, 1245873) :=
  block_138.trans block_139

theorem join_00_070 : SafePath step head 256 (162725, 1245873) (1709390, 255050) :=
  block_140.trans block_141

theorem join_00_071 : SafePath step head 256 (1709390, 255050) (1980358, 251258) :=
  block_142.trans block_143

theorem join_00_072 : SafePath step head 256 (1980358, 251258) (1807712, 574911) :=
  block_144.trans block_145

theorem join_00_073 : SafePath step head 256 (1807712, 574911) (243081, 186092) :=
  block_146.trans block_147

theorem join_00_074 : SafePath step head 256 (243081, 186092) (1308234, 1579874) :=
  block_148.trans block_149

theorem join_00_075 : SafePath step head 256 (1308234, 1579874) (441570, 295074) :=
  block_150.trans block_151

theorem join_00_076 : SafePath step head 256 (441570, 295074) (1244651, 1266738) :=
  block_152.trans block_153

theorem join_00_077 : SafePath step head 256 (1244651, 1266738) (1922304, 627199) :=
  block_154.trans block_155

theorem join_00_078 : SafePath step head 256 (1922304, 627199) (1024992, 1390655) :=
  block_156.trans block_157

theorem join_00_079 : SafePath step head 256 (1024992, 1390655) (1572600, 1092096) :=
  block_158.trans block_159

theorem join_00_080 : SafePath step head 256 (1572600, 1092096) (1323263, 1547778) :=
  block_160.trans block_161

theorem join_00_081 : SafePath step head 256 (1323263, 1547778) (9345, 2065657) :=
  block_162.trans block_163

theorem join_00_082 : SafePath step head 256 (9345, 2065657) (1617521, 838561) :=
  block_164.trans block_165

theorem join_00_083 : SafePath step head 256 (1617521, 838561) (267692, 464584) :=
  block_166.trans block_167

theorem join_00_084 : SafePath step head 256 (267692, 464584) (1181781, 1298198) :=
  block_168.trans block_169

theorem join_00_085 : SafePath step head 256 (1181781, 1298198) (79462, 1940411) :=
  block_170.trans block_171

theorem join_00_086 : SafePath step head 256 (79462, 1940411) (238339, 179704) :=
  block_172.trans block_173

theorem join_00_087 : SafePath step head 256 (238339, 179704) (1269312, 1927804) :=
  block_174.trans block_175

theorem join_00_088 : SafePath step head 256 (1269312, 1927804) (1865480, 1549792) :=
  block_176.trans block_177

theorem join_00_089 : SafePath step head 256 (1865480, 1549792) (997536, 110143) :=
  block_178.trans block_179

theorem join_00_090 : SafePath step head 256 (997536, 110143) (1948366, 1475444) :=
  block_180.trans block_181

theorem join_00_091 : SafePath step head 256 (1948366, 1475444) (72346, 1697987) :=
  block_182.trans block_183

theorem join_00_092 : SafePath step head 256 (72346, 1697987) (212356, 1672935) :=
  block_184.trans block_185

theorem join_00_093 : SafePath step head 256 (212356, 1672935) (801751, 494917) :=
  block_186.trans block_187

theorem join_00_094 : SafePath step head 256 (801751, 494917) (626748, 958376) :=
  block_188.trans block_189

theorem join_00_095 : SafePath step head 256 (626748, 958376) (922618, 776204) :=
  block_190.trans block_191

theorem join_00_096 : SafePath step head 256 (922618, 776204) (575842, 1011123) :=
  block_192.trans block_193

theorem join_00_097 : SafePath step head 256 (575842, 1011123) (2094232, 22254) :=
  block_194.trans block_195

theorem join_00_098 : SafePath step head 256 (2094232, 22254) (1479784, 1107724) :=
  block_196.trans block_197

theorem join_00_099 : SafePath step head 256 (1479784, 1107724) (2030980, 657127) :=
  block_198.trans block_199

theorem join_00_100 : SafePath step head 256 (2030980, 657127) (137242, 258027) :=
  block_200.trans block_201

theorem join_00_101 : SafePath step head 256 (137242, 258027) (1797730, 150450) :=
  block_202.trans block_203

theorem join_00_102 : SafePath step head 201 (1797730, 150450) (1022062, 192419) :=
  block_204.trans block_205

theorem join_01_000 : SafePath step head 512 (1022062, 192419) (1108474, 1092620) :=
  join_00_000.trans join_00_001

theorem join_01_001 : SafePath step head 512 (1108474, 1092620) (456411, 1266537) :=
  join_00_002.trans join_00_003

theorem join_01_002 : SafePath step head 512 (456411, 1266537) (1642096, 910430) :=
  join_00_004.trans join_00_005

theorem join_01_003 : SafePath step head 512 (1642096, 910430) (1457918, 1780266) :=
  join_00_006.trans join_00_007

theorem join_01_004 : SafePath step head 512 (1457918, 1780266) (1977691, 767592) :=
  join_00_008.trans join_00_009

theorem join_01_005 : SafePath step head 512 (1977691, 767592) (435295, 296000) :=
  join_00_010.trans join_00_011

theorem join_01_006 : SafePath step head 512 (435295, 296000) (949667, 207165) :=
  join_00_012.trans join_00_013

theorem join_01_007 : SafePath step head 512 (949667, 207165) (861156, 81223) :=
  join_00_014.trans join_00_015

theorem join_01_008 : SafePath step head 512 (861156, 81223) (1203139, 157816) :=
  join_00_016.trans join_00_017

theorem join_01_009 : SafePath step head 512 (1203139, 157816) (1114578, 1703256) :=
  join_00_018.trans join_00_019

theorem join_01_010 : SafePath step head 512 (1114578, 1703256) (1086318, 1610314) :=
  join_00_020.trans join_00_021

theorem join_01_011 : SafePath step head 512 (1086318, 1610314) (1611417, 582889) :=
  join_00_022.trans join_00_023

theorem join_01_012 : SafePath step head 512 (1611417, 582889) (458477, 1715017) :=
  join_00_024.trans join_00_025

theorem join_01_013 : SafePath step head 512 (458477, 1715017) (284789, 487193) :=
  join_00_026.trans join_00_027

theorem join_01_014 : SafePath step head 512 (284789, 487193) (1809002, 191282) :=
  join_00_028.trans join_00_029

theorem join_01_015 : SafePath step head 512 (1809002, 191282) (939054, 202275) :=
  join_00_030.trans join_00_031

theorem join_01_016 : SafePath step head 512 (939054, 202275) (271242, 276722) :=
  join_00_032.trans join_00_033

theorem join_01_017 : SafePath step head 512 (271242, 276722) (898713, 599278) :=
  join_00_034.trans join_00_035

theorem join_01_018 : SafePath step head 512 (898713, 599278) (1172408, 2014508) :=
  join_00_036.trans join_00_037

theorem join_01_019 : SafePath step head 512 (1172408, 2014508) (158817, 1288121) :=
  join_00_038.trans join_00_039

theorem join_01_020 : SafePath step head 512 (158817, 1288121) (824640, 451711) :=
  join_00_040.trans join_00_041

theorem join_01_021 : SafePath step head 512 (824640, 451711) (551801, 805289) :=
  join_00_042.trans join_00_043

theorem join_01_022 : SafePath step head 512 (551801, 805289) (1434855, 439877) :=
  join_00_044.trans join_00_045

theorem join_01_023 : SafePath step head 512 (1434855, 439877) (31429, 2075781) :=
  join_00_046.trans join_00_047

theorem join_01_024 : SafePath step head 512 (31429, 2075781) (621232, 590558) :=
  join_00_048.trans join_00_049

theorem join_01_025 : SafePath step head 512 (621232, 590558) (759937, 191729) :=
  join_00_050.trans join_00_051

theorem join_01_026 : SafePath step head 512 (759937, 191729) (638996, 1146647) :=
  join_00_052.trans join_00_053

theorem join_01_027 : SafePath step head 512 (638996, 1146647) (516345, 1228301) :=
  join_00_054.trans join_00_055

theorem join_01_028 : SafePath step head 512 (516345, 1228301) (1280248, 183983) :=
  join_00_056.trans join_00_057

theorem join_01_029 : SafePath step head 512 (1280248, 183983) (341933, 1167413) :=
  join_00_058.trans join_00_059

theorem join_01_030 : SafePath step head 512 (341933, 1167413) (1196972, 1867046) :=
  join_00_060.trans join_00_061

theorem join_01_031 : SafePath step head 512 (1196972, 1867046) (473323, 1158829) :=
  join_00_062.trans join_00_063

theorem join_01_032 : SafePath step head 512 (473323, 1158829) (935175, 684538) :=
  join_00_064.trans join_00_065

theorem join_01_033 : SafePath step head 512 (935175, 684538) (1488953, 1084462) :=
  join_00_066.trans join_00_067

theorem join_01_034 : SafePath step head 512 (1488953, 1084462) (162725, 1245873) :=
  join_00_068.trans join_00_069

theorem join_01_035 : SafePath step head 512 (162725, 1245873) (1980358, 251258) :=
  join_00_070.trans join_00_071

theorem join_01_036 : SafePath step head 512 (1980358, 251258) (243081, 186092) :=
  join_00_072.trans join_00_073

theorem join_01_037 : SafePath step head 512 (243081, 186092) (441570, 295074) :=
  join_00_074.trans join_00_075

theorem join_01_038 : SafePath step head 512 (441570, 295074) (1922304, 627199) :=
  join_00_076.trans join_00_077

theorem join_01_039 : SafePath step head 512 (1922304, 627199) (1572600, 1092096) :=
  join_00_078.trans join_00_079

theorem join_01_040 : SafePath step head 512 (1572600, 1092096) (9345, 2065657) :=
  join_00_080.trans join_00_081

theorem join_01_041 : SafePath step head 512 (9345, 2065657) (267692, 464584) :=
  join_00_082.trans join_00_083

theorem join_01_042 : SafePath step head 512 (267692, 464584) (79462, 1940411) :=
  join_00_084.trans join_00_085

theorem join_01_043 : SafePath step head 512 (79462, 1940411) (1269312, 1927804) :=
  join_00_086.trans join_00_087

theorem join_01_044 : SafePath step head 512 (1269312, 1927804) (997536, 110143) :=
  join_00_088.trans join_00_089

theorem join_01_045 : SafePath step head 512 (997536, 110143) (72346, 1697987) :=
  join_00_090.trans join_00_091

theorem join_01_046 : SafePath step head 512 (72346, 1697987) (801751, 494917) :=
  join_00_092.trans join_00_093

theorem join_01_047 : SafePath step head 512 (801751, 494917) (922618, 776204) :=
  join_00_094.trans join_00_095

theorem join_01_048 : SafePath step head 512 (922618, 776204) (2094232, 22254) :=
  join_00_096.trans join_00_097

theorem join_01_049 : SafePath step head 512 (2094232, 22254) (2030980, 657127) :=
  join_00_098.trans join_00_099

theorem join_01_050 : SafePath step head 512 (2030980, 657127) (1797730, 150450) :=
  join_00_100.trans join_00_101

theorem join_02_000 : SafePath step head 1024 (1022062, 192419) (456411, 1266537) :=
  join_01_000.trans join_01_001

theorem join_02_001 : SafePath step head 1024 (456411, 1266537) (1457918, 1780266) :=
  join_01_002.trans join_01_003

theorem join_02_002 : SafePath step head 1024 (1457918, 1780266) (435295, 296000) :=
  join_01_004.trans join_01_005

theorem join_02_003 : SafePath step head 1024 (435295, 296000) (861156, 81223) :=
  join_01_006.trans join_01_007

theorem join_02_004 : SafePath step head 1024 (861156, 81223) (1114578, 1703256) :=
  join_01_008.trans join_01_009

theorem join_02_005 : SafePath step head 1024 (1114578, 1703256) (1611417, 582889) :=
  join_01_010.trans join_01_011

theorem join_02_006 : SafePath step head 1024 (1611417, 582889) (284789, 487193) :=
  join_01_012.trans join_01_013

theorem join_02_007 : SafePath step head 1024 (284789, 487193) (939054, 202275) :=
  join_01_014.trans join_01_015

theorem join_02_008 : SafePath step head 1024 (939054, 202275) (898713, 599278) :=
  join_01_016.trans join_01_017

theorem join_02_009 : SafePath step head 1024 (898713, 599278) (158817, 1288121) :=
  join_01_018.trans join_01_019

theorem join_02_010 : SafePath step head 1024 (158817, 1288121) (551801, 805289) :=
  join_01_020.trans join_01_021

theorem join_02_011 : SafePath step head 1024 (551801, 805289) (31429, 2075781) :=
  join_01_022.trans join_01_023

theorem join_02_012 : SafePath step head 1024 (31429, 2075781) (759937, 191729) :=
  join_01_024.trans join_01_025

theorem join_02_013 : SafePath step head 1024 (759937, 191729) (516345, 1228301) :=
  join_01_026.trans join_01_027

theorem join_02_014 : SafePath step head 1024 (516345, 1228301) (341933, 1167413) :=
  join_01_028.trans join_01_029

theorem join_02_015 : SafePath step head 1024 (341933, 1167413) (473323, 1158829) :=
  join_01_030.trans join_01_031

theorem join_02_016 : SafePath step head 1024 (473323, 1158829) (1488953, 1084462) :=
  join_01_032.trans join_01_033

theorem join_02_017 : SafePath step head 1024 (1488953, 1084462) (1980358, 251258) :=
  join_01_034.trans join_01_035

theorem join_02_018 : SafePath step head 1024 (1980358, 251258) (441570, 295074) :=
  join_01_036.trans join_01_037

theorem join_02_019 : SafePath step head 1024 (441570, 295074) (1572600, 1092096) :=
  join_01_038.trans join_01_039

theorem join_02_020 : SafePath step head 1024 (1572600, 1092096) (267692, 464584) :=
  join_01_040.trans join_01_041

theorem join_02_021 : SafePath step head 1024 (267692, 464584) (1269312, 1927804) :=
  join_01_042.trans join_01_043

theorem join_02_022 : SafePath step head 1024 (1269312, 1927804) (72346, 1697987) :=
  join_01_044.trans join_01_045

theorem join_02_023 : SafePath step head 1024 (72346, 1697987) (922618, 776204) :=
  join_01_046.trans join_01_047

theorem join_02_024 : SafePath step head 1024 (922618, 776204) (2030980, 657127) :=
  join_01_048.trans join_01_049

theorem join_02_025 : SafePath step head 713 (2030980, 657127) (1022062, 192419) :=
  join_01_050.trans join_00_102

theorem join_03_000 : SafePath step head 2048 (1022062, 192419) (1457918, 1780266) :=
  join_02_000.trans join_02_001

theorem join_03_001 : SafePath step head 2048 (1457918, 1780266) (861156, 81223) :=
  join_02_002.trans join_02_003

theorem join_03_002 : SafePath step head 2048 (861156, 81223) (1611417, 582889) :=
  join_02_004.trans join_02_005

theorem join_03_003 : SafePath step head 2048 (1611417, 582889) (939054, 202275) :=
  join_02_006.trans join_02_007

theorem join_03_004 : SafePath step head 2048 (939054, 202275) (158817, 1288121) :=
  join_02_008.trans join_02_009

theorem join_03_005 : SafePath step head 2048 (158817, 1288121) (31429, 2075781) :=
  join_02_010.trans join_02_011

theorem join_03_006 : SafePath step head 2048 (31429, 2075781) (516345, 1228301) :=
  join_02_012.trans join_02_013

theorem join_03_007 : SafePath step head 2048 (516345, 1228301) (473323, 1158829) :=
  join_02_014.trans join_02_015

theorem join_03_008 : SafePath step head 2048 (473323, 1158829) (1980358, 251258) :=
  join_02_016.trans join_02_017

theorem join_03_009 : SafePath step head 2048 (1980358, 251258) (1572600, 1092096) :=
  join_02_018.trans join_02_019

theorem join_03_010 : SafePath step head 2048 (1572600, 1092096) (1269312, 1927804) :=
  join_02_020.trans join_02_021

theorem join_03_011 : SafePath step head 2048 (1269312, 1927804) (922618, 776204) :=
  join_02_022.trans join_02_023

theorem join_03_012 : SafePath step head 1737 (922618, 776204) (1022062, 192419) :=
  join_02_024.trans join_02_025

theorem join_04_000 : SafePath step head 4096 (1022062, 192419) (861156, 81223) :=
  join_03_000.trans join_03_001

theorem join_04_001 : SafePath step head 4096 (861156, 81223) (939054, 202275) :=
  join_03_002.trans join_03_003

theorem join_04_002 : SafePath step head 4096 (939054, 202275) (31429, 2075781) :=
  join_03_004.trans join_03_005

theorem join_04_003 : SafePath step head 4096 (31429, 2075781) (473323, 1158829) :=
  join_03_006.trans join_03_007

theorem join_04_004 : SafePath step head 4096 (473323, 1158829) (1572600, 1092096) :=
  join_03_008.trans join_03_009

theorem join_04_005 : SafePath step head 4096 (1572600, 1092096) (922618, 776204) :=
  join_03_010.trans join_03_011

theorem join_05_000 : SafePath step head 8192 (1022062, 192419) (939054, 202275) :=
  join_04_000.trans join_04_001

theorem join_05_001 : SafePath step head 8192 (939054, 202275) (473323, 1158829) :=
  join_04_002.trans join_04_003

theorem join_05_002 : SafePath step head 8192 (473323, 1158829) (922618, 776204) :=
  join_04_004.trans join_04_005

theorem join_06_000 : SafePath step head 16384 (1022062, 192419) (473323, 1158829) :=
  join_05_000.trans join_05_001

theorem join_06_001 : SafePath step head 9929 (473323, 1158829) (1022062, 192419) :=
  join_05_002.trans join_03_012

theorem join_07_000 : SafePath step head 26313 (1022062, 192419) (1022062, 192419) :=
  join_06_000.trans join_06_001

theorem closed_safe_cycle : SafePath step head 26313 entry entry := join_07_000

theorem head_no_return : ∀ p, 0 < p → advance step p head ≠ head :=
  no_return_of_safe_cycle (by decide) reach closed_safe_cycle

theorem no_bounded_inverse (s : Nat → State) (h0 : s 0 = head)
    (hb : ∀ n, (s n).1 < modulus ∧ (s n).2 < modulus)
    (hs : ∀ n, step (s (n + 1)) = s n) : False := by
  obtain ⟨p, hp, he⟩ := bounded_inverse_return s hb hs
  rw [h0] at he
  exact head_no_return p hp he

end Ruliology.CellularAutomata.Rule30Certificates.TrapPeriod21
