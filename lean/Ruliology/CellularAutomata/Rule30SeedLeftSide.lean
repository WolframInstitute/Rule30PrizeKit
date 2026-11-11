module

public import Ruliology.CellularAutomata.Rule30FourFronts

/-!
# The single seed's left side is the strip `A0`

`Rule30FourLeftSides` puts every configuration with a leftmost black cell on one of four strips `A0`, `A1`, `B0`, `B1` through
wheel 87,866, and `Rule30FourFronts` from an explicit tick, but for the single black cell neither says which. Here it is `A0`, with
no time shift: for every wheel `j ≤ 87,866` and every tick `t ≥ 177,560`, the `j`-th left diagonal of the single seed is wheel `j`
of `A0` at tick `t` (`seed_on_A0`, `seed_eq_A0`). So its white diagonals through wheel 87,866 are `D 2`, `D 7`, `D 28`, `D 399`,
`D 53207`, `D 58286` and `D 87866`, each with a black diagonal two above it from `D 4` on (`seed_white_black`).

The left band evolves by itself from below (`rowAt_low`): wheel `j` at tick `t + 1` depends on wheels `j - 2`, `j - 1` and `j` at
tick `t`. The kernel runs the seed's band through wheel 58,288 for 77,920 ticks, restarting at four checkpoints, and finds `A0`'s
row (`seed_band`), so through wheel 58,288 the seed is on `A0` from tick 77,920 (`seed_low`). Each checkpoint is `A0` below the
settling front and the transient above it: at ticks 16,000, 32,000, 48,000 and 64,000 the band is `A0` below wheels 12,009, 23,890,
35,901 and 47,870, about three wheels for every four ticks. Wheel 400 then pins the time shift, and the forks at wheels 53,208 and
58,287 exclude `A1`, `B0` and `B1` (`shift_zero`, `not_on_complement`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SeedLeftSide

set_option autoImplicit false

open Rule30Diagonals Rule30FiniteDiagonals Rule30Realization Rule30FourLeftSides Rule30FourFrontsBase Rule30FourFronts
open Rule30UniversalLeftSide (stepK rowAt stepK_bit_zero stepK_bit_one stepK_bit_step ofRow)

/-! ### Running the band -/

theorem rowAt_add' (K v a : Nat) : ∀ b, rowAt K v (a + b) = rowAt K (rowAt K v a) b
  | 0 => rfl
  | b + 1 => by rw [← Nat.add_assoc, rowAt, rowAt, rowAt_add' K v a b]

/-- `rowAt` by halving: `bandRun K f n v = rowAt K v n` whenever `n < 2 ^ f`, with recursion depth `f`, so that the
kernel can evaluate long runs. -/
def bandRun (K : Nat) : Nat → Nat → Nat → Nat
  | 0, _, v => v
  | f + 1, n, v => if n % 2 = 1 then stepK K (bandRun K f (n / 2) (bandRun K f (n / 2) v)) else bandRun K f (n / 2) (bandRun K f (n / 2) v)

theorem bandRun_eq (K : Nat) : ∀ f n v, n < 2 ^ f → bandRun K f n v = rowAt K v n
  | 0, n, v, h => by
    have : n = 0 := by simp at h; omega
    subst this; rfl
  | f + 1, n, v, h => by
    have hlt : n / 2 < 2 ^ f := by rw [Nat.pow_succ] at h; omega
    have hw : bandRun K f (n / 2) (bandRun K f (n / 2) v) = rowAt K v (n / 2 + n / 2) := by
      rw [bandRun_eq K f (n / 2) v hlt, bandRun_eq K f (n / 2) _ hlt, rowAt_add']
    simp only [bandRun]
    split
    · have hn : n = n / 2 + n / 2 + 1 := by omega
      rw [hw]
      calc stepK K (rowAt K v (n / 2 + n / 2)) = rowAt K v (n / 2 + n / 2 + 1) := rfl
        _ = rowAt K v n := by rw [← hn]
    · rw [hw, show n / 2 + n / 2 = n by omega]


/-- The band at tick 16000: `A0` below wheel 12009, the settling front, and this above it. -/
def cp1 : Nat := A0 % 2 ^ 12009 ||| (0x8000e9f5c816ef365d08e44c171b88236c2efaa38d7d08ba1585bfc4b556ec85df1f6da856207fdedf71728078affaff635a246c40a1740f0469d0b63beb548269c05493bed4c339e4cd350aa37615261ed3a7be9a5366b5ac931b86009f1e7bfc335eb38511d871fb66d2433f5ac2da84903450281a34ef7a347d39a78c9c44deabc03cdc9e3d491e090f3134e969d24df6710fcf90c93c512206f461144647cb2a6275684c8df6163fe6d2b09982b655067b964446bd6b4615a80577b0e58ec0d38ba2a9af661cf4ba3e1c1396b73fdb4f3d3d463d6ab2f330c4228085ba3be737237d3872b3c47af36bc1e0bffce7f7cbdc41a287b1c085702856edb5a1e20eb7aca737f95034c48ac05b77cec637fd8aea7f33654445e2e47cb77032a80cc636ea97e2361e92e9cff0999314e67e7b4d9b9fbbc6f144fe1deec922b48a87c5c8b8b70aaef44e6992162c84d6fff0175fdda973cc1b8b3bb03f0787f5e37cf3efbf05b894905dca4373892e0ef2894088a3ac042cdd2c88a381c7c99c3ce1940af9b909c5d6bedf282a7e5c9aed4c5c5c4264c22469d3a1fa9b664acd2468ab6f543be2b855842b0d6c151e92894c3a35781e33a12bb4f73dcbf4a541f533cdff8dc0e567ccc7bace08d6187da25b5163df15bea2c2268e4b2cacb3a4b29e91d6efcc7a14005d8eb9462cd7b44619d6174b4e244e8d01a739d4802c116a4440f32c97b1c6a9e36f58daeae6bd8674118f826d534b7508f1ee67f26e40f2c8401fa49773b689df0ae8c648e5c4f5df129454849f12f7262ad79993ad8d1058894729f9b012061fc92fa8d5c8ae599de6ac2a8d3c5526df289a6e4313c9f0ae8111748eca622c7513a59794bbbb04c80daeb90b0231fe97ae7f0ea9f1fd1acb72ef53b795bd5b0a2bd5e773a30372db64a55ca010b203f597d0a966b60d7bec4695a36a3fbea8efb7b75880ce2083574f1adb9c2e41eef33258e77e9846a13a96b996e9c713f5a5a0fefb11e6fa5d0da8af2886d27b8ab0bb96588215b1dfec3992a09edc7f621dd0ab70869d17f56ae8dd75ffd67d0e873574f56b56afb7204ae885e6fecb15a3a28efe730a99454c1327914f98a60e6bdfc296fd0c852330f5d672eb83b3ad928a83bf161ad68116b1c6133cd639d56f7426ea58f464e0bae9fd8e6fe92a8d98439606ac3a6d6520cd1e5445428c3afefb4e2af667ac040ade10f4998752bda9af52eb1654da0dacac2cc0b082cd6b1473330d7c500b9ea5b61cafc9d2476a1d7d70e07c999d4b159de408e150697a80d849fececfe6de6ff1545e7d49b5b7dfcb163139f21ded0a71abefcf442b85e9b95e5a818b435dd1bc339fc6d223ccf0bb84d103d918c6f9c0b923a67261294a42a55a807b8741dd8a981532766aa9ed9fde70540b4f071730a1a5e0f105810e513ad6f41f845efc871efde9e68b649e44e89a69e94ac1ec182b11bd7fb3b47213e039deecc66dc3c1dcb90c48460a8b07898300e418e96be0ebf60326ae0edd156cbeafda23fbb3b728fc1e6d722ecd0cb205900a07672791b29a9a646d0e72c54f043672b085ed975b172dee03c7c63a6b9226d526cd39481a4231d922b3b6623d01fe7bf2714363e543e8f192c8b652d6110599667083bdd03267a01cf150127024976884e6396ac6c494bd31c8f840e81b70aa1cb9ed3e98319553bf68520f297d7c0b2fb9615b2a47315ccda68d88f162f93dd6b69ca6efd87f0c0c0292cec7bdde1906eca310d16a7fa3e793681e89a2b26b7887a793d815caf69c5ea795f61215ab8550c58394e4af5a47450d10992a09724c535fd56f1019d102206fa653e8cd9690b39e3faf4dac5608f92a4b195d9e86c9e570a336c824567a7fd0d7df34db1911ee7f7171c5ebd253778e354a06dc670f7e868ff94ccd3277a0f8cc0d223fc3c64396cbbf6d4faaddec84b109c7c260d406f44f30d876b8e1d7db2f77b3156ff77685a1ba858fbda42d950cc6a8f02597649daf67c358dad0528db70a5923096e3ddaf3218f9f9a79d649fbea6dcf30ffb9efba103028f2ceb176d0f2f9ae292da13b0ee5ac7c82f108802c2ae2f5488d70e4debd2aa2327cfbea07663000ece316247bd131704a0d68dda77163bdfe91ce50220c4d8fcb5073e8aeab928154621bf1a25da1de0dd93f9b33440fb10cc186207aac8548ea41137d9101852d2075f81fbba6f2473f9d8bcd68026f43ef3448eda6bb0d468177723348aad8bfcc48a5d28248c33b19727424100990c5f3b9327cd4961df9a7263c9d5cc3e156845e6a548857ef8c4771395eff5d40df998159a06add70fe57f1d5d93155a6cf62e1be89810b9badb31934cc052c2f66a162dbd8a6df35bc1180ccde467ee30c3284b1f7444a6d6d6cbe9e3e2623a5ca93b6364519da9a2c714dd21fe61533640a0043bfe4aec23cc146017456f7d819f1e12a3dd53a648204cfdc951185d45a41be31ffe0dfdd043ddc858d8764aeab792f923adadffc8262da696d844637adbc5debff4f4db9a0b0730f834a785f76b3ae51511f7b85a973f3f8fbcf5e016f848f3a61c7e30e4ea8dbbcfadad06f6507c16ba33069f30e66de6afc5d634e36b98d11d9d7cd8a33c04a5188fb1b31893ccbee2b62eef22438b4ba67141e19a5bb8c9d706f6083f36b061795e99dee6a5b11c076041e11b26af63849ece3350765cad6517ec2374df5fdcb8f3fed5f5f663040bd7b6ac0d8e1f6ef1a39015815c5229663e8a40b271527d305f384633e01a02197ab79c2edbd235007b60edc80d2f399173166f74db0d9b4efc01aea296f6f65498198e3a9648bf0b977ee7f8af00652eef76fb6a9620f9f9d37465f063bd4d93a78849f530f29e59851cf1f74717c8495feada3d09e0b79d9b51e7e5f2cd369de2abee8b6d1a3d02a47777b6efd3f04c9d253659f1dd569d69da82df71f425fce1334dca4112bd926d8ed0d6ccb88f955ee253926ccdc283dfc3a667cd42b091082ea231b36e8411846ec1702c39af4c1a288972965303cb263125ceb5df239418b5eef3ca5ac65460d17f42315cba75b6e78bcd8c9ca3412cbbdba49bf84448bbc21cd3f9e2649b23b281392dedcaa01e5253a76abbe91f164a13b751090a5a0d350781cbc5c73aa7aef8ac4801df3ad0e2ec7524b558622d327845f2c0305fc59a9a0449c65d374ac623bbf071697c2000e7ff7c017c5f2ede4945715bafcb7d230d3f80867cdb089ff77dd87862f69f265c918ff3742c0fd226364e7a71540f64ba72294848257ebe4b4a7123947ac1ec88fcf46a3188cff90ddcd5a36d1e9e43267bfa2db09ea58f0c2124e436a58f43ef3bef40c9426f07eeec12b09d6c81b2e9491eeb0417b422460e0b65ab021e35e703780982f5554ca778e85c410b60307315039ab60b598824067bc41d6887c188f90bbe4b26d4e12770194ce1a555dfcc890822404fc32397ae4b9dd9f4de80a0242c16a28c5b18cc3150dabf8bfc5a319b9eda40848ab083286f53d97f15a775e <<< 12009)

/-- The band at tick 32000: `A0` below wheel 23890, the settling front, and this above it. -/
def cp2 : Nat := A0 % 2 ^ 23890 ||| (0x76086d579e6aee81158a0ac9e368f499862140e64645d59dcc715cd80fa5a69a0865f226615cf8d63ff30c6c9654f3c3ab37f8062479a0c7b68b4a8681eaa05dc8738be05928325607ad911644b9113c607a17e8e85ab8e33f560d187559f91ec644975a47204215a6f7269e43519d234311784366a2f2c3790e05007cb37641e945b6a5ce9a2676d80b6b3e572192cebd2e652a6c3e272ded799aed404c4dccd295025d33c94c63046a75cc15741a4875327201cad0d4024afa43e0131fb986849e3863c530733589e9f295e93df5c69254dd6878f580ff542eef2ba2d8a99944c3cca247e68ca3d16ae1e0d119ddb0372eb7440d8cc535377fd3b55471554d139ae0c9a089e54f593d5b30629a2044124f5a58c28e18000e215655837bf868de54861aa9518ddeb7d50f58914ec17e0ce8c8446b2c4f478e9f0b0652a1c76f7e24760bcc05b2a6acc9b2886203bc1921ac202a88ec3608333dbf9630deaa1353ab149cfa5dff638206d9b483f19c47480193577d4c712ba396d770d3d8aafb4f8449d820ff08a3fd2375aaed71edb1bf00fb3c9a9c8fb29cbd2ec153bd067b92fef6f9f430cdf9e9bac37dcd78d057f841f2bbf85d27421ed0d8e74c9f454bd0a78d5be7144c1df58d76b58e965117550f0577ae953183b03d06e9c51b4293d57fb19ddc51383ecc97169b4a07b410def874f8ab35a6856be8854feab061ed35a647b1cc06927d9fb28407acb08253ac2509123854cc88256528472987e81475ab9477a0dd8ce9be66d38b01f6c9c0ce0234255b28e61b2597383cf05a2a310fff89f8e4fbaff39df65f0d80db5f056b28b5ebc2f28ba5d489a6965cbec186c6b7826c9d608602870e74e480ab4618dd9fd30f8bbcc00437d98edd53a559c1b6297d608e68aecd14be2b02c8c18070d9c716fcdc7d53bc53e86ed14e597dab7781e59d1abbd44f6a32e53251106503cd7e6121723bc4cdb1cd34df38fdd7cdfb046d10a75c4cff40f6b1264eec754c01657a850e969ef0bb1d8396403a3104960debb7e7a1a4b162e3ee2741b020664184bfc26a19b3b8f4f38eca0f99548cd9c0035b655422dfd18cea63152b03baf3d2c37811b8c93401e647af838cea31b755afc36c00acb161b2a8e0a1f893ad5c2da0add2d52212cb61aa88161dae6ee069a98ef705befcabc888582ce173c82043a0b61db4bc777f2143c3ec6fd58618d4d60a4a1d6a0db837f7372ac6e12d5bcdfd1ce8d97b38920d5e23c4a6025454267ec2796da07f60e68a3c5bc28e6f336dd3836073882d3827e29cfe36dd569278407e1c047f4c429f00fb39a8e2baaadc058b270f028243cdca00a7d46c858e544630949b310e7b78af19312b9ffd07fe9e694b2ec3f11a478792ea4729a879fc46f4a1136cf7d34225003951da0467bb8ea37bdc57b41ce7e46a76fcf09c44266f37b8808efd3e29f41164ff3bb8dd47a0404e13525085e26297a620961a221e68a48464995debaa4ff30faa33cab1d15d2f2aec6bc0a0b1c458d2260601039b2515ff59f2b8a9184d904cbae64c226df4dec2b5dfa903494e65c2a5db738dff5c37cdb50609687d56b6c50297c7c58ada1c1fa212ff6a2ad2e6086da03116fe7b1384011d9d73d6ce93bb319b34c2261a15fd137d1a0e6578f60d884a6c5d3a0090c8dc9879ec17073a1b85bcd5ae435e8422eeb8e04f4e4e9760276c3522ee90e3c01e3e09a1abcab013700ca8bd0f8085875967c96b59075d217a817ea7aed4f2393761ac4134bffa5089b51a6e53164db88e99bc3c37c530347c6252794d8371738f96b7b5ee1bdfa77ad44c998a47a8d5ed0423b2b8ffa746d506b50497b846aa2b84448359816337f90140e866859c74f9b57b74a64c16c47c002ee5c4c52d806f990a5baf7b8bd40769739c342d78ff7610a033004070a145933513a91be6d780527735680e03d66b4ffafd9d4b91f1d3d12c1d580e067449fa0aeac4c628dc099c9f2d3cc94fa91c67b1b67b90ffcce3756f3ead8905fcf9c0685d463a9170e471dc8b75e7b2069f7591331cf18fc8e64dace63892b7a9bed3298c456dcf866a1c7a45f66fc9f543468a496b3276ea4666d7adc6616c4690f9f1fc6da9a08fe9c146392f4109f0402418e49ba907db79de033f97cf175e239275a343f0a496043c246f9396c10ac05f02dfc32c146219be80d81db721d3ff31db6e6704fa24f2ebade471e6f2ac5ee5d403bbed0a0f4a656220a68fa0093ad0ac55d0b9aeea855baffaeb022f746768fc7180209f7dbfcbfe4f297eb8fa0fdf9a89babc90ea4667307b11ea4bae764528e2085725f8dc80ebc93a989a60b599db8798943227bc427866bb89683bf836004f2442298478a413e7fa503802771005a635eaccf48a141291265e0870f217f0ee37c87164fc41505457e93de75a0dc63280fba4d3c3d3c9f638070a763fbe6911024ed23adaa423f35a6167cdf639ab826931acae751ffc80a0859c442f557865c45c048d2e79833216f66d27d0e33be5f7f1057ded6ac08ca4d50beb0aad2feec63042de09e5c489fd76d20ad38c21d8e90626df40a92ff190663f9c75a800a2472ea8b76844cf95e69f0b5bb178cc250493c092927c8e7b8cd632a472494c171b08c7fddc52957e42ada6f9059a0eff707830fb2c83a2d6bb518f3f5de7da31be7e3f1baf8798381b1af826ed6b0aeaa6b2970a2f7eb7cae6fb55e3f0c25c8375741f2bf00925db1077d38ad70c8f986b6b5ef6293cca6cf4cc35d7b41497a49e87238a2c541997c63701775479883880e09bfef7597af51167774f480bdceb09f64f6dc855266decaf1cbf03fccf893ff34ebc221e651c4455147e2b2ab2893043cdf95896a132c0dd27516dce60907ca9b3ebfd0ff787f3c28d46576caee4f716dd36cc804f1c68f155de2c1bf15d183872eb5f9354a6d347c12689ce776e1b41acb642a7b13af467b60da77499de043573dec23a791e2a8e4a089b34ffbd099e9d65f188a18a1ebf5cdc6278ff683f7b97e554192d9661acbef9054d80b6953afbd9671a7ebde5d0da1f55d7a84fc4a762b5c259109d4092de5c0a6b8c3e8b9c3efa7052141b4675b0d5b14dc196c9f1c4289f1bef24dd917034af98b8cab1e5a63f476c9309525a8f914ea4bac63c68eb937df7434bec60b31f07bdfcb81962d38bcefb4be92ce19434fb55516770ee895b1836f0a53c19b18ef786084fadd46ac776b19c57981c44c58b43275cb43a476b371a00f2e1285ddafc9b4c37258acc476be15dd8a4bdde4a20e45c35febcb5d8ddbbeb13f7ad6ad90d68ced0e88da64dbf95e5b6345a3f7bce3bbf616be64de44dea769b5ff7b2c2c5961c25eb66327e290a0c1112742811c10223b35271d34c1a5b41c870b2d6608c1ff2b23b4db9717fe7cd8c20186603029fa125f416b82840ed4f9305a66787c70cfeb9758015ce5e16f26642889ea87dcc6c5905f926e84f0e7613dd3c1d050e16ec10f55db2f508c75ea8788e041721441183868b0d0939376b431bf103e96f5b9d0700cf28d2d12de0956a1d2d57904f2278cdf8025174f2c67ca7ce8b4faed28a129f2055561ec407839285651ef0148def7eb22da97dec546b99394f5a16c4716f5710601f1af7320a82abf570fc41ac05a64813b54fc24639931e333c1d712ef40692dd6ff00d4485cfbb6dd8c2e0c53ae8bcb5a5db1be481e6a0f34e66b92f1b4f748723eda26b0ae8a596389867c4f20fa224584c4924c0f673bb30443fe22e2571e8fd356eef638d40ed1822b366ba34ca98602812ac245acf515b0367cc3828c5675982fedf0fee653597f34a4dd280f91ce4869194ff9190004fd8bbcf08a1a3a96949e1d766dd9bfee2de60af2b2799a22da3d9e3d43e493a9dff5e897cb951e0b662930fb8e6c607d44ba4997d9f63c6003db80c75846912d87cde401ba9d65ccc52dc1758131af320209558ff729383f525fb6a2352af2ae3bd29569d928fe19836b122807ea2dfd3f95ece739cbb59bcb63a7b6a535cf9e952a6538a43da96c56251ce52087a2d9a2dd6602d078ed2b27747a321344a7697730bb867ec60bd9acdf0c9456af757081ce80b337bb1844340a58ba8112af124223a69ef5c59023601ae05ab0835672c087f6aabc556f7c5790497b3d864bc9424ace9dc77f73c11a240d2d31d4a0da9b2d4eb38ed5e068e637c8f9a83614c274797d5e9f8ef42356db8f9e2c896da7dba6ad7ba1d8217849142ae9f0245d8f7aa414371a1e874d24f8e911dfdf5ce3a426886015eb7eb95e9dfcc25179d15bf48b7b532b0eb1e05bcd8bb5b13319c0c99eb170863fbc9dca4e2fb88c8e00f42f8ff7aca9227a6c1355d113b25443613e61bfada882d7302bca5b8d76afaff43bf482dc092b7f3e59fcd1ad291be9b5941217a69d14eaf2df3609e72a0961691da67b6bf4811d5f6f2658af886223c27999ee25fefa16d45030cb1d6bdd40bf8dc4fe1bf4f251e694e1aaf8ae179d74f56d00231f5cdddea4e40e9b86cb9fed3f18fd0dec53145adea0c50f47edd7691bf50aec262d09f98e25d002a25ee28cab9aecae4115f80ad204e0ce99545b71b69884c46007784cea1bebf7c719ea0687e59654db9bb096aff8cd31244bff1bd10694cf5f437bc29f4403fa624ffada3873964a40117c983cda768a460a34b4763ed36db398811210de4bf32689fef881e0e5f33cb4101416023235e8eae7eef29d75aaede25e2f033dc6c8aaa3bccc5d077d8810e8ca90f7741b806c19277ceace0ec4694c49f13accd1286a57bbd6e348b2835efa84777eb29ab077d6076774d686a1f71eec6c178ef0e1bfe553cee0b06a9ee42cd160ce84111e52ee3cf991d087d367129f786a3ebe4fe92bf20f58ab6dfd834925b7d9f63927ce4580ca12e9f0a694470b39e4e9508c388c314be33b6a07faaa831f1da23b6dcd9ed193bca57d8f2b1b3e5bd78441b788b70d70f99d7f65b939f029d75ca61bebf0e86e0c9f6245536e9a17675d46433d836c0d1bbb3ab07035e08650976fb0f1dd65e7ffe1799f4f2b5004da098004ff689d2b5f64809a66e38751cea31fe02536d97c6c82eaf8392b79112c1559a343ad80d9f4a86165d979a0e71dc9c94465ae8970e0af2b08b9fe08496ca251b67a536f4e79c7b66d0e69130af18790458ea132d8f68e1c4d89d76cc947d603f9c4e982e541ad33aacf2b82d60756564a62e384960884b157bebbb6cc24b79c2f4b3c35c47caad09470dcd4f3f4d337a4752885b5e35891e5e6ddb3eceb8d8a00da8deedb78f977422156d249414d11394b34fc839750971ff1a4b1234aa82c9dabc02c8865da475b3d79525bc4c6b8c60ee6c8a2f6924e7a712531cd1aa05c79126be4945e9a2745b0e300dfa6f2a09d795f1fa0516063cc82eeab8a12f46e5b02ba050be6c59802159102c86f0b2df62e16c0786347514db820c68c3e3655c4288640754b46dbd38352801765a84557f091bf4870416c69049669935d0e23f84779e738fbe3074ba569f2e88f9e33e606dfd59ed40a9c56eb840203013bbde518e5e2c5227839be828baaa9851cf6b60c0835a9d5edb4f2dbfad7c80b0251e06db669f8b9b5cb65835f0945201fe72b4cf36f4cbae8f793c22601d5855dcf7d2c135646284d2f01664c20ea77c6fccd33a12fb1730063b4ed41e4ca650dd39f6bbc398646eeb26b246da0a38fdd28532d4815e9f502805dabea34eae7f74ed6cc8245d5e1ef982e22f493bee92d3416f6cead27ab81b52faf9721c71ce35ea5c282efbc8c3ec50364c347acab06dc4fe757da06b1b58f2adcafaed2bfa370ecc36334c6bfa357812934b5d14b75fdbd3cb9b6f36ac3ea629c9c393768a2b98b01c1f23f6e8483d807e0422e9edc1712f0e830a242dd872f9274eb2c523dbf7bcff1f585ac7fb1fcb8fb2fdc97b93af8150b126373e09ff5eb8b04191d1173b1a2ada5b19907240b77f196cee0089b1079540661062a39c3bf82f422c132896ae9dbd77e00b48c2488aba325a35e8e7373a81724d30ca505207c14b2dccba73e4ce71d6 <<< 23890)

/-- The band at tick 48000: `A0` below wheel 35901, the settling front, and this above it. -/
def cp3 : Nat := A0 % 2 ^ 35901 ||| (0x9ec00fd773ba3169cd1f85750518000cac7452fd98bde296ae165218dc9f9f2760ecd07cf28fafc3685c74c53f749f438bdd082c53a2a93a66b4861130a373174b939a600e675407a4c320a6f16c23a0d23243322ea2ebe85e8542314f514dbe742ec712b8d3711bdf7b669773a2b3fbf86bfad0a4149ac6ddde35f9af6360ff5aa8a7008f1afe061866b260a18352874c730327ad86b5a0ec3badcc901eece89edb98fdac129c2ac78ed5b06a5259e9d3cf1db649fa5aacbe17adf88aa413a0a8401f79a7fdca9c511db9a0a0461d8d309ae22a318be87b073c442561c3cc438653919fae7865c64ba2569b846fdf981ed38c66853834cde55790bd886e54f44826dbe02294706a343dc3fa60d2213cbb5fcb2f18672dbf2b06329dec1209c36348a0d19efaab9ca0a957a22e4e6119d6994390d4733161d776f57d4fadc59f64dc443982d2898000b4ffc6c6064db9278dc98013af17284a7cf7992900856514926e8bb1873af7d02fb4138f9020f4e314ed8b802647c9868f0d84ad2a590f180f1da57c49337a787f7b5405e2876107b52070013bf25f23790c3ff26f1a69815eee42a509d67d81d517569df8d5a915a61653d72df3ac78f8e51cec3734adcfcf5fe91144e3633368d3c54512a0a8cd18c2baae58d03eb21319eadecc80576a31df75751e007275a697da57df88914d3541691a11f9d4226d9ca618bda469e2e358a085d65df2c27459a73d0a5b512972ad37e18b61a7e7e6203e6ea9b706e674cd681ff9e7900ad87dcf1fc2f6d0f5211137f96e9879807909f039fe4fe4d317c3e4e0cd11dc8ad6f0b6048eec5fe004471b5d3d041fec72d6dbe24ceef1d1f1b5c9c242021559a8e0fd6f6de75401d5d0848c7e16abd425fc2638c18c53871f3a55f2b7ab60c362e7d4f322003a738672ca6c6ec164b114f8c0211a680152d30bcb07cd05bed928dd671ddce680c4b95f37015ff7730fcfcaa5e75eed7c6ecf73145171c8c123a5c6d268e37312f74d19061a22e56421a94f36a63a34c70d5d10a533ed73d55a3a2e82952d50f7dcabf58346dbb1c376472041913e0d2cb812484c0711a8c77276a922de7ea03987ee61f07f2725aa2e288865e4b6cef144c528bede92327da9ddbf0f422b4d014ed45655fa8bd132683a59fa5c353b9c99093d183eb93a18a7e395c030d3a82a185d76c188fcc90cfe91d1cd288e2ef6544d22dbaa0167142e5ffff47ee5daca3c5e3dacc42deab4de3b1373600ad5bf5fc89c2f276a8d825a6ccb6758bc581fa3fbb1f4f6554c6c54cb07d3a4336738f056ace492519418e7ca322c55028c72ec73af46f90bd155f575be883ad1af4d76d53fa870b296d0be9d9823aed3c576b1207b3374690acba06bbef597c13584b47245e061266f8af62b09b20950e6d185b59a31bfd18e77f3649386f0a87627d705bc5394cc03a8046d61386e8c14f3523a4fbdfbfd375113741e6321852c873ebb0b8ce718bb395ea070cf904bf971eeda0d2a0089da04ae6aaa37591ce60d36d3b850764bdb27954a0b47d22de30e9d2f28dac1d01db2ab255da5fdf0730ea9f056779681d6398d23b91e6fa4dca10b36f12c22a2e24103acab7534cce7bb9aaf2ca132a6d147124769e27b40ea515a2f79d37c00c45606b568dc5be6cf82f08f32f4f8accdc8c74d0d90ae2958e18ed4e23e9305f49b57f212b6c9165e506f022fe72b6e7703ccadf8ca7ca8076749e4bf6706dedce05aeb152db12422abdf4b3c995ab11243838c02a46078c5265099fdb71bb3f06cbbcf433e5e587904164adbadb5c500774e4fcc3d40c21c68ea5095b727c753651d4cf541e10b9baa7e09d5b69114991d03ede52d7ab089c09c111589957ff3502f5692b8d1f7a3836fa1d5325ee61e2459dde4fd70dbf986232024dd32d65506807ba4fb64815beb6ecb18ef36c8817e081597770a740ab50501203500bae000446593210c470c75062dab2d059ce9e1b7e87404a3ac35a5847f466e757baa58747b40872e2b9b82ecddd2c616e6ab7851bfa9874583755b59c2037dc47fedc96cfbaa3d4351d3853aa0ae4b349f88122cfff8941e24a20a18638224a6c37b300942861965ad3bd2fa24a1d3af28c61bf3088d2bbecec494646d47d6373e516eef58609244ed09c408663b6f8544184167c466418894d411b190087dbf653c6bde1e289a1d952ba2b65760eb24a7c871c7d5847c8fefa1f49192dbaa0ab31f65604dbeae49b26184cb1c1fcb0a2cc795c17d4ac3e9418503e4b2fe06e100ec06f1085f52b3fac70cfa663cf410516b6c95bf5991dbe0bac59251a9ed170b588111cd15474f97a6fa315c5fe3101f6646bfd233dc8cde8dd0288b076a7124c8cfb565aa7fb46e771071ba389175bd7ab403f9606ddd8d1c50d3bd9fe037f61a8330b46cbd3bb50c544939a4c2677ff873dfb57f53a40678af8968c07523f70408170388b4b0261671b4174c5a587247adf02902071a15418b85e0b1e20f1075c393e088789a1f07197eed12fb2d0963bdc7440dd8f5dd7adea46bf64528b254dfb6eeac280c80dac6e0662951a0fa8ce3ff7b1b8e325fb189ae7f79ae93fd8d9ba2da75bdeaef39ddc29b6f561f109002740c35d587f748a5ee3c450718eeb588a6f6362027884af39b28dde5513d440beec153f584d2d17c2c2e8a1db38eeb2612aa639d87f13e7ccc636ac5f28607673b68fd9bf08e15a53309d1f9b355b8e01452e7f14f07e04e74c40d19708546ff9728df8af2632e0e8e2b64dc9818926f50a4246aeea4594403924a4203370f2b0472968d7065bf5217856f2a08e5b95aed5ed8fb7372ae37684f535d6b3d42ad570831837d734365880016fc838490789f6e00e7a4d2d15c8f546d29b53f77cbff6eb52efbeff87ed0e2e87e8664fd1fabc1a488c97b8d8c66b59d91d4443798ead84fc5635691f801667925be587e7463d49948f1752f1651c8163514d2c53472ca63724abf35d8377ce6b14789e44c41b4b02260686d2513704f8f5d31103dcb1f581ec10278b43b78916da98b23248ca8f2b880c68416aa661392038719d61da1f3a23ee6fa528b0bd57a3db7ad704cd8873f69345e373c152ae57a780444abf643e56b4aea806c5e4832b8fe1929053303f5f098196b14dca5ed666d15052a2890c88a61e3baf573d5f62057c2b18a35c754db1953c7c16110c01d62baa682adad6fe0c3dfa5991ffeb56debc944b4125dc62eafbf081148e2807cf2c35d21ad99d1ca6205b0b3f12d2ca95b4c2deb6fa6be5db32739a7ac133b7af7351b2133cf5a40d708acc83eecced0982ac53b8de35cc7be5b86ae58dbf1cea8dce31dbf72326d341a242e64329981bf7b40eadb9c88e35fe318f25c887dc83775aceee526685b8985e642c2c5e7fa668d774ca2ae69734dbc74276a0a61e5d7725ff8abed83a6cfc310dab9110d4c66bf14602711dea0ce6b50ca45283eb075c890a8f0b5d9f22774b3c079c3d8accfd9eb00b857647e4a924130e8609344b5f7a825a74f5e820331485c7edf9d0117725fc7986b88b6101b4d16789d5eb7916054d62531ccd556b7971930513df43137cebf9d9050e0f9ead52e012a28a9bbf9c416cd69e86e6762860225867af4ff85bc335df4d0ee5546431c697dd3477881ccb162ad1f43e734840b3d62eb28318a806103a7d852c60f879afc771f29ac127321680a5487dea2e6c82a54239d58884f26c1f820d56d31e7237d482acad0c7db252046b7525916987b63cf8f0a5a2165ed0a59ee0e9b993ef2302a60c5d90aedcfaf43171fea48b97c42499373df9b2b8e19cd7e6a3afb61ad0b24ae8f172e38782384201f10c15d92494e9896dd3fca68b64d25254b623f79814245322d2859e0e96660acd8dbdd1620b643513983851460a43397beebd9a2703822d0a0c34530cdb09049868 <<< 35901)

/-- The band at tick 64000: `A0` below wheel 47870, the settling front, and this above it. -/
def cp4 : Nat := A0 % 2 ^ 47870 ||| (0x7f63aebe3c2bef70c39a701cc0bfa861075ada3776271b69833ce2fc3c4a352e0033dc4fb4af0fed4243a815bfca8a98d21f7186e171cc44ac58337edaece0633ebc638cfc2cdabad19d30ad3b94939d8de1e1277795307f51b1de6899692b4bdaa654c37c8d401a21b11aca9b978bb54cd78608db2ef3b21ff9e0cd46b0c212aef7f2bfb6044684ddf68273d6fee00f73044ebfcdc5bd9b8fedad75bdce95bd74ef5e6a28abd0e45a1feaa79a40a9354c1f1fab587aea26ec2773cd4c3a5e519c4e972b926bf498d9b6f538bf8f97f94b9363b112760e9822a2559d22280be0bbae13360566fb826154fdd0092d276e702a4ec68676bee681acd5861d285be691b7f108fbcc0637d2567b12f5dd47d4d0f120ee9d8e44cc190b8964dcb5236454b64522b7705d02cfb309cde2e7383221cde972fa8299994e30d08a216d5b78192fe3230df4a8fb4d65c078425a884f0981ac66e1ff9464ce160e70d8607e923c888d82d36c7fc7d8c3c01a5a6b5065be1f6a11b733bd192249ca3c1e90f8f5f0c7c52b1647b0def092c614a1c2058a4b6c54bd95a6137382d381d0a8f4b752f1273c7ba61b9a6611713d0f2e623f8189aa140dc6714bdcfa97462de6e7e2bac9a3f89b12a5fe116c2b843f8289b8f88a75b0d5253b335213e9a9656741a90fe4951b897d7447aded74f526d99b7bfe744b0e079232a797728f9a31fa1f4d14f89f4b41da75e0474106d7f9762213fba9265affa2b49ecbc61b1d28c713528d283951f1c8f6b4e890682c366ec1eb7dd79a269a0f0cebfd2edf39c6ecf3575ce37fe7fbae979a707036cf71ad643e6d1ee3425d1d77f0750b0245d95b411e9c0c4e2c3195a449782c2d1e97776309214939a45d68f356e8cdbcfd432ac6fc6ab3967997d16e251f699169577ece88b4098b59da9b35817207a18363285ef457cfb1c5232779be0e18ad875af147bcb12c22ef9d7a4f7249aa2c2d38d42799c7ec13845861f2186845bd3bb91f703d0adb8b7f0c7e66bc7e9227982504ea7c1b2cda460593dda45b22d0844444c2fbf1377842d9b8dd3de9cc274dd81325d0267f6a6612deee9fefa0d4a000312bb6fcecc455e75182a7abfb6fd1ed49220ef3dd2c7fa369452b6f1c6c098b32f0dc815f7dbccdb0e6176048ca718c54da3ef28c3cb9ce4730b6efac58e86057f0912f1e5d587d87ace0d32be6bf29e57c11ffa4ad769740f2e428c48e54fb2d0351c926a423a8e7e6dbd922bafc8b408ec412c05033055b13a5c81e3d88ac6056d065ec5b182821ab323498db4ac29c6d09d25e71d19738a62e15dd285700804af36fbefe10d6ec3b2f87581b2dc59fc081ddb5cf4f1697a778683452dc5714363b434378a70acb83c53550a410a23cb9bad3d30565031fc16f72f2a62bc34b97d43a85d59397a0c5a0c948d38477b1adb142eb06b7289a5567acd88ab294e4e937e7960bb74aae682c2fa9b86815a73f3d16da4f17983a93cf9b829f43764f26c144510ad4af7b3efbf87a341e52a4956efcc4b6abb3000efcdfd11868169869274639b4bb27826ea323759e1fd6a43e1c182049a2bf9f4bcef9f5d5d41c5832c802c69c833773b0022139f621be04fdf27b25a5d1e928004729f6e348d546807dac869e28a761323875c00604fd04e9c12b65200e909dc0a594790a6276ee5c0f76ef2ff48743009ad20b8ae7f1f97f684527d8aa6604011992f35e2f00b634f153c45e156fac87557d98c843e9f6d380b19cc09e8e19518a3b99b509429fdff722fee2c9c27c2091ba9b16297b7abefee3250cd25f7244d74a9672714112d9c031b5b0936f51e3e <<< 47870)

theorem band_c1 : rowAt 58289 1 16000 = cp1 := by
  rw [← bandRun_eq 58289 14 16000 1 (by decide)]
  decide +kernel

theorem band_c2 : rowAt 58289 cp1 16000 = cp2 := by
  rw [← bandRun_eq 58289 14 16000 cp1 (by decide)]
  decide +kernel

theorem band_c3 : rowAt 58289 cp2 16000 = cp3 := by
  rw [← bandRun_eq 58289 14 16000 cp2 (by decide)]
  decide +kernel

theorem band_c4 : rowAt 58289 cp3 16000 = cp4 := by
  rw [← bandRun_eq 58289 14 16000 cp3 (by decide)]
  decide +kernel

theorem band_c5 : rowAt 58289 cp4 13920 = A0 % 2 ^ 58289 := by
  rw [← bandRun_eq 58289 14 13920 cp4 (by decide)]
  decide +kernel

/-- The single seed's left band through wheel 58,288 is `A0`'s at tick 77,920. -/
theorem seed_band : rowAt 58289 1 77920 = A0 % 2 ^ 58289 := by
  rw [show (77920 : Nat) = 16000 + 16000 + 16000 + 16000 + 13920 from rfl, rowAt_add', rowAt_add', rowAt_add', rowAt_add',
    band_c1, band_c2, band_c3, band_c4, band_c5]

/-! ### From the band to the diagonals -/

/-- Low wheels evolve by themselves: rows that agree below wheel `m` keep agreeing there, whatever the number of wheels
`≥ m` each is cut to. -/
theorem rowAt_low {m K K' : Nat} (hK : m ≤ K) (hK' : m ≤ K') {v v' : Nat}
    (hv : ∀ j, j < m → v.testBit j = v'.testBit j) :
    ∀ t j, j < m → (rowAt K v t).testBit j = (rowAt K' v' t).testBit j
  | 0, j, hj => hv j hj
  | t + 1, 0, hj => by
    show (stepK K (rowAt K v t)).testBit 0 = (stepK K' (rowAt K' v' t)).testBit 0
    rw [stepK_bit_zero (by omega), stepK_bit_zero (by omega), rowAt_low hK hK' hv t 0 hj]
  | t + 1, 1, hj => by
    show (stepK K (rowAt K v t)).testBit 1 = (stepK K' (rowAt K' v' t)).testBit 1
    rw [stepK_bit_one (by omega), stepK_bit_one (by omega), rowAt_low hK hK' hv t 0 (by omega),
      rowAt_low hK hK' hv t 1 hj]
  | t + 1, j + 2, hj => by
    show (stepK K (rowAt K v t)).testBit (j + 2) = (stepK K' (rowAt K' v' t)).testBit (j + 2)
    rw [stepK_bit_step (by omega), stepK_bit_step (by omega), rowAt_low hK hK' hv t j (by omega),
      rowAt_low hK hK' hv t (j + 1) (by omega), rowAt_low hK hK' hv t (j + 2) hj]

/-- The row `1` is the single seed. -/
theorem ofRow_one : ofRow 1 = seed := by
  funext p
  unfold ofRow seed
  split
  · next hp => exact (decide_eq_false (by omega)).symm
  · next hp =>
    have h1 : (1 : Nat).testBit p.toNat = decide (p.toNat = 0) := by
      cases h : p.toNat with
      | zero => rfl
      | succ n => simp [Nat.testBit_succ]
    rw [h1]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- The single seed's left diagonals are the wheels of the row `1`. -/
theorem D_eq_Sp_one {j : Nat} (hj : j ≤ 87866) (t : Nat) : D j t = Sp 1 j t := by
  rw [← Ld_row 1 hj t, Ld, ofRow_one, evol_seed]
  unfold D
  congr 1
  omega

set_option exponentiation.threshold 90000 in
/-- **Through wheel 58,288 the single seed is on `A0` from tick 77,920.** -/
theorem seed_low (t : Nat) (ht : 77920 ≤ t) {j : Nat} (hj : j ≤ 58288) : D j t = Sp A0 j t := by
  obtain ⟨u, rfl⟩ : ∃ u, t = 77920 + u := ⟨t - 77920, by omega⟩
  have hlow1 := rowAt_low (m := 58289) (K := 87867) (K' := 58289) (by omega) (by omega)
    (v := 1) (v' := 1) (fun _ _ => rfl) (77920 + u) j (by omega)
  have hlowA := rowAt_low (m := 58289) (K := 58289) (K' := 87867) (by omega) (by omega)
    (v := A0 % 2 ^ 58289) (v' := A0) (fun i hi => by rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]) u j (by omega)
  rw [D_eq_Sp_one (j := j) (by omega), show 77920 + u = u + 4870 * 16 by omega, Sp_add_mul A0_return]
  unfold Sp
  rw [show u + 4870 * 16 = 77920 + u by omega, hlow1, rowAt_add', seed_band, hlowA]

/-! ### The classification leaves `A0` -/

/-- Wheel 400 pins the time shift: a strip with `A0`'s wheel 400 that carries the seed from tick 177,560 does so with shift
0. -/
theorem shift_zero {v s : Nat} (hv : rowAt 87867 v 16 = v) (hs : s ≤ 15)
    (h400 : ∀ r, r < 16 → Sp A0 400 r = Sp v 400 r) (hon : OnStrip D v s 177560 87866) : s = 0 := by
  rcases Nat.eq_zero_or_pos s with h | h
  · exact h
  · exfalso
    obtain ⟨p, hp, hne⟩ := prim_A0 s (by omega) (by omega)
    apply hne
    have h1 := hon 400 (by omega) (177568 + p) (by omega)
    have h2 := seed_low (177568 + p + s) (by omega) (j := 400) (by omega)
    have e1 : Sp A0 400 (p + s) = Sp A0 400 (177568 + p + s) := by
      rw [show 177568 + p + s = (p + s) + 11098 * 16 by omega, Sp_add_mul A0_return]
    have e2 : Sp v 400 (177568 + p) = Sp v 400 p := by
      rw [show 177568 + p = p + 11098 * 16 by omega, Sp_add_mul hv]
    rw [e1, ← h2, h1, e2, h400 p hp]

/-- The forks exclude the other strips: a strip whose wheel `w ≤ 58,288` is the complement of `A0`'s does not carry the seed
from tick 177,560 with shift 0. -/
theorem not_on_complement {v w : Nat} (hv : rowAt 87867 v 16 = v) (hw : w ≤ 58288)
    (hc : ∀ r, r < 16 → Sp A0 w r = !Sp v w r) (hon : OnStrip D v 0 177560 87866) : False := by
  have h1 := hon w (by omega) 177568 (by omega)
  have h2 := seed_low 177568 (by omega) (j := w) hw
  have e1 : Sp A0 w 177568 = Sp A0 w 0 := by
    rw [show (177568 : Nat) = 0 + 11098 * 16 by omega, Sp_add_mul A0_return]
  have e2 : Sp v w 177568 = Sp v w 0 := by
    rw [show (177568 : Nat) = 0 + 11098 * 16 by omega, Sp_add_mul hv]
  rw [Nat.add_zero] at h1
  have hc0 := hc 0 (by omega)
  rw [← e1, ← h2, h1, e2] at hc0
  cases h : Sp v w 0 <;> simp [h] at hc0

/-- **The single seed is on `A0`, with no time shift, from tick 177,560.** -/
theorem seed_on_A0 : OnStrip D A0 0 177560 87866 := by
  obtain ⟨s, hs, h | h | h | h⟩ := forced_front_four_seed
  · obtain rfl := shift_zero A0_return hs (fun _ _ => rfl) h
    exact h
  · obtain rfl := shift_zero A1_return hs pair_A0_A1.2 h
    exact (not_on_complement A1_return (w := 58287) (by omega) pair_A0_A1.1 h).elim
  · obtain rfl := shift_zero B0_return hs pair_A0_B0.2 h
    exact (not_on_complement B0_return (w := 53208) (by omega) pair_A0_B0.1 h).elim
  · obtain rfl := shift_zero B1_return hs pair_A0_B1.2 h
    exact (not_on_complement B1_return (w := 53208) (by omega) pair_A0_B1.1 h).elim

/-- For every wheel `j ≤ 87,866` and every tick `t ≥ 177,560`, the `j`-th left diagonal of the single seed is wheel `j` of
`A0` at tick `t`. -/
theorem seed_eq_A0 {j : Nat} (hj : j ≤ 87866) {t : Nat} (ht : 177560 ≤ t) : D j t = Sp A0 j t := by
  have h := seed_on_A0 j hj t ht
  rwa [Nat.add_zero] at h

/-- The white wheels of `A0` through wheel 87,866, and the black wheel two above each of the last six. -/
theorem A0_white_black : ∀ r, r < 16 →
    (Sp A0 2 r = false ∧ Sp A0 7 r = false ∧ Sp A0 28 r = false ∧ Sp A0 399 r = false ∧ Sp A0 53207 r = false ∧
      Sp A0 58286 r = false ∧ Sp A0 87866 r = false) ∧
    (Sp A0 4 r = true ∧ Sp A0 9 r = true ∧ Sp A0 30 r = true ∧ Sp A0 401 r = true ∧ Sp A0 53209 r = true ∧
      Sp A0 58288 r = true) := by
  decide +kernel

/-- **The single seed's seven white diagonals through wheel 87,866**, and the black diagonal two above each of the last six,
from tick 177,560: the seventh white diagonal is `D 87866`. -/
theorem seed_white_black {t : Nat} (ht : 177560 ≤ t) :
    (D 2 t = false ∧ D 7 t = false ∧ D 28 t = false ∧ D 399 t = false ∧ D 53207 t = false ∧ D 58286 t = false ∧
      D 87866 t = false) ∧
    (D 4 t = true ∧ D 9 t = true ∧ D 30 t = true ∧ D 401 t = true ∧ D 53209 t = true ∧ D 58288 t = true) := by
  have e : ∀ j, j ≤ 87866 → D j t = Sp A0 j (t % 16) := fun j hj => by rw [seed_eq_A0 hj ht, Sp_mod A0_return]
  rw [e 2 (by omega), e 7 (by omega), e 28 (by omega), e 399 (by omega), e 53207 (by omega), e 58286 (by omega),
    e 87866 (by omega), e 4 (by omega), e 9 (by omega), e 30 (by omega), e 401 (by omega), e 53209 (by omega),
    e 58288 (by omega)]
  exact A0_white_black (t % 16) (Nat.mod_lt _ (by omega))

end Ruliology.CellularAutomata.Rule30SeedLeftSide
