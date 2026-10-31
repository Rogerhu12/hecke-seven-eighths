# Low reflected energy: source and verification ledger

Prepared from verified CI artifacts at 2026-10-31T09:58:22.369493+00:00.

**78 of 94 new modules have successful evidence for their current source bytes; 16 do not. The current full dependency graph and final target remain unverified.**

The latest completed actual run is `41188282678`, job `124499578347`. It checked out the exact published head `245e1de501287489868916f4a7e4b4df0b060e2f`. It records 786 direct successes (634 exact-cache reuses and 152 new compilations), separately from 1,794 native old-dependency reuses, with 20 compiler failures, one diagnostic timeout, and 957 skips (821 dependency-blocked and 136 budget skips).

The two newly successful task modules are `ActualSeparatedBlock` (five clean public axiom reports) and `ActualFrozenStateCount` (four). Their reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The actual phase has 76 successful task modules and 294 printed public reports; the source-matching union reaches 78 using preserved core evidence. `ActualHybridEntry` remains compilation evidence without a printed public theorem report.

`ActualBlockEnergy` and `ActualBlockReindex` failed in that run. Their compiler-generated `sorryAx` reports are not successful proofs. Their subsequent proof repairs await the next run. The timeout in `ArchimedeanGaussianMellin` is a diagnostic budget interruption with no proof result.

The current source snapshot includes upstream base `5f3c782680be2c74365b4d8e5760fc16f1f222c5` and all 66 import-adjusted old files restored to exact upstream bytes. The [restoration audit](IMPORT_RESTORATION_20261031.json) confirms that every non-import byte is unchanged. The unused `FLTReuse.ExplicitMathlibImports` helper was removed. Restoring the broad import paths implicated in the 18 old-file failures is not compilation evidence. The new default actual lane uses the pinned official `lake-cache-76c696e` release and native Lake. No restored `HeckeSkeleton` output may supply task verification; both final theorem audits remain required.

The 1,794 native validations retain their original `native-lake-foundation-v1` receipt, catalog, configuration, artifact hashes, and validation log. They are historical evidence for the recorded context; they do not authorize reuse under the changed configuration and never certify a new proof module. Python regression fixtures are excluded from proof evidence.

Latest completed actual final gate: `not_run_due_to_failed_or_skipped_modules`.

All source classifications below refer to successful recorded contexts. A matching source hash alone does not validate a changed dependency graph. Earlier raw records and full compiler output remain in [aggregate_evidence.json](aggregate_evidence.json); prior evidence references remain in [source_manifest.json](source_manifest.json).

| Module | Current source SHA-256 | Source evidence | Latest supplied attempt |
|---|---|---|---|
| `HeckeSkeleton.LowEnergy.AnnularEnergy` | `5d1592104712b988144dd32b0783c3daa735c0f74545654345362f50fbd24748` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.MellinEnergy` | `3246452a28eba477a0534613895cb331e8dfecb6e25f3570c85f726b042b30dc` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.KeepOriginalRow` | `011da9dcf746e4ab6a9a9ff029f23c94ea46adec50aae916e45d1f9d082d05e1` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.OriginalRowNormalForm` | `707f797038f6b9c115711c3701b4229d5faf8edf6c8984be19310051b32e49a5` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.SmallPowers` | `45c6abcb4dd50f7bc21c1595cea816e7adec9fb6de30150563f3b45e2633daa1` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.IdealMajorant` | `dcd161483c67bfc4e61dd8dd2a2bc9f1cb3f4e74cb9c7c99116a27c7ccea76fc` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.IdealMass` | `de311d9dfa1cf265a511380ab659698997673f10b43ae3038fa677aea5866c4f` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.OriginalRowSupport` | `d0d075ae5841cd64b2ddc8b4c428f0d8c87f666e9385517a8f75ff341eb654c3` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.SquarefreeFibers` | `8b71a2ee70b724c141d3257656c5107a771ce0de9e634b8c146cc7735b549185` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowHybrid.SieveComposition` | `b59601851cb677b730d0927d1b423140a98c601167cd580813662c778b11bbb9` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowHybrid.Assembly` | `bfbc0a1cb47dbde64240f318bcc9cfacdc12d43336b42ace31b6717a18cdb456` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowHybrid.Weighted` | `30e1f4a7ced3a7a12109d5f9b634267975a64105953638e0fd21903c9cb8091f` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowHybrid.Global` | `4fee86656221c1abf7dfac6b151edff0d2fc0e342b58b4ecbaa8dc4d3d67b4d7` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowHybrid.SieveBounds` | `2798478ee031d9112d5ed8fa6ce2d1f2be193b9b431158231b2f727b5744d36b` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowHybrid.Transpose` | `cf53f11bfabb6ae2d84784a8cf0e38b24708994bed3c77db017de5495538cad5` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowHybrid.WeightedSieveBounds` | `508aaef817c8aba5b7f9ad33fb9e32b93e326c9b6a5b0dd18d5a6f1b5c94709f` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ConcreteIdealBlock` | `ee207c9801cc72577d68b2686f24c2ab2ee057f0231b15fa9e3e3d5fd9001389` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.UniformIdealHybrid` | `afc3f55d580a4d0f24d5120b800c4071f7729f3bdeb94f5c503fb85324681266` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.IdealDivisorMasks` | `c88c5268423399b65030a5dd7aee714709bb8a0b64cdd655ffecb35c582ce33d` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.IdealCanonicalColumns` | `bdfeb5349871965e8093a8ed6ec4c7e6bb699c7740d392b34591844e0e6b2206` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.RawIdealHybrid` | `5b6a2cf8503baaadf803f24ffa340d6757eb48db92ec500fe514f71ba170d8e0` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.HybridScaling` | `b44f5bbb0ea15675d53b24debe7cef9a477957ed4e9234391437beab616cb96b` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.MellinHybrid` | `964f08a630601c28580ee304f6fb0d182858cce70239830cf4ce5929ee74ea46` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.Exponent` | `6e2a5c32f5913e62a31d287a54dfcc345e11df9cf78aa8fb30a1e569b73e5ab4` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ExponentTail` | `690fafe1df46d84c203a29388941e54de411cde053ef6a8fcfdf8c18039fb9ee` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.CommonMellin` | `2b88696cd22a8b361094766c78ea1a1b9cc2d2ab192c81a45597c963bf8895af` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.CommonMellinTail` | `7d47587515bcd1822f67fba469870029bc4d3dbbb257ee740db3d0fb3fb84b91` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.BlockPolynomial` | `531de8ea0d05afd26e99191d2337777be07d757597955445eb36c5f4aef8c739` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.DyadicTail` | `4af86f5e7cb309b18faa901fd5999080bcb47d13e98c3559d930836493e6da2f` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.EulerLog` | `17846e1fc90894d2e17e53194a370990928bc45a40df4b9e984168eb2a9f36c0` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.GaussianReconstruction` | `19199329a679c99ad32a731a8e47c296545df5f0593ee5d68118d6aabaec6730` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.GaussianSeminorm` | `87f07e913c0edf9f7304a9b12ca6c5ae7237fad78eca7d6bb2f31a8e2dbb8581` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.GaussianDyadicBudget` | `2004a772930e5cafe9c536ad58864793365f11d4663cfe43314394d2a06026eb` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.GaussianEnergyAssembly` | `3450d85543b3125e297d517fe4829c57cf2299cfc94c17d3f2478d22d56d5c91` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.IdealRows` | `7ab30fac83247540d6ab663d1929375ccc1dca1c3bad4d80e74d556d31889a44` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.Rankin` | `cf609b3271aa6a31af843413fa89128dd637faab760c223cc2d1199e4e05983a` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.IdealRankin` | `81b3cc328aadb5242be6f4630678fb4ff8272aa76e70c8b92471f47195406134` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.FiniteFiberEnergy` | `33dc88a2b8e15c184eb1fe8612111161d8df1847d33286a96d01f27c95981ae1` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.PowerfulRowAssembly` | `7ea7481216763975d13109dcac748c285d8f0eacb2e7cdebe3c2f37e47e7dc19` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.PhysicalDyadicBudget` | `89552bd5eed7a7491c4f18dfa1019c247b1726d9f309ea76c4ef35ecbb93fa6d` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.LogGeometry` | `8d27cd3ef66f28e93190a711195513f18fbb75e40a3098d42885e19ef93fa1bc` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.FiniteHybridIntegral` | `ada046f6c2773e29d4a32cd3b1aae23f5eac5eea07c1b42aceb1e1c9e9ae552c` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.TupleCore` | `97bda35566a1ee9e0ea32ab48a1d30144f21b53611f3da6ce2b795c28692c843` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.InactiveCore` | `c34b54792916fb39205e6770487cf10f4f4ad25f8f907394cdf3efaacb9cbfb4` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.DyadicReindex` | `219709977718b91fd49038da3d6112a185c89f428818c7d0a3bad179c4f8760d` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.LocalWeylTableCore` | `feca761900a6068ab4fb2fd482906d5691f084458c1efac0e4c211ecb2c51aed` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.FrozenChargeCore` | `7341f3fbf0ac735466382af63aea40b3379408b205950813a62b4364098349be` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.SupportPowers` | `e985c4857fc79f114080f3b0cad770729247f6af598b2b66811eb93391387566` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.IdealSupportPowers` | `57e3cef5f6de2c9aa68892bc62361c228d1b16fdbbca9b1668182842d0f43ed7` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualRows` | `1984654b60ee1e534b91818036ffe0d57ed025f2cfccc729b1f4830cb24e6930` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualSymbols` | `de486fd4e59862eb9b1de7d4aa9b5b39bb9d98ea190d632fe384d0dfa9b908de` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualReflection` | `e308dce568976555c99081e8261b11e690b6cc37cbe479cbb2011b4f2fe698c1` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualSymbolProducts` | `2a12162291d545368c226a2c88619cf5036e90ff157acaa6f4874efc616671b1` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowFrozenCube.Exponents` | `85c9a0b5694c870bb37eaa309acbf33deaba03cc34fe600a60a58f7cfb8e55f3` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.FrozenIdealRows` | `5366d207da63509df2a337d7618c06858e1130dea74d9c1e23ff5006729c9c79` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualFrozenCube` | `993d2b1e17853dcf44b4ec7452c2e97c81efb2c70fd904a89793c653c8dca70c` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualLocalWeylTable` | `756607d8af9886598e7344653f8284d7f0f34c4c907cc173db67f86ad99427f2` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualFrozenMajorant` | `9d778e91996a11a240e4e2ca3a560f92e39c5fcf5b31fe08a9ac37ac7bfceb61` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualFrozenIndependence` | `e8e85cd0a5a9febb7cafb46e2136ae25f84d1401ee7b9031767ae1f644d76062` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualReflectionReindex` | `36c0d10a68e2dc30628e1a621e9638e338dde7c37f129dbe77aee11bee970862` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualCommonMellinTail` | `1e17a8197abe8ee47a796245bcf4db82e53c092d9de47310832b7e949ef70b5b` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualFrozenCharges` | `bc60ee44c2669ab7257441afdbee05b2f29bddb0f8aa9be710783348921dd880` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualFrozenStateCount` | `a877d86f448e5ad8e3c78a87c228389a4a3fe6ca1b47c5167c8d368ad8df7858` | direct_compiled_success | direct_compiled_success |
| `HeckeSkeleton.LowEnergy.ActualSieveDictionary` | `f58fd9887be68209382570e91ebe3c8c4856bcf3bf8b74b514cbd1a24b5218c8` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualRawHybrid` | `094374bb2150f3c85e7cc7e1a5c1684a7222403a3b425e80410326de0388c5d1` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualHybridEntry` | `f3bdb01ca452f7116cf1b754203c94dcfb80459427ff65146b47b5de8e5005fe` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ClassSlices` | `e6d8d177a719024e0258d2a2373e0d1c930b84f588e0c44e5f9f6809a0e595c1` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualClassSlices` | `f4e8a37f474aa408bfb5c20dbb06ee8f77aaf32a8b4f730417ee8d69afa72896` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualGeneratorClasses` | `94f309c0127dcbd7e293013c0dd6bb410d9980b4a78b5ea5b8275f092dfb8cc5` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualSeparatedBlock` | `df34c2583706ea16e9ab9978882cd514c165d6888bc4619db1f49a138072410e` | direct_compiled_success | direct_compiled_success |
| `HeckeSkeleton.LowEnergy.ActualBlockEnergy` | `eee0dd9a7cc01951dc550b9f3f92430cd3fa79e8ba6e80d60300f917e2bd1bdb` | changed_since_recorded_source | failed |
| `HeckeSkeleton.LowEnergy.SlotTuples` | `6bf40582c293fce717b909cbd8783c9a6d70b685771b0b75afffffea4416c1b9` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.WindowTuples` | `c8ce8280dc4e6164ed75ab79447e5fa1101473a1c94a478c8b0f824a2951d36f` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.InactiveWindows` | `9278a82089e84d999a85b223feace80ffdac10bdb819a814f9e607d0b9f05485` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.TargetDictionary` | `89c7e7faef5340f13530d8c4d8a3c0e603254008d58e409b6b79a2d8536727ed` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.GaussianTheta` | `9b4b613f3db37039dd4fa21714455c44494d56174596b8a249500f6a4855efea` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.TargetGaussian` | `9c36836c6aa54d5e4093a70bd241debc39c9a983d32ee1e9671fc61a6cdc9461` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.TargetSieveDictionary` | `76ba1619c063dba496ec891841cd1d61f92d93d1f39c605e6a26ed8f5c0a6929` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualBlockReindex` | `03b246ca9d5136a7ca69fd47f3820dea993a6b8a5a70411c5228e6406a51fc4a` | changed_since_recorded_source | failed |
| `HeckeSkeleton.LowEnergy.ActualSourceReindex` | `c0acedfdf1431832d1042228dcb9a7e0c6046f6addf86d54b8ea7cca2e2d914b` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualRowFibres` | `1759c44a943601c80a103da42945620c346fb7608d47df0cb02491b56a8742bb` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualDyadicReflection` | `c3383936674728438f52c8024610b47e47d752059ec71f08cf378bd3715ef574` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial` | `bb5e86bb0bee0b24dc02e21993f90c896a32cbb096f4fbd0dfce68feebe3c409` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.PhysicalGaussianEnergy` | `66559059e3e32ec55dba8fd635ed3fc1d2f52fabdb39b1751dda0d2054a9a2c8` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowEnergy.ActualAnnularBlockEnergy` | `b367a9debe758ffd2aed265e13983f5c940fa8c565a6a4460545425fef9b7ddc` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualFrozenAggregation` | `47370edda622bf773f41ef966a874b1dc94bc0764a9ffe44dbe28b33b3399131` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualFrozenReconstruction` | `5456398c7ef6a18c4a64afaf3c1d0c9271fc1d2cdc8ffb1f928737bc105c18b7` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualMarkedTupleEnergy` | `763cd3d13594e3caead07b43da22c3d0b1e49130f57ee42f3a3e6d1bf0076cdb` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualTupleReconstruction` | `fddcae0c3187ba1097e93970803a7e3583b06abe14c023a5a0dd7c1df578d22f` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualResidualDyadicEnergy` | `e3643acb6ed48c2510c739099cbfbca58f4ffb79137801f09d6bb9f072f5ca49` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualCompleteIdealEnergy` | `aff5da5ca4eb82f4d6a43b284159354b3bb85220959cee5d46ad4967131de103` | skipped | skipped |
| `HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy` | `6b17122916d248f46bf750637b7de135dbaacd7662e97ce43ab280ee59481b84` | skipped | skipped |
| `HeckeSkeleton.LowFrozenCube.Valuations` | `5249d242539316a45ea01cfe73af5ac6dd607b1ddf6b3b9033ca850ef980a1c7` | direct_exact_cache_success | direct_exact_cache_success |
| `HeckeSkeleton.LowFrozenCube.LocalCoefficients` | `480a326fa64d1ab714ab9e751e3c32a88a248c7938b1c398bbed187a8fba4a17` | direct_exact_cache_success | direct_exact_cache_success |

## Preserved evidence runs

- `41167618537:actual:13030181239`: 534 direct successes; kinds `{"diagnostic_timeout": 1, "direct_compiled_success": 73, "direct_exact_cache_success": 461, "failed": 2, "skipped": 3015}`; final gate `not_run_due_to_failed_or_skipped_modules`.
- `41169613835:core:13030830729`: 66 direct successes; kinds `{"direct_exact_cache_success": 66}`; final gate `not_applicable_core_phase`.
- `41169613835:actual:13030109450`: 575 direct successes; kinds `{"diagnostic_timeout": 1, "direct_compiled_success": 41, "direct_exact_cache_success": 534, "failed": 7, "native_old_dependency_reuse": 1794, "skipped": 1181}`; final gate `not_run_due_to_failed_or_skipped_modules`.
- `41171430364:actual:13031561006`: 634 direct successes; kinds `{"diagnostic_timeout": 1, "direct_compiled_success": 59, "direct_exact_cache_success": 575, "failed": 6, "native_old_dependency_reuse": 1794, "skipped": 1123}`; final gate `not_run_due_to_failed_or_skipped_modules`.
- `41188282678:actual:13038675514`: 786 direct successes; kinds `{"diagnostic_timeout": 1, "direct_compiled_success": 152, "direct_exact_cache_success": 634, "failed": 20, "native_old_dependency_reuse": 1794, "skipped": 957}`; final gate `not_run_due_to_failed_or_skipped_modules`.
