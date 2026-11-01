# EXPANSION：实际展开、同源检测配方与验证状态

分支 `codex/expansion-detector-20261030`，PR #5，基线 `dtests-handoff`。

**任务仍在进行，原始目标尚未全部通过。** 已合并 base 50f 的原生运行中四个 strict 组通过；skeleton 剩下 HighBin 与 DetectorProfiles 两个原生根，当前两份修复及后来合并的 b46 基线仍待完整重验。

最新完整原生证据为 `f606882` / run `41278811681`：pure 112／2,042／0，arithmetic 116／2,110／0，physical 39／808／0，contours 56／709／0（模块／声明／非标准公理依赖），均在已合并 base 50f 的环境真实通过。ActualRowEligibility 原模块 fresh Built，HighBin 剩三处 Haar 实例族错误，后继 DetectorProfiles 新到达两处 elaboration 错误；skeleton 共两个根、五条诊断。三个共享源模块及19个原名目标的严格 gate 均未执行。本轮另外逐名核实480个尚未入账的真实公理打印，历史总记录757；这些记录没有代替严格终门。

## 原始目标与实际对象

最终展开必须作用于原 `normalizedProbe - principalLineProbe`。它由主行三项余量、小行、绝对大行、固定缓冲壳层块及真实高度尾组成。物理字符、完整理想掩码、有限素数窗口、全部 selected/unselected compensation 和原 primeNormalizer 都留在同一核中。族参数始终允许 `7/8 < B ≤ 1`，没有新增 `B ≤ 11/12` 或 `delta ≤ 5/6`。

原小行界的 saving 为 `1/50`；主行两条竖线保留 `23/960` 与 `13/9600`，第三项保留原 `principalSlotSaving`；大行目标保留 `63/800`。顶层 `GeneralHeckeSevenEighths` 的声明未改。

## 同一真实源生成见证与矩模型

共享 `HeckeSkeleton.SourceData` 固定显式全尺度 E，`SourceMomentIndexFor / ModelsFor / PolynomialCalibrationFor / RowEligibilityFor / WholeMomentProfileControlFor / UniformMomentBoundFor` 全部使用它。`recipeMomentSourceData` 使用同一 `RecipeExpansion R`；actual aliases 最后选择 `expansionRecipeRaw`。模型行宽是 `1+log 2/log U`，精确覆盖原 `U<N(u)≤2U`，多项式长度基数仍为 U，capacity 上端仍为 1。

实际 detector 端点从原 Hecke 零点、有限高度 buffered zero bounds、原删除系数和固定 cutoff 推出 terminal source、同频率 inverse/plain 乘积、两因子饱和及长度条件。它们不接受最终多项式上下界。Fourier 环境集取 `6H`，源本身不变；真实 `2pi` 频率消耗已纳入高度缓冲。有限背景取消行的纯范数极点由实际算术角色的有限纤维阈值排除。

`PhysicalAmplitudeSource / Provenance` 从原素数多项式数值构造有限 amplitude fibers，在同一物理高度盒中选择最大行数样本，并保留所有原标签及其精确来源。`PhysicalRecipeSchedule / Assembly` 固定壳层、互斥 buffered selector、sector 与标签族；每个块的值在所有尺度上都是原 shifted rowContourBox 的真实有限和。小尺度默认见证也不改这个值。

`physicalRecipeExpansion_geometry` 给统一 `MomentGeometry 22`，包括无选中行的标签；实参数范围为 8，虚参数为 `1+||heights||`，原高度锚不变。`exists_physical_recipe_parameters` 先选检测宽度、标签宽度、ceiling 与计数常数，再允许选择 tau 和尺度。新增独立正 cap 令内部 e 同时服从两项外部损失；通过同一 WitnessCover 的 loss 单调性放宽到 lamA，原壳层上端仍由 lamA 控制。没有因 lamB 很小而错误缩短壳层。

同一参数项现已填入原 `expansionRecipeRaw`，其 `MomentGeometry 22` 也已在原名上给出；这些新源码仍须通过 native build 和传递公理检查。

## 物理 Poisson 与初始 Mellin 链

已写成的完整源码链保留真实 Haar/Fourier、Gauss 系数、六次剩余符号和原理想轨道：

1. `PhysicalFourierNormalization / FinitePoisson / ProbePoisson` 从原归一化 Poisson 公式推导真实有限系数变换与物理探针公式。
2. `PhysicalFrequencyReindex` 证明原频率到六次幂自由行/sector 的真实满射与可和重排，识别唯一主行。`PhysicalAdditiveOrigin` 从原 annular 支持证明实际原点值为零，Fourier 零值使用实际 test 假设。
3. `PhysicalCompletedPoisson` 完成真实 completed-theta、denominator 与频率和的交换。
4. `PhysicalPositiveMellinInversion / InitialHeight / InitialPowers / InitialMellinTerm / Absolute / Identity` 给正线 Mellin 反演、真实 height shear、三变量绝对交换与初始线 `(5,5,3)`。
5. `PhysicalCompensatedInitial` 由 PR #7 的实际 Euler calibration 接到完整原 compensatedRowMellinKernel；`PhysicalInitialRowSum / Truncation` 给逐行 norm-integral 可和、唯一主行拆分，以及原有限盒加真实盒外积分。

上述源码不以目标积分恒等式、收敛结论或最终范数界为输入。正在用原 Lean 环境逐层编译；不能把写成状态计为验证通过。

## 原主行、外部行及移线尾

实际素数计数链直接从原 prime logarithmic derivative、有限高度 contour 与去对数窗口得到 primeNormalizer 的正性及任意小幂 reciprocal 界，不调用旧 admitted 的 `PR-WINDOW-PIT`。

`ActualSmallRowBound` 合并真实 common-packet reciprocal、有限删除多项式、原局部 Euler 表、Mellin 权重与行求和，得到 `(B+e,1/2,17/50)` 的小行界。`ActualLargeRowBound` 保留所有真正大行，在 `(2,2,1+3/zeta)` 得绝对可和尾及半幂节省，足以给原目标。

主行的实际 pole-cleared zeta、两项 residue limits、w/z 全线移线、双留数与 `compensatedPrincipalCorrection` 的精确识别已经写成。原 w 余项取 `19/20`，z 余项取 `33/200`；主要 residue line 才移回原 `Re(s)=2`。`ActualPrincipalUniformDecay / ResidueTails` 固定粗尺度幂与高度次数，再选择任意外部衰减阶，保留真实有限积分差和高斯尾。

`FiniteTripleContourTransport` 保留六个字面横面。small/large 使用正区；moderate 的真实起点是 `(B+20e,1-a-6e,17/50)`，其 w 可为负，不能塞进要求 w>0 的 rowEulerRegion。`ActualModerateSweepHolomorphy / CorrectionBound` 使用 PR #7 较大的真实 sweptTube 和正常收敛 Euler product，保持原 hmove 的起终点与原 mask。粗有限 tuple/subset 求和只用于横边尾预算，不冒充最终 slot cancellation 界。

`PowerHeightTailAlgebra` 合并已经证明的尾，保持 A、R、ceiling 在 tau 与外部 N 之前。

## 独立可审查的定义修正

| 问题 | 修正及依据 |
| --- | --- |
| 实际 Fourier normalization 的 Poisson 标量遗漏 | `physicalResidueNormalizer` 与 row numerator 同时加入 `c_K=2^r2/sqrt(abs(discr K))`。逐点证明原数值 row kernel 不变；物理 normalizedProbe 明确乘固定 `c_K^-1`。论文 3529–3531 允许固定 Haar convention 改变 residue scalar。独立提交 `7e44ea4`，详见 EXPANSION_POISSON_NORMALIZATION.md。 |
| 旧 packet 表示未去掉 omega 自身的范数分量 | 固定一个无限位，令 target 乘 NormTwist(radial target)，使该径向分量为零。正确的 untwisted_eq 使用 normalized omega。原 packet、零实部和 permitted inverse 不变。 |
| 正槽 theta={1} 不能排除有限 plain background 的取消行 | canonical theta 在 psi 有限阶时取 `{1,psi,psi^-1}`，否则 `{1}`；对全模型证明 plain 非主，再由径向零分量排除所有 normTwist。另从真实有限纤维证明物理行的 eventual eligibility。 |

后两项按 #12 评论协调由共享源 owner 修正。新旧陈述、论文1537–1548及3818–3825的依据、影响的调用者和验证状态详见 `EXPANSION_CHARACTER_NORMALIZATION.md`。未新增最终矩界或无零点假设。

## 已完成的验证与当前阻塞

环境：Lean `4.35.0-rc3`，compiler `470d5ce1400764999581fd26d5d72b00d990b0f4`；Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`；项目原 implicit 选项不变。当前 EXPANSION CI 沿用官方 `restore-lake-cache@ci/lake-cache-test`；新版 README 推荐 `@dtests-handoff`，两者的版本引用在记录中明确区分，未因此改动原验收工作流。保留普通 Lake 与 `use-github-cache: false`，自定义恢复/重编译驱动已移除；编译日志、源码清单和公理输出只放 Actions artifacts。

- `5bf0cbc` 的 EXPANSION pure job `124511697073` 完整成功：穷尽审计 **1,996 个声明，0 个非标准公理依赖**。actual/skeleton 当时均被同一 physical residue cancellation 化简超时阻挡。
- `2cba624` 修复该消去证明后，skeleton 日志明确新编译 `PhysicalProbePrincipal`（14秒）、`HeckeAxiom.ProbeNormalization`（6.1秒）、`HeckeSkeleton.Base`（6.3秒）。这三项成功不表示骨架无 admissions。
- `2cba624` 的 Theta run `41193234078` 完整成功。
- `2cba624` 的 pure 新失败是 PhysicalInitialHeight 的 pi volume 实例不匹配，已改为真实 product measure-preserving 等价；skeleton 新失败集中于旧 DetectorProfiles 的 namespace、Fin6 数值实例与支持集证明，修复已写入。两组均尚须重验，未执行最终穷尽审计。
- `2cba624` 的 actual job `124514098386` 已完成失败。原始日志逐项定位到有限轮廓 transport、物理 Fourier、主行 punctured limits、小行 reciprocal/Mellin、大行 subtype 重排、实际 Euler/cast 以及 canonical amplitude 的 elaboration 根错误；本批按这些日志修复，并处理相同记号在未编译后继模块中的同形错误。尚须 CI 重验，不据静态检查宣称通过。
- 共享 SourceData 的7个公开接口已在 #12 run `41190828198` 实际 Built 并逐项验证仅三条标准公理；本分支也加入逐声明严格 gate，类型依赖同样接受检查。

历史逐模块记录保留在 `EXPANSION_VALIDATION.json`；历史 pass 不自动覆盖改动后的源码。allowed axioms 仅 `propext`、`Classical.choice`、`Quot.sound`。failed、cancelled、仅打印 Ran 或尚未编译的声明不计通过。

下一轮保留完整 source manifest 与传递公理检查，将原 actual 审计任务按 arithmetic、physical、contours 三组分配；每个模块恰归一组，所有原 imports 仍由 Lake 构建。pure 与 skeleton 各保留独立任务，skeleton 中的共享 SourceData 严格 gate 不变。拆组仅用于缩短反馈时间，未删除声明、放宽公理白名单或改变验收标准。

## 原始接口已经写成，完整验证仍未完成

`Base.expansionRecipeRaw` 已由 `actualPhysicalRecipe` 实例化，选用同一 arithmetic choice、原 self-dual measure、同一 probe test 与实际 Euler provider。`expansionPhysicalParameters` 先于 tau 选定 e、width、ceiling、k；`expansionRecipeRaw_geometry` 给该原名对象的 `MomentGeometry 22`。`expansionBudget / CutoffsRaw / Cutoffs` 由已经写出的实际保留项界和 detector threshold 选择。

原 `expansion_identity / principal / small / large / blockCount / blocks / tail / expansionSource` 的证明体均已补齐。`ActualRecipeIdentity` 从实际初始三变量积分、唯一主行、small/moderate/large 精确分拆及 active/raw 有限重索引给原恒等式。保留项使用同一共同常数和次数，未引入目标估计作为假设。

尾是六个字面项：principal tail、nonprincipal initial complement、small horizontal faces、large horizontal faces、moderate initial horizontal faces、whole-bin boundary。主行盒外补项只计一次；`ActualPresentationBoundary` 证明原 actual presentation 的 whole-bin difference 与第六项在原 guard 下逐项相等，EXTAIL 只消费原有 `HighBoundaryControl`。

原 `actualHighPresentation` 的数据构造来自同一 raw recipe，包括每个实际 fixedRows、bin、height 和标签 piece。piece 是原 movingPiece 在实际物理高度盒上的积分；已使用实际有限高度 reciprocal 和完整核可积性推出分片求和恒等式。其他 HB 分析义务仍属于 #7。

`1c9f422` / run `41194677568` 的五组均完成失败，原始编译日志和 artifact SHA-256 已读取验证。这一批按原生日志修复 Fourier 的实际零值与变量捕获、有限三变量轮廓映射、detector 的原 filter 实例、删除 Euler region、Mellin product measure、实际 zeta residue/log derivative 和 radial normalization 等根错误。没有从失败 elaboration 的 `#print axioms` 推断成功。

验证脚本现在除全量 pure/actual 严格审计及共享 SourceData 严格审计外，还对 **19 个原名及共享实际接口目标**单独调用 `collectAxioms`，包含类型依赖；任何非标准公理都会让任务失败。新原名证明尚未通过这一 gate。剩余完成标准是：修复全部真实编译错误，让所有组及原名/SourceData 严格 gate 通过，记录精确源码与公理证据，然后将 PR 标为可审查。

## 全标签实际行资格与最新已验证组

`ActualRowEligibility` 从同一个 raw 的每个 amplitude origin（含默认和padding标签）取得严格 U<rowNorm，结合 U≥2 排除单位基理想，再通过真实行字符分歧证明排除同一个固定 Θ。它给出全部尺度、标签、细分下的完整 `SourceRowEligibilityFor`，没有新增 calibration、资格或能量前提。原 `Moments.moment_row_eligibility` 保留 hcal 原签名并接到这个实际证明；其他矩归纳及 profile 结论未改。`actualRecipeSourceGeometry` 同时导出长度22与原参数盒 admissibility。该 leaf 与原名均加入严格 gate，新增源码仍待下一轮 CI。

head `63fb331` 的 run `41204649328` / pure job `124547158378` 已完整成功：112 个源模块、2,042 个声明、0 个非标准公理依赖。artifact `13043873689` 的 SHA-256 为 `5bebd9ef9fae0778754445bb3af575e210cea2bec6e25d2ac8cdc8a0d36c5c9e`，已校验；112个源文件的SHA-256与本批相同。其余四组已完成失败；全部 artifacts 已下载并核对 SHA-256，根错误落在同样九个模块，没有据失败 elaboration 宣称原名 gate 成功。

本批逐项修复这九个根模块：`ActualProbeContext` 的局部记号字段及 subtype quotation；`ActualZetaLogDerivative` 的 id 函数表示和标准复数实例转换；`PhysicalFourierNormalization` 的真实 Schwartz 坐标变换；`PhysicalDetectionParameters` 的终端标签索引、隐式参数及 wrapper 化简；`LargeRowMellin` 的坐标变换展开与实积分类型；以及四个 actual Euler/prime-window 模块的有限乘积集合实例、显式区域参数和 tsum 表示。相同的局部记号问题在未编译到的下游统一改为显式 `Subtype.val` 或带括号的 term projection，包括四处实际 sixth-power unit 记号。没有添加定理假设或提高 heartbeat 预算；这些修复仍须下一轮原生 CI 验证。

已在本地合入最新基线 `e66f738`；Base 的唯一 import 冲突取双方并集，保留新的 aligned arithmetic choice 及本 PR 的唯一实际 recipe。修正 MOM_BASE/LocalGauss 四处 complexEmbedding 调用补齐原上下文参数 c；最终主定理陈述未变。合并后的完整原生检查仍待后续CI。

## `dd22356` 的原生复验

包含该基线合并与全标签资格的 head `dd22356` 已发布；run `41206596037` 的 pure job `124552815612` 再次完整成功：112 个模块、2,042 个声明、0 个非标准公理依赖。artifact `13045026083` 的 SHA-256 为 `1fb1ade44fb3932743b799997ecdca8e66e69b4c2282240b715f9c2bbbe10d6b`；已核对压缩包、原日志以及112个源码哈希与该 head 完全一致。

四个 actual/skeleton 分组均完成失败；五份 artifact 已全部下载并核对 SHA-256。arithmetic、contours、physical、skeleton 的原生日志逐条比较完全相同：七个根模块、41条诊断，完整错误上下文没有差异。完整 artifact 标识、摘要与日志 SHA-256 见 validation JSON。上一轮九根中的八个已明确实际 Built：`ActualNormFormWindowDetector`、`PhysicalFourierNormalization`、`ActualEulerRegion`、`ActualInitialEulerProduct`、`ActualDeletedEulerProduct`、`ActualZetaLogDerivative`、`PhysicalDetectionParameters`、`ActualProbeContext`。`LargeRowMellin` 的超时已消除，剩余错误是一处原权函数非负性的改写。

本批修复七根的名称解析、原积分/求和类型、自然数/实数/复数转换、有限 Poisson 原轨道权重、局部域原点的 punctured-neighborhood 实例，以及实际素数窗口有限删除等式的代数方向。另补实际 presentation 边界与两个后继 amplitude/schedule 模块缺失的命名空间；四个后继 Mellin/retained/height/full-correction 模块中的同型加法单调证明改为明确的 `add_le_add` 组合。原声明、假设、实际物理对象及公理白名单保持不变；这些新修复仍待下一轮原生编译。MOM_BASE 的测试 merge commit `794d9a5` 也返回相同七根与41条诊断；该失败运行尚未构建到 Base/LocalGauss，不能将其计为兼容验证通过。

该 arithmetic 原始日志为126,068行、7,503,795字节，其中大量为缓存重放的警告。验证脚本现仅压缩 `lake build` 的控制台显示，保留实际 Built/失败头、完整错误上下文和最终状态；每一行仍原样写入同一个 artifact 日志，所有 axiom audit 的控制台输出也保持完整。Lake 命令、全部 imports、清单、公理白名单及非零退出 gate 均未改。独立的失败子进程检查确认完整日志逐字保存且退出码7原样传播；未据此断言日志是构建时长的瓶颈。

## `e28f926` 的原生复验与当前冻结修复

head `e28f926b30be095d97a798b665551824dc40be8b` 的 [run `41208791356`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41208791356) 已全部结束。五份 artifact 的压缩包 SHA-256、解包后的原始成员及各组源码清单均已独立核验；335 个源码哈希逐一对应该原生 head。pure job `124559247053` 成功审计 112 个模块、2,042 个声明，非标准公理依赖为零，112 个源码也与当前冻结工作树完全相同。其 artifact `13045816355` 的 SHA-256 为 `537c32ec15877d1e0bdf6a01411b1ba6837cb453d9cdfb404bc50e0480c80675`。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13045816355 |
| actual-arithmetic | failure；未进入完整公理审计 | 116 | 8／19 | 13046026810 |
| actual-physical | failure；未进入完整公理审计 | 39 | 8／19 | 13045648643 |
| actual-contours | failure；未进入完整公理审计 | 56 | 7／18 | 13045709453 |
| skeleton | failure；原名及共享源严格 gate 被前置构建阻挡 | 12 | 8／19 | 13045813589 |

arithmetic、physical 与 skeleton 的八个根模块、19 条诊断及完整上下文逐字一致；contours 仅少 `PhysicalFloorSource` 的一条诊断，其余七根、18 条完整上下文一致。没有把分片未报告的错误视为该模块通过。全部 artifact、日志及清单摘要均保存在 validation JSON。

相较 `dd22356` 的七根、41 条诊断，六个旧根已在本轮原生日志明确 **Built**：`LargeRowMellin`（11 秒）、`PhysicalFinitePoisson`（7.3 秒）、`PhysicalAdditiveOrigin`（4.9 秒）、`ActualPrimeIdealWindow`（5.9 秒）、`ActualInitialLocal`（5.4 秒）及 `PhysicalAmplitudeSource`（4.8 秒）。`ActualNormFormPrimeContour` 从13条诊断推进到一处积分函数的 rewrite；其余错误来自进一步编译到的后继模块。这些单模块成功记录不替代整组公理审计。

本批已按日志修复八个根模块：`ActualNormFormPrimeContour` 的逐点函数表示；`ActualMellinRegularity` 的负幂符号归一化、导数乘法结合与真实竖线连续映射；`PhysicalPositiveMellinInversion` 的有限乘法 Haar 可积实例及逐点轨道核等式；`PhysicalFrequencyReindex` 的单位理想 coercion、实际字符/放大子命名空间与原轨道权重转换；`ActualLocalBlockSummation` 的空 Finset API 和负复数虚部化简；`ActualPrincipalSlotRemainder` 的竖线实部及积分测度；`PhysicalAmplitudeIntegral` 的常量可测 API；`PhysicalFloorSource` 的原零长度投影。另在 `ActualPrincipalResidueTails` 与 `ActualPrincipalTruncatedShifts` 补齐同形的显式竖线连续映射和测度参数。十个文件均保持原实际函数、声明与假设；当前修复仅为源码状态，尚未编译验证。

MOM_BASE 的 [run `41208797442`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41208797442) / job `124559263969` 也完成失败，exit code 为 1。它测试的是 `e28f926` 合入 `e66f738` 的 merge checkout `4a39962d3b6765a26c30a025ef8b9ea5667a1e7d`；artifact `13045219208` 的 SHA-256 `2ef25fa5bd68a3d1a5055ceb8c1b7cd692d3519dbd8b112a8b3551a3f357c4a0` 已核验。其八根、19 条完整诊断与 arithmetic 相同，没有 Base/LocalGauss 的 Built 或 Replayed 记录，不能据此认定兼容检查成功。

当前清单固定335个源模块，保留19个原名目标、三个共享源模块及原三条标准公理白名单。验证脚本未再改变，本轮原生运行已经使用压缩控制台输出并保留完整 artifact 日志。先前证据和原清单保存在历史快照中；最新清单对十个冻结修复重新计算 SHA-256，不沿用修改前的通过状态。原始 EXPANSION 完成标准、完整类型依赖审计及 PR 可审查状态仍待后续原生验证全部通过。

## `2107024` 的原生复验、冻结修复与基线清理

head `2107024b63d9de77d89e98c020cb4ce1780a21ec` 的 [run `41210967770`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41210967770) 已全部结束。五份 artifact 的压缩包摘要、解包成员及合计335个源码哈希均已独立核对，并逐一匹配该原生 head。pure job `124565668810` 成功审计112个模块、2,042个声明，非标准公理依赖为零；112个源码也与当前冻结工作树逐一相同。artifact `13046655699` 的 SHA-256 为 `235ca7736d9a58fe5962f471b43b569565b27c68672e710cb5a5d55e2e422289`；完整公理输出的 SHA-256 为 `585bb43aacca843c3788b566ea08a37a13cf3d4d7e1bf7988e76cce3fc55e267`。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13046655699 |
| actual-arithmetic | failure；未进入完整公理审计 | 116 | 9／19 | 13046826653 |
| actual-physical | failure；未进入完整公理审计 | 39 | 9／19 | 13046279967 |
| actual-contours | failure；未进入完整公理审计 | 56 | 8／18 | 13046542160 |
| skeleton | failure；原名及共享源严格 gate 被前置构建阻挡 | 12 | 9／19 | 13046543147 |

arithmetic、physical 与 skeleton 的九个根模块及19条完整诊断逐条一致；contours 仅缺 `PhysicalRecipeSchedule` 的一条诊断，其余八根、18条完整上下文一致。同一源码位置、相同首行摘要下的三条不同目标均分别保留比较，没有在汇总时去重。skeleton artifact 的 SHA-256 为 `5c121f259e0b10285eb7d52cd661a6ba02c37b1fea0c6132dffe9f2353478721`，原始 build log 的 SHA-256 为 `1995a2819d21be20a578d0867554519625bc3081daa41a316f3de6c68b7e2a5b`；其12个源码与原生 head 及当前工作树均相同。

相较 `e28f926` 的八个根模块，本轮 arithmetic 原生日志明确新编译通过六个：`ActualNormFormPrimeContour`（15秒）、`PhysicalPositiveMellinInversion`（8.6秒）、`PhysicalFrequencyReindex`（7.7秒）、`PhysicalFloorSource`（5.2秒）、`PhysicalAmplitudeIntegral`（5.4秒）及 `ActualPrincipalSlotRemainder`（9.7秒）。`ActualMellinRegularity` 与 `ActualLocalBlockSummation` 各剩一条新诊断；这些 Built 事件不替代整组的穷尽公理审计。

本批已按原生日志修复九个根模块：`ActualNormFormPrimeCap`、`ActualMellinStripDecay`、`ActualMellinRegularity`、`PhysicalInitialMellinWeights`、`PhysicalProbePoisson`、`ActualLocalBlockSummation`、`PhysicalContourMeasure`、`PhysicalRecipeSchedule` 与 `ActualPrincipalMainContour`。修复保留原声明、假设和实际物理对象，处理相应函数表示、竖线映射的点相等、可测与可积 API、局部求和以及自然数到实数的转换；尚未用后续原生运行验证这些新源码。

另有九个已冻结的后继兼容修复：七个 small/large/principal/outer/moderate 核估计模块只定点改写原分母，保留 `1/2`、`17/48`、`23/48` 等幂表达式以匹配已经证明的界；`ActualPrincipalResidueTails` 与 `ActualPrincipalTruncatedShifts` 则显式给出竖线复合映射所需的点相等。这十八个文件的当前 SHA-256 全部重算并列入 validation JSON。三个没有原生错误证据的预测性 beta 改动已撤回，不计入本批修复。

本批同时合入基线 `6eb687277d73bc16b4a3e537ba6cdd1fa0fca073`。相对 `e66f738`，该基线仅删除七个已经退役任务的 CI 工作流，没有 Lean 源码或数学陈述改动；`theta-local-wiring` 的 modify/delete 冲突按维护者删除处理，索引中已无未解决冲突。当前工作树中的十八个 Lean 修复哈希不受该合并影响。GitHub API 返回本 head 的 MOM_BASE run `41210971820` 与 THETA_GLOBAL run `41210971823` 均为 completed/cancelled，不能记为通过；Theta local run `41210971814` 的 success 仅作为独立工作流状态记录，不替代 EXPANSION 的验收。

遵照 PR #5 维护者评论 `6541316400`，完整编译输出继续只保存在 Actions artifacts 和本地诊断目录。仓库验证记录只新增源码位置、单行错误摘要、日志行号及完整上下文的 `detail_sha256`，并保留 artifact、日志、清单的摘要和所有历史语义证据。既有 JSON 没有原始多行编译上下文，无需清洗历史记录。

EXPANSION 的验收范围仍为335个源模块、19个原名目标和三个共享源模块，公理白名单仍只有 `propext`、`Classical.choice`、`Quot.sound`。基线工作流清理不减少这些 gate。当前十八个修复与完整原始接口均等待后续原生编译及公理审计，PR 尚未达到可审查标准。

## `ec60fe7` 的原生复验与六个冻结修复

head `ec60fe753f584a1a40069c36a93dbc5123a1f324` 的 [run `41214968233`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41214968233) 已全部结束。该提交以 `2107024` 为第一父提交、`6eb6872` 为第二父提交，已包含前述基线工作流清理。五份 artifact 的压缩包摘要、原始成员及合计335个分组源码哈希均已核对并匹配原生 head。pure job `124577496182` 成功审计112个模块、2,042个声明，非标准公理依赖为零；112个源码也与当前冻结工作树相同。pure artifact `13046934855` 的 SHA-256 为 `859c246c2798bb8401a6e3ed70c2f4a76131ff4e1644377a13a6391e4304116b`。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13046934855 |
| actual-arithmetic | failure；未进入完整公理审计 | 116 | 5／22 | 13048277645 |
| actual-physical | failure；未进入完整公理审计 | 39 | 5／22 | 13047843553 |
| actual-contours | failure；未进入完整公理审计 | 56 | 4／15 | 13048492226 |
| skeleton | failure；原名及共享源严格 gate 被前置构建阻挡 | 12 | 5／22 | 13048990220 |

arithmetic、physical 与 skeleton 的五个根模块、22条完整诊断逐项一致；contours 的四根、15条是其中的完整子集，仅缺 `PhysicalRecipeAssembly` 的七条诊断。比较保留同位置、同首行摘要诊断的重复次数。skeleton artifact 的 SHA-256 为 `8404c97b3d976d22dad7e8abf21f7fbd966ccfd2ca74fe61d269b78f1af15f1a`，原始 build log 的 SHA-256 为 `671c2566b81dfff54be56e58f2f85f83c825f9845bb3502f0a52402329500f76`；其12个源码均匹配原生 head。

arithmetic artifact 还保存了原生提交标识、源码归档及归档摘要。`sources.tar.gz` 的 SHA-256 为 `ec56c072c049be615931255be8126be24bcb716c86f3a74dfe376ad6c911b8ec`，其中1,112个文件逐一匹配 `ec60fe7` 的 Git blob；这提供可复现的原始源码快照，不表示这1,112个文件全部编译或通过公理审计。原来的335个源模块、19个原名目标和三个共享源模块的验收范围保持不变。

上一轮九个根模块中的八个已在本轮 arithmetic 原生日志明确新编译通过：`ActualMellinStripDecay`（8.2秒）、`ActualMellinRegularity`（7.7秒）、`PhysicalInitialMellinWeights`（5.3秒）、`PhysicalProbePoisson`（7.9秒）、`ActualLocalBlockSummation`（4.9秒）、`PhysicalContourMeasure`（9.5秒）、`PhysicalRecipeSchedule`（6.4秒）及 `ActualPrincipalMainContour`（8.5秒）。`ActualNormFormPrimeCap` 还剩一条诊断。上述单模块 Built 事件不替代失败分组尚未执行的穷尽公理审计。

本批五个原生根模块的修复均已写成：`ActualNormFormPrimeCap`、`ActualKernelRegularity`、`ActualInitialCalibration`、`PhysicalCompletedPoisson` 与 `PhysicalRecipeAssembly`。校准修复使用字面数值的复数幂 API，先精确改写再处理范数矛盾，并显式展开局部定义供类型转换；核正则性与 completed Poisson 修复按真实函数表示、测度和原始求和对象接线。assembly 的辅助 cap 定理显式纳入原证明已经使用、所有调用处已经持有的 `hB0`、`hB`、`he` 上下文，原始 EXPANSION 目标没有新增假设。

第六个文件 `ActualPrincipalResidueAssembly` 是被前置依赖阻挡的同形静态修复：五处 `Continuous.sub_const` 改为现有连续函数 API，并给 `6 * z` 的复合映射显式类型及点相等。该文件在本轮没有原生错误诊断，也没有 fresh Built 记录；没有把静态修复记为编译通过。有效的 `DifferentiableAt.sub_const` 和 `Continuous.add_const` 调用保持原样。

此前七个 small/large/principal/outer/moderate 分母家族模块，以及 `ActualPrincipalResidueTails`、`ActualPrincipalTruncatedShifts` 两个后继，在本轮仍没有新的 Built 记录。验证 JSON 保留这九项已包含在 `ec60fe7`、但仍被前置依赖阻挡的状态；它们没有因为本批仅修改六个文件而被清除或标为通过。新六个文件的当前 SHA-256 已重新计算，修复均等待下一轮原生复验。

历史语义记录、source hashes、公理清单、artifact IDs 和计数继续保留。仓库仅增加单行错误摘要、位置、`detail_sha256` 及 artifact/log 摘要；完整编译上下文仍只在 Actions artifacts 和本地诊断目录。当前19个原名目标及三个共享源模块的严格 gate 尚未通过，原始完成标准及 PR 可审查状态仍待全部原生验证达到。

## `0263481` 的原生复验、联合解析性修复与幅度宽度预算

head `0263481ab8c8f2ef30d909f6a665ed22d64e5b8c` 的 [run `41217907744`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41217907744) 已全部结束。五份 artifact 的压缩包摘要、原始成员及合计335个分组源码哈希均已核对并匹配这一原生提交。pure job `124586189983` 成功审计112个模块、2,042个声明，非标准公理依赖为零；112个源码也与最终冻结代码相同。pure artifact `13048478654` 的 SHA-256 为 `c5747c756de3a09ae5ff10ca9bb698551bf7600e9fe998c93f80f3d6359603f0`。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13048478654 |
| actual-arithmetic | failure；未进入完整公理审计 | 116 | 4／11 | 13049502116 |
| actual-physical | failure；未进入完整公理审计 | 39 | 4／11 | 13049436978 |
| actual-contours | failure；未进入完整公理审计 | 56 | 3／9 | 13049636130 |
| skeleton | failure；原名及共享源严格 gate 被前置构建阻挡 | 12 | 4／11 | 13049294518 |

arithmetic、physical 与 skeleton 的四个根模块、11条完整诊断作为多重集完全相同，比较不依赖输出顺序；contours 的三根、九条是其中的完整子集，仅缺 `PhysicalRecipeAssembly` 的两条诊断。skeleton artifact 的 SHA-256 为 `8fdce51d118ac3e671b2eb59901775ab29499ae42c5ddeea4a1210e5d699c1e8`，原始 build log 的 SHA-256 为 `d75b4edc51f6372d54ca1abf6bc692756eb2fbf505e02cfda10eebdb7bc2a684`；其12个源码匹配原生提交。包含完整源码归档的 artifacts 也已逐文件核对；arithmetic 的归档 SHA-256 为 `fcb317b5685f2192a3076af5061cb02d8d17a18f58116bbbd87c3fff577f9c1a`，1,112个文件全部匹配 `0263481` 的 Git blobs。

上一轮五个根模块中的三个已有本轮 arithmetic 日志明确的 fresh Built 记录：`ActualKernelRegularity`、`ActualInitialCalibration`、`ActualNormFormPrimeCap`。`PhysicalCompletedPoisson` 与 `PhysicalRecipeAssembly` 分别还剩一条和两条诊断；新编译到的 `ActualRowKernelHolomorphy` 有两条诊断，`ActualNormFormFullCorrection` 有六条。单模块 Built 事件仍不替代整组尚未执行的穷尽公理审计。

### 后续证明修复的不可变版本

七个证明修复文件固定在 [commit `496aee9914912e54feac9fced688ce6e61bc7f6f`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/496aee9914912e54feac9fced688ce6e61bc7f6f)，其中四个对应本轮实际根错误，三个对应已确认的相同 API 问题。`ActualRowKernelHolomorphy` 保留原可微接口，并从真实标量因子的解析性、解析坐标映射及原 joint correction 直接组合出三复变量联合解析性。原先错误调用的标量 `DifferentiableOn.analyticOnNhd` 只用于其合法的单复变量来源；最终联合解析结论及原数学域保持原陈述。

三个后继修复是 `ActualShiftedRecipeIntegrability`、`ActualPrincipalInitialTransport` 与 `ActualModerateSweepHolomorphy`。第一项展开原 product measure 的别名以取得已有有限性实例，并显式展开由原 `hzre` 给出的正半平面成员条件；后两项使用同一实际因子构造联合解析证明。它们在本轮没有对应的新原生错误诊断，均明确记为有直接 API 依据、仍被前置依赖阻挡的修复。`ModerateSweep` 四个具体标量复合点的显式等式随后固定在 [commit `b7b3375650826ae2572ecc1667a2bf54a8a016d3`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/b7b3375650826ae2572ecc1667a2bf54a8a016d3)，归入同一静态修复，不增加文件或修复计数。

### 独立的幅度宽度预算修正

[commit `7d598d966a6105f816c4b421bbd6dd8d537f0c15`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/7d598d966a6105f816c4b421bbd6dd8d537f0c15) 单独修改 `PhysicalRecipeParameters` 与 `PhysicalRecipeAssembly` 的数值构造。旧参数仅给 `width_pos : 0 < width` 和 `e_cap : e ≤ eCap`，assembly 将 detector 提供的独立 ε 用作幅度宽度，缺少它与 detector 位移及外部损失预算之间的联系。同一个实际 amplitude source 已对任意正宽度成立，因此非空性证明取 `width = 4 * eCap` 为见证，并将以下不等式记录为实际选择参数的契约：

| 字段 | 当前构造或结论 |
| --- | --- |
| 非空性见证的 `width` | `4 * eCap` |
| `width_buffer` | `2 * e < width` |
| `width_cap` | `width ≤ 4 * eCap` |

实际 `choosePhysicalRecipeParameters` 保证两个新增不等式；其接口不要求选出的宽度与上述见证宽度逐字相等。在既定 `eCap = min(lamA, lamB) / 1000` 的实例中，由 `width_cap` 得到 `width ≤ lamB / 250 ≤ lamB / 100`。这是一项协调后的数值构造修正，单独列为待验证，不计入四个原生根错误或三个后继 API 修复。由于 `PhysicalRecipeAssembly` 同时属于证明修复与宽度构造，两类改动合计八个不同 Lean 文件。

依据 [论文 TeX](../weil_seven_eighths_revised.tex) 第3868–3898行，尤其3880–3884行，幅度宽度与 detector/prime 损失必须协调选择，以获得实际幅度分箱界；第4301–4308行要求总指数损失放入固定剩余预算，第4348–4355行将实参数放在后续高度选择之前。数字4、1000、100是本实现对这些“充分小”条件的具体预算分配。原核、原标签分箱定义及全尺度 source 的量化仍用于同一个实际配方；新增不等式由构造给出，最终定理没有新增假设。第4364–4381行要求的内部高度次数先于 τ 与外部尾阶 N 的顺序也继续保留。

最终正半平面成员条件修复固定在 [commit `d972f69776401dc514d8fd5a0d9e863103f9d6d1`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/d972f69776401dc514d8fd5a0d9e863103f9d6d1)，仍属于同一个 shifted 可积性后继修复。最终代码 tree 为 `aa82b45f5f1eb4422f387bbd3fec250ece1e65b4`。本地提交与上述 GitHub 提交的对应代码树已核对一致；报告和源码清单引用正式 GitHub 版本。本次 `0263481` CI 没有验证这些后续源码。先前静态修复中仍有10项没有新的 Built 记录，原有 pending 状态继续逐项保留。

所有历史语义记录、source hashes、公理清单、artifact IDs 和计数均保留；仓库只增加单行错误摘要、位置、`detail_sha256` 及 artifact/log 摘要，完整编译上下文仍只在 Actions artifacts 和本地诊断目录。验收范围仍为335个源模块、19个原名目标、三个共享源模块以及原三条标准公理。全部后续证明与数值构造尚待原生复验，PR 尚未达到可审查标准。

## `77dbe77` 的原生复验、五处根修复与兼容接口

提交 `77dbe777f479823d0bc830f82a15e594a17191b7` 的 [run `41221403216`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41221403216) 已全部完成。五份 artifacts 的 ZIP 摘要、每个归档成员及合计335个分组源码哈希均已独立核对。pure job `124596540705` 实际审计112个模块、2,042个声明，非标准公理依赖为零；全部112个源码也与当前冻结工作树一致。其 artifact `13049498965` 的 SHA-256 为 `63cbd38a5cc748b9a5f22c1a9b235a39f1a7b4bf82e23c14feb65ac14a665486`，完整公理审计日志 SHA-256 为 `585bb43aacca843c3788b566ea08a37a13cf3d4d7e1bf7988e76cce3fc55e267`。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13049498965 |
| actual-arithmetic | failure；未进入完整公理审计 | 116 | 5／15 | 13050288916 |
| actual-physical | failure；未进入完整公理审计 | 39 | 4／9 | 13050463893 |
| actual-contours | failure；未进入完整公理审计 | 56 | 3／7 | 13049904150 |
| skeleton | failure；原名及共享源严格 gate 被前置构建阻挡 | 12 | 4／9 | 13050634333 |

arithmetic 有五个根模块、15条完整诊断；physical 与 skeleton 的四个根模块、九条完整诊断作为保留重复次数的多重集完全相同，相对 arithmetic 缺少 `ActualCompensationSlotIdentity` 的六条；contours 的三根、七条还缺少 `PhysicalRecipeAssembly` 的两条。所有共享诊断的完整上下文均逐项相同，比较不依赖输出顺序。skeleton artifact 的 ZIP SHA-256 为 `b16f32976b2d5e4e5ef93bbba86a2038e597a7d58e6c0e430139e25c057c90ea`，build log SHA-256 为 `62922fbc6c873627b8bff29ee2e8d73c7f1dc14c7a6d8bd0d6ecbb66b954a472`，其12份源码哈希与 `77dbe77` 精确一致。含完整源码归档的 artifacts 也逐文件核对了1,112个 Git blobs；arithmetic 源码归档 SHA-256 为 `df11300ff0092e5c7252c2afcff9041861b3bd22b4960b9970c0335f913f2baf`。这些归档证明源版本一致，不能替代编译或公理审计。

### 已解阻的原生模块

上一轮四个根模块中的三个已有明确 fresh Built 事件：

| 模块 | 证据分组 | 原始日志位置 | 编译耗时 |
| --- | --- | ---: | ---: |
| `ActualRowKernelHolomorphy` | `77dbe77-actual-arithmetic` | 123990 | `6.1s` |
| `PhysicalCompletedPoisson` | `77dbe77-actual-arithmetic` | 125259 | `11s` |
| `ActualNormFormFullCorrection` | `77dbe77-actual-arithmetic` | 17731 | `20s` |

这包括 `ActualRowKernelHolomorphy` 的实际联合解析性证明及两个公开 analytic helpers。该模块的编译成功解除了这条前置阻塞；它所在分组仍然失败，不能据此记整组穷尽公理审计通过。`PhysicalRecipeAssembly` 仍有两条新的原生诊断。

### 五个原生根模块的冻结修复

以下修复依据本轮完整原生错误上下文，均已写入源码，尚未经过下一轮原生复验：

| 根模块 | 本轮诊断数 | 修复内容 |
| --- | ---: | --- |
| `SmallRowCorrection` | 2 | 补全 `1 * 2⁻¹` 的单位元化简，并由已有正 margin 定理显式证明商非负。 |
| `ActualModerateSweepHolomorphy` | 2 | 使用联合解析性工具的完整命名空间，保持原实际 correction 与原解析域。 |
| `PhysicalInitialMellinTerm` | 3 | 显式化有限坐标投影、函数等式与真实三个尺度，保留原 Mellin 积分及 Poisson 系数。 |
| `ActualCompensationSlotIdentity` | 6 | 修正现有 API 名称，并显式处理依赖型 slot 索引、共轭及同一 primeScale 的正性。 |
| `PhysicalRecipeAssembly` | 2 | 通过对实际 cap 的等式消去传递依赖标签类型与来源证明。 |

这些证明修复没有增加最终目标假设，没有更换实际核、有限素数窗口、完整掩码或原归一化因子。本轮没有将同行提出但未原生通过的补丁计入成功证据。

### 一项独立的后继 API 修复

`PhysicalInitialRowSum` 的两个 `Integrable` 证明具有本轮 `PhysicalInitialMellinTerm` 原生错误所暴露的相同函数表示问题；现改为先用 `funext` 建立显式函数等式，再输运原积分性证明。该文件在本轮没有对应原生错误诊断，单独标记为静态审查后的预测修复，仍待下一轮原生编译。它不计入五个原生根模块或15条原生诊断。

### bounded 增强入口与既有公开类型

`PhysicalRecipeAssembly` 与 `PhysicalRecipeParameters` 另有一项兼容调整，与 assembly 的原生证明修复重合一份源码，加上前述一项静态后继修复，本批合计七个不同 Lean 文件：

| 入口或结构 | 当前契约 |
| --- | --- |
| `exists_bounded_physical_recipe_parameters` | 增强入口，保留同一参数存在性、全尺度实际 source，以及 `2 * e < width` 与 `width ≤ 4 * eCap`。 |
| `exists_physical_recipe_parameters` | 从增强入口投影，恢复增强前的原名公开类型。 |
| `exists_physical_recipe_expansion` | 恢复增强前的原名公开类型，继续输出同一个实际配方的几何与全尺度 source。 |
| `physicalRecipeParameters_nonempty` | 使用 bounded 入口构造原参数结构；`width_buffer` 与 `width_cap` 字段保持不变。 |

非空构造使用 `width = 4 * eCap` 作为见证；随后 `Classical.choice` 所选参数的结构保证是 `2 * e < width ≤ 4 * eCap`。结构没有导出“所选宽度等于该见证宽度”的字段，文档与下游调用均不使用这一等式。既定 `eCap = min(lamA, lamB) / 1000` 下的 `width ≤ lamB / 250 ≤ lamB / 100` 仍由这两个界给出。参数在 τ 之前固定，阈值 Z₀ 在 τ 之后选择，原全尺度 source、几何与最终目标假设保持原有顺序和含义。

最新协调评论已核对。HIGHBIN 同行撤回了自己的兼容 wrapper，转而跟随既有宽度结构；本分支保留上述向后兼容入口，结构中的两个宽度界与共享版本一致。同行评论属于接口协调依据，不作为本轮原生编译证据。

### 当前仍未通过的范围

七份源码的最终哈希已纳入335源清单，并与本轮 `77dbe77` 原生源码分别记录；本轮 CI 没有验证这些后续修改。先前13份静态修复源码本轮均没有 fresh Built 事件，其中 `ActualModerateSweepHolomorphy` 已到达原生错误并归入当前五个根模块，其余12项继续保留各自的前置阻塞状态。七份分母相关源码也仍未取得新的 Built 记录。

完整编译日志和多行错误上下文继续只保存在 Actions artifacts 与本地诊断目录；仓库证据仅记录位置、单行摘要、`detail_sha256`、artifact/log 摘要和源版本。历史快照、257份既有公理记录、artifact IDs 与计数全部保留。验收范围仍是335个源模块、19个原名目标、三个共享源模块，以及 `propext`、`Classical.choice`、`Quot.sound` 三条允许公理；这些原名与共享源严格 gate 尚未通过，PR 仍未达到可审查标准。

## `2a82988` 的原生复验、七处根修复与辅助引理签名

提交 `2a8298882530d5c4c3212cda05db8c92017b915a` 的 [run `41224037323`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41224037323) 已全部完成。五份 artifacts 的 ZIP 摘要、全部 ZIP 成员以及合计335份分组源码哈希，均已独立核对到这一不可变提交。pure job `124604331918` 实际审计112个模块、2,042个声明，非标准公理依赖为零；其112份源码仍与当前冻结工作树一致。pure artifact `13051372030` 的 SHA-256 为 `17b0ab2c9cebb22e55cda78e8881a926db162ebfd53dabe82cd838a40ed9def9`，公理审计日志 SHA-256 为 `585bb43aacca843c3788b566ea08a37a13cf3d4d7e1bf7988e76cce3fc55e267`。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13051372030 |
| actual-arithmetic | failure；未进入完整公理审计 | 116 | 7／31 | 13051803098 |
| actual-physical | failure；未进入完整公理审计 | 39 | 6／26 | 13051142878 |
| actual-contours | failure；未进入完整公理审计 | 56 | 5／20 | 13051003027 |
| skeleton | failure；原名及共享源严格 gate 被前置构建阻挡 | 12 | 6／26 | 13052420429 |

arithmetic 的七个根模块共有31条诊断。physical 的六根、26条缺少 `ActualPhysicalPrimeSlotBound` 的五条；contours 的五根、20条还缺少 `PhysicalRecipePresentation` 的六条。skeleton 相对 arithmetic 缺少 `ActualPhysicalPrimeSlotBound`，没有新增根模块；全部共享诊断逐字一致。 比较均采用保留重复次数的完整上下文多重集，不依赖日志输出顺序。skeleton artifact 的 ZIP SHA-256 为 `9b74caaa13ceddba01301edc2cfbfbf169dc9547264d70d59b91993e16dbb399`，原始 build log SHA-256 为 `f3a197db9fea8a44d7f3f03ef8d67bf989d1b52229df4f4669423763d291fe9c`，其12个源码哈希匹配本轮提交。只有 arithmetic artifact 包含完整 `sources.tar.gz`，其中1,112个 Git blobs 已逐文件核对；该源码归档 SHA-256 为 `5e02e1a6c2c64ac634ea6685a600ca00a461cb63db6f72749fac1fd3588bc70e`。其余分组核对各自 manifest，不视作另外四份独立源码归档。这些源码核验不替代编译或公理审计。

### 上一轮根模块全部已有新的 Built 记录

| 模块 | 原生证据分组 | 日志位置 | 编译耗时 |
| --- | --- | ---: | ---: |
| `ActualCompensationSlotIdentity` | `2a82988-actual-arithmetic` | 18497 | `5.6s` |
| `ActualModerateSweepHolomorphy` | `2a82988-actual-arithmetic` | 126813 | `8.8s` |
| `PhysicalInitialMellinTerm` | `2a82988-actual-arithmetic` | 125295 | `6.6s` |
| `PhysicalRecipeAssembly` | `2a82988-actual-arithmetic` | 126850 | `7.3s` |
| `SmallRowCorrection` | `2a82988-actual-arithmetic` | 19074 | `11s` |

`PhysicalRecipeParameters` 也在 `2a82988-actual-arithmetic` 日志位置126917得到 fresh Built，耗时 `5.3s`。因此上一轮 bounded 增强入口、恢复既有公开类型的 wrapper 及参数结构之间的接线已有这两份模块的实际编译证据；该证据仍不代表其所在失败分组完成了穷尽公理审计。

### 当前七个原生根模块与11份冻结源码

| 根模块 | 原生诊断数 |
| --- | ---: |
| `ActualOuterKernelDecay` | 3 |
| `ActualPhysicalPrimeSlotBound` | 5 |
| `PhysicalInitialMellinAbsolute` | 11 |
| `PhysicalRecipePresentation` | 6 |
| `LargeRowAllScales` | 3 |
| `PrincipalRowLocal` | 2 |
| `SmallRowKernel` | 1 |

本批七个根模块的源码修复已经冻结，包含现有 API 名称、依赖类型的表达、函数等式输运、数值不等式及多余化简步骤的修正。`SmallRowKernel` 删除了目标已展开后不再起作用的 `dsimp`；`PrincipalRowLocal` 使用明确的单位元化简及原 margin 正性；`PhysicalRecipePresentation` 保留原标签嵌入与积分函数，以显式函数等式传递积分性，并从相同中心范围直接证明同一 cap 界，避免纯数值证明意外要求测度实例。真实源、标签、阈值与原实际核继续使用同一数据。

另有四份独立静态后继修复，依据已观测原生错误或已编译同形证明，均没有本轮原生错误诊断或新的 Built 记录：`PhysicalInitialMellinIdentity` 打开已有父命名空间以访问原 `ExteriorIdeal` 等名称；`ActualModerateKernelDecay` 显式给出外范数正性并归约实际 character；`ActualModerateCorrectionBound` 显式给出同形复幂估计中的外范数正性与乘积非负性；`PhysicalInitialRowTruncation` 在逐点函数等式中展开 `Function.comp_def`。这四份源码单独标记待验证，不计入七个原生根模块。`ActualPhysicalPrimeSlotBound` 末段依赖型 `Fin` 索引的 `erw` 调整也是静态后继修复，位于本来就有五条原生诊断的文件中，不额外增加文件或原生诊断计数。本批因此合计11个不同 Lean 文件。

### 辅助全复性引理的签名修正

按照接口变更说明要求，`Expansion.Project.all_complex_of_original_probe` 的新旧签名分别列出。旧项是失败的 elaboration 结果，并非已编译成立的定理：

| 版本 | 参数与结论 |
| --- | --- |
| 旧失败尝试 | `(K : Type) [Field K] [NumberField K] : ∀ v : InfinitePlace K, v.IsComplex` |
| 当前修正 | `(K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (P : ProbeData K S) : ∀ v : InfinitePlace K, v.IsComplex` |

原源码已经声明 `P : ProbeData K S` 并在证明中使用 `P.arithmetic.primitive6`，但没有把这个仅供证明使用的 section 变量保留在辅助引理中，原生日志因此只有 `K` 与其域/数域实例，既无法解析 `P`，也无法接受已有的调用 `K S P`。新增 `include P in` 明确保留原 `P` 及其依赖的 `S`、`Fintype S`。原主 prime-slot 定理本来就接收这个同一 `P`，其陈述没有改变，也没有增加独立 `hcomplex` 或最终定理前提；全复性仍由该 probe 中既有的六次本原单位根推出。

这与 [论文 TeX](../weil_seven_eighths_revised.tex) 第377–378行的固定数域设置一致：工作扩张 `K = F(ζ₁₂)` 是全虚的，并包含 `μ₁₂`。此处只修复已有形式化输入在辅助引理中的绑定与传递，不把一般数域无条件宣称为全复数域。辅助签名修正仍待下一轮原生复验。

### 当前证据边界与保留的量词

原幅度宽度的精确区别保持不变：非空构造使用 `width = 4 * eCap` 的见证，`Classical.choice` 所选结构导出 `2 * e < width ≤ 4 * eCap`，没有导出所选宽度等于该见证的字段。bounded 入口与旧名兼容入口的含义及原全尺度 source 的量化顺序继续保留。

此前14份静态修复记录中，`ActualModerateSweepHolomorphy`、`ActualShiftedRecipeIntegrability`本轮已有明确 fresh Built 事件；另外12份仍没有该证据。`PhysicalInitialRowSum` 仍被前置构建阻塞，不能计为通过。七份分母相关源码也继续按各自原生状态记录，其中新报告错误的文件已归入当前根修复，不能用旧的 pending 或未报错状态代替本轮结果。

11份当前冻结源码的哈希与本轮原生源码分别记录在335源清单中；本轮 CI 没有验证这些后续改动。完整编译上下文仍只在 Actions artifacts 和本地诊断目录，仓库证据仅保留位置、单行摘要、`detail_sha256`、artifact/log 摘要及源版本。全部历史快照、257份既有公理记录及原 artifact IDs 和计数继续保留。验收范围仍为335个源模块、19个原名目标、三个共享源模块，严格允许公理仍只有 `propext`、`Classical.choice`、`Quot.sound`；原名与共享源的严格 gate 尚未通过，PR 尚未达到可审查标准。

## `0460b9c` 的原生复验与六处根修复

不可变提交 `0460b9c217f4a272d6cad6158ffc321d0a596bf8` 的 [run `41227268916`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41227268916) 已完整结束。五份官方 artifacts 的 ZIP 摘要、全部 ZIP 成员以及335份分组源码清单均已核对到该提交。pure job `124613922103` 审计112个模块、2,042个声明，非标准公理依赖为零；112个源码哈希仍与当前工作树一致。pure artifact `13052342394` 的 ZIP SHA-256 为 `258cc6c792f7c049895efecff2861ae52247c565ceb78fac6376fe84777249e0`，公理日志 SHA-256 为 `585bb43aacca843c3788b566ea08a37a13cf3d4d7e1bf7988e76cce3fc55e267`。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13052342394 |
| actual-arithmetic | failure；严格审计被前置构建阻挡 | 116 | 6／12 | 13052568623 |
| actual-physical | failure；严格审计被前置构建阻挡 | 39 | 6／12 | 13053112645 |
| actual-contours | failure；严格审计被前置构建阻挡 | 56 | 5／10 | 13052826552 |
| skeleton | failure；严格审计被前置构建阻挡 | 12 | 6／12 | 13052524716 |

arithmetic、physical、skeleton 的六根、12条完整诊断多重集相同；contours 的五根、10条是其子集，差集恰为 `PhysicalRecipePresentation` 的两条。比较保留重复次数并覆盖完整上下文，不以摘要替代原始日志。skeleton artifact 的 ZIP SHA-256 为 `408b861c619fac21b0bb3e7978e9a74a6e58816c6406dc89f1ab89bf12a95db0`，build log SHA-256 为 `7b5a3be140ef1d79d5116efc0d6063d934a895a52e4030646c65a2eb2844ace1`；其12份源码清单与原生提交及当前工作树均匹配。四个失败分组均未进入完整公理审计；skeleton 的19原名目标与三个共享源模块严格 gate 也均未运行。

只有 arithmetic artifact 包含完整 `sources.tar.gz`，归档中的1,112个文件均与该原生提交的 Git blobs 一致，其 SHA-256 为 `5d67b2b382e075be764cb6c3f1bcc3b7912e4f7594caa62dc7c73e6c8e72f45e`。其他分组提供并核对各自 manifest 与编译输出，不计作另外四份独立源码归档。外部分支或 PR merge checkout 的结果不计入本分支验收。

### 上一轮七个根模块中的六个已有新的 Built

| 模块 | 原生证据分组 | 日志位置 | 编译耗时 |
| --- | --- | ---: | ---: |
| `ActualOuterKernelDecay` | `0460b9c-actual-arithmetic` | 125755 | `12s` |
| `ActualPhysicalPrimeSlotBound` | `0460b9c-actual-arithmetic` | 126475 | `5.0s` |
| `PhysicalInitialMellinAbsolute` | `0460b9c-actual-arithmetic` | 125349 | `5.2s` |
| `LargeRowAllScales` | `0460b9c-actual-arithmetic` | 126097 | `4.7s` |
| `PrincipalRowLocal` | `0460b9c-actual-arithmetic` | 127029 | `8.9s` |
| `SmallRowKernel` | `0460b9c-actual-arithmetic` | 126212 | `10s` |

`PhysicalRecipePresentation` 未计入这六个通过编译的模块：其上轮标签嵌入与 cap 绑定错误已不再报告，但两份逐点函数等式仍各留下一个局部目标，本轮据完整日志继续修正。每条 Built 记录只说明对应原生模块实际编译成功；所在分组失败，不能宣称全组穷尽公理审计通过。

`ActualPhysicalPrimeSlotBound` 的 fresh Built 特别确认了上一节所列 `all_complex_of_original_probe` 参数绑定修正：已有的 `P : ProbeData K S` 及依赖参数在辅助引理中被保留，其消费者成功编译。原主 prime-slot 定理的陈述保持不变，没有增加独立全复性假设或新的最终目标条件。该辅助签名已经有本分支原生编译证据，不再描述为“等待第一次编译”；原名严格 gate 仍然未通过。

### 本批六个原生根与两份静态后继

| 原生根模块 | 原生诊断数 |
| --- | ---: |
| `ActualModerateCorrectionBound` | 3 |
| `ActualPrincipalKernelBound` | 2 |
| `PhysicalCompensatedInitial` | 1 |
| `PhysicalRecipePresentation` | 2 |
| `LargeRowKernel` | 2 |
| `SmallRowSum` | 2 |

当前八份改动均为局部证明修复，原实际行、核、标签、归一化及目标陈述不变。`SmallRowSum` 显式给出幂函数重写的指数与自然数3，避免匹配到局部定义展开或未定的 cast；`ActualPrincipalKernelBound` 明确化简 `conjugate 1` 并删除已无作用的 `dsimp`；`PhysicalRecipePresentation` 在同一原目标集合上显式呈现依赖条件分支，直接应用 `dif_pos hu` 或 `dif_neg hu`。`LargeRowKernel` 的空化简与实数常量化简、`ActualModerateCorrectionBound` 的非负乘法估计与幂表达、`PhysicalCompensatedInitial` 的原始定义归约也均按本轮完整原生日志修复。

此前静态预检指出的 KernelBound 和 LargeRowKernel 空 `dsimp`，本轮日志已经明确报告，因此计入上述原生根。另两份仍单独记作静态后继：`ActualPrincipalZShift` 删除同形空化简；`ActualPrincipalResidueAssembly` 仅在需要代入零高度后化简的位置使用当前 Mathlib 的 `Continuous.comp'`，使组合显式呈为 lambda。这两份文件本轮没有相应原生错误诊断，也没有 fresh Built，不能并入12条原生诊断或计作已验证。

此前17份静态修复记录中，`ActualOuterKernelDecay`、`SmallRowKernel`、`ActualModerateSweepHolomorphy`、`ActualShiftedRecipeIntegrability`、`PhysicalInitialMellinIdentity`本轮有 fresh Built；其余12份保留各自阻塞或原生错误状态。七份较早的分母相关源码只有 `ActualOuterKernelDecay` 与 `SmallRowKernel` 在本轮 fresh Built；其余成员没有被统称为通过。`PhysicalInitialRowSum` 仍无 fresh Built 记录。

### 保留的接口与验收范围

幅度宽度仍保持既定的精确语义：非空构造使用 `width = 4 * eCap` 的见证，`Classical.choice` 所选结构只导出 `2 * e < width ≤ 4 * eCap`，不导出选择结果等于该见证的字段。bounded 增强入口、恢复旧类型的兼容入口、共同全尺度数据以及先固定高度次数再选尾阶的量化顺序均保持。

八份当前冻结源码的哈希与原生 `0460b9c` 源哈希分别记录；当前改动尚未由本轮 CI 验证。全部历史快照、artifact IDs、源摘要、257份既有公理记录均继续保留。完整编译上下文仅保存在 Actions artifacts 和本地诊断目录，仓库记录位置、单行摘要、`detail_sha256` 与 artifact/log 摘要，不嵌入多行原始输出。

验收范围仍为335个源模块、19个原名目标与三个共享源模块，允许公理仍限于 `propext`、`Classical.choice`、`Quot.sound`。原始 EXPANSION 义务保持 `closed = false`，PR 尚未达到可审查标准；下一轮须继续验证这八份修复及其后继。

## `1ff1c2b` 的原生复验状态与当前源码

提交 `1ff1c2bcfb21c49c484c08db91d137064d306f58` 的 [run `41230022424`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41230022424) 已取得5个完成分组的 artifacts；对应 ZIP 的官方 SHA-256 与335份选定源码的 Git 哈希均已核对。完整日志保存在各 Actions artifacts；源码归档逐个核对 Git blob，未以归档存在代替编译证明。

| 分组 | 原生结果 | 模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13053153479 |
| actual-arithmetic | failure；构建失败，未执行公理审计 | 116 | 3／4 | 13052829870 |
| actual-physical | failure；构建失败，未执行公理审计 | 39 | 3／4 | 13053977296 |
| actual-contours | failure；构建失败，未执行公理审计 | 56 | 3／4 | 13053803302 |
| skeleton | failure；构建失败，未执行公理审计 | 12 | 3／4 | 13054866348 |

### 前轮根模块的实际编译进展

| 模块 | 证据分组 | 原始日志行 | Built 事件 |
| --- | --- | ---: | --- |
| `Expansion.ActualModerateCorrectionBound` | `1ff1c2b-actual-arithmetic` | 126549 | `ℹ [15427/15435] Built Expansion.ActualModerateCorrectionBound (5.2s)` |
| `Expansion.ActualPrincipalKernelBound` | `1ff1c2b-actual-arithmetic` | 127228 | `⚠ [15449/15474] Built Expansion.ActualPrincipalKernelBound (10s)` |
| `Expansion.PhysicalCompensatedInitial` | `1ff1c2b-actual-arithmetic` | 125841 | `⚠ [15362/15368] Built Expansion.PhysicalCompensatedInitial (5.1s)` |
| `Expansion.PhysicalRecipePresentation` | `1ff1c2b-actual-arithmetic` | 126572 | `⚠ [15430/15435] Built Expansion.PhysicalRecipePresentation (4.9s)` |
| `HeckeSkeleton.ExpansionModels.LargeRowKernel` | `1ff1c2b-actual-arithmetic` | 126114 | `⚠ [15383/15394] Built HeckeSkeleton.ExpansionModels.LargeRowKernel (6.5s)` |

这些 Built 事件保留原始模块与原 imports；失败组未完成的全声明审计仍独立记录。

### 本轮根诊断及严格 gate

| 根模块 | 在各组出现的诊断数 |
| --- | --- |
| `Expansion/ActualModerateKernelDecay.lean` | actual-arithmetic: 2；actual-physical: 2；actual-contours: 2；skeleton: 2 |
| `Expansion/PhysicalInitialRowTruncation.lean` | actual-arithmetic: 1；actual-physical: 1；actual-contours: 1；skeleton: 1 |
| `HeckeSkeleton/ExpansionModels/SmallRowSum.lean` | actual-arithmetic: 1；actual-physical: 1；actual-contours: 1；skeleton: 1 |

三个共享源模块严格 gate：`not_executed_after_build_failure`。19个原名目标严格 gate：`not_executed_after_build_failure`。完整错误上下文仅留在 artifact；仓库记录单行摘要、日志位置和完整上下文 SHA-256。

### 当前改动与后续验证

本轮在完成基线整合后，仅追加以下3份既有 EXPANSION 源码的修复，代码固定于 [`6154741`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/6154741f88abf04be323f09f1739f1f2193a5bfc)，记录如下；本轮原生结果不覆盖这些修改。

- `Expansion/ActualModerateKernelDecay.lean`
- `Expansion/PhysicalInitialRowTruncation.lean`
- `HeckeSkeleton/ExpansionModels/SmallRowSum.lean`

三份修复逐项对应本轮原生诊断：`ActualModerateKernelDecay` 直接用原 `hz` 的 `neg_le_neg` 证明同一幂指数比较，并在最终数值化简中展开局部 `A`；`PhysicalInitialRowTruncation` 向原 box/tail 恒等式明确传入同一个物理高度 `H`；`SmallRowSum` 先展开同一 rpow 加法，再以 `Real.rpow_ofNat` 归一化数字3，保留原非负乘法比较。原定理陈述、假设、实际积分、行及指数均不变。本批没有额外静态后继改动。

### 基线合并与本任务修复分别记录

最新基线 [`0af8c1a`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/0af8c1a8627f9515ccd9258421de8e061af7fc0a) 通过正式合并对象 [`f25337d`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/f25337d7ecedcd45a5032809ad8e09928fd9c21d) 接入，其父提交为本轮原生 `1ff1c2b` 与该基线。合并树 `3874ed46b22d65c195a7992d9a3a259f634c4911` 与本地 `970ce9b` 逐字一致。

这一基线净增274份 `MOM_INV_STEP` Lean 源码，另有该任务的 `verify.py` 与工作台账变化。对335份选定 EXPANSION 源码的项目导入闭包检查没有发现这些新增文件；它们单列为基线整合，不计入本批三份 EXPANSION 修复，也不宣称已在本任务中编译。`scripts/expansion_verify.py`、EXPANSION 工作流、19个原名目标与三个共享源模块均保持原有验收范围。

三份 proof 修改位于正式代码对象 [`6154741`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/6154741f88abf04be323f09f1739f1f2193a5bfc)，其树与本地 `d2509b2` 完全一致；其父为上述基线合并对象。该代码树尚未获得新的原生 CI 通过记录，本轮 `1ff1c2b` 的结果不覆盖它。最终 `HeckeEndpointTarget.lean` 与 `HeckeSkeleton/Main.lean` 未变。

当前全部源 SHA-256 与原生源 SHA-256 分别保存。独立 Cg 复现、静态 API 审查及同行评论仅作为修复依据，不记录为原模块原生编译成功。历史快照、既有公理记录和旧 artifact 证据均保留；完整公理白名单、原19目标、三个共享源模块及所有原 imports 不变。

## `6709923` 的原生复验与六份候选证明修复

提交 `6709923e324f5ee3e4d529dc46a505b6b47de49b` 的 [run `41265148631`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41265148631) 五组已全部结束。五份 artifact 的官方 ZIP SHA-256、原始日志摘要和335份选定源码的 SHA-256 均已独立核验，对应同一不可变原生提交。完整编译上下文仍只保存在 Actions artifacts 与本地诊断目录。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13066854222 |
| actual-arithmetic | failure；构建失败，未执行公理审计 | 116 | 4／5 | 13067735684 |
| actual-physical | failure；构建失败，未执行公理审计 | 39 | 4／5 | 13067960251 |
| actual-contours | failure；构建失败，未执行公理审计 | 56 | 3／3 | 13067241776 |
| skeleton | failure；构建失败，未执行公理审计 | 12 | 4／5 | 13067432114 |

arithmetic、physical 与 skeleton 的四个根模块、五条诊断及完整上下文逐字一致；contours 的三条诊断是它们的精确子集，仅未报告 `PhysicalRecipeRemainders` 的两条错误。分组没有报告某个错误，不等于该模块通过。

arithmetic artifact 中的 `sources.tar.gz` 包含1,387个文件，逐个与原生 `6709923` 的 Git blobs 完全一致；归档 SHA-256 为 `aa583569d10f378dd8b82637104cc2a404206bb4d101ac7ebab6ad2f7a25380b`。这与旧轮归档的1,112个文件分别记录。已有基线合并 `f25337d` 及其中274份 `MOM_INV_STEP` 新源码已包含在本轮 checkout 中；文件归档不代表这些闭包外模块已经编译。本批没有新增基线合并，六份 EXPANSION 证明修改单独计数。

### 上轮三个根模块均已实际 Built

| 模块 | 原生证据分组 | 原始日志行 | Built 事件 |
| --- | --- | ---: | --- |
| `Expansion.ActualModerateKernelDecay` | `6709923-actual-arithmetic` | 126623 | `⚠ [15432/15436] Built Expansion.ActualModerateKernelDecay (18s)` |
| `Expansion.PhysicalInitialRowTruncation` | `6709923-actual-arithmetic` | 126360 | `⚠ [15397/15412] Built Expansion.PhysicalInitialRowTruncation (6.7s)` |
| `HeckeSkeleton.ExpansionModels.SmallRowSum` | `6709923-actual-arithmetic` | 126146 | `⚠ [15385/15397] Built HeckeSkeleton.ExpansionModels.SmallRowSum (7.3s)` |

上述三份源码与当前候选相同，原本的指数比较、局部常量展开、高度参数和数字幂改写已得到原模块编译确认。它们所在的整组仍失败，因此这些 Built 事件不能替代穷尽公理审计。

### 本轮四个原生根与对应候选修复

| 原生根 | 原生位置／诊断 | 当前证明修复 |
| --- | --- | --- |
| `HeckeSkeleton/ExpansionModels/LargeRowSum.lean` | 149:8；`tsum_subtype` 无法匹配局部 `rows` | 先仅展开同一个 `rows`，再应用原 subtype 求和恒等式。 |
| `Expansion/ActualPrincipalVerticalRemainders.lean` | 161:4；原核界与局部 `F`、`b` 目标未归约到同一表达式 | 明确化简原 `F`、`b`、余量核、`R` 与指数等式，保留原高度盒及目标幂。 |
| `Expansion/ActualOuterTailSums.lean` | 70:23；行范数的负实幂尚未化为逆幂 | 从原理想范数正性给非负前提，再用 `Real.rpow_neg`、`Real.rpow_two`，最后完成同一乘法重排。 |
| `Expansion/PhysicalRecipeRemainders.lean` | 102:78；字段记号解析失败；110:15；后继化简无进展 | 将同一个有限集的 `.filter` 字段 token 保持在一起；原 `hsector` 改写及选行集合不变。后继化简错误仍待新原生结果确认消除。 |

三个共享源模块与19个原名目标的严格 gate 均为 `not_executed_after_build_failure`。没有对失败 elaboration 的公理输出作成功推断；白名单仍只允许 `propext`、`Classical.choice`、`Quot.sound`，包含类型依赖。

### 两份静态后继与当前源码标识

`ActualPrincipalUniformDecay` 的三处与 `ActualPrincipalSweepDecay` 的两处数字实幂归一化，统一使用 `norm_num only [Real.rpow_ofNat]` 处理字面实数指数。它们属于静态后继修复，本轮没有对应的原生根诊断，不能计入五条原生错误或记作已验证的新证明。

完整六文件候选固定于 GitHub 不可变 proof 对象 [`4386011`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/43860111ec9127778f88b6fed5269f77a12409b3)。其完整树 `8dd6299d105d8b9dcdd7ae7bce1d0439898aa7d0` 与本地观察 HEAD `31dfcafbcda3e16168a771be98ce6fe34d287964` 逐字一致。候选父链为 `6709923 → 01a530b → 089c92d → 4386011`；本记录时这些候选对象已创建，分支仍指向原生 `6709923`，尚未进行下一次分支更新或获得候选原生结果。

当前335份选定源码的哈希已重新计算，其中329份与本轮原生清单相同、6份为上述候选修改；pure 的112份源码保持相同。`GeneralHeckeSevenEighths` 所在 `HeckeEndpointTarget.lean`、`HeckeSkeleton/Main.lean`、工作流、验证脚本、全部335源模块、19原名目标与三个共享源模块的验收范围均未改。

原始义务仍保持 `closed = false`，PR 尚未达到可审查标准。57条旧 CI 记录、10份旧历史快照和257份既有公理记录原样保留；本次追加后为62条 CI 记录、11份快照，既有公理记录数量不变。原生源码、当前候选源码、单模块 Built 与最终严格 gate 分别记录，完整 compiler context 不写入仓库。

## `6d256b9` 的原生复验与四份候选证明修复

提交 `6d256b9d63f71bd900c09247a42ee4798d5731cb` 的 [run `41267321802`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41267321802) 五组已全部结束。五份 artifact 的官方 ZIP SHA-256、原始日志摘要和335份选定源码哈希均与同一不可变原生提交核对；每组保存的 audit 输入还与原版验证脚本的生成结果逐字一致。完整 compiler context 不写入仓库。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13067837016 |
| actual-arithmetic | failure；构建失败，未执行公理审计 | 116 | 4／10 | 13068029452 |
| actual-physical | failure；构建失败，未执行公理审计 | 39 | 4／10 | 13067358893 |
| actual-contours | failure；构建失败，未执行公理审计 | 56 | 3／8 | 13068700359 |
| skeleton | failure；构建失败，未执行公理审计 | 12 | 4／10 | 13068910966 |

arithmetic、physical 与 skeleton 的四个根模块、十条诊断及完整上下文逐字一致；contours 的三根、八条诊断是精确子集，仅未报告 `PhysicalRecipeRemainders` 的两处超时。缺少某一分片的诊断不能计作该模块通过。

arithmetic artifact 的完整 `sources.tar.gz` 共1,387个文件，全部逐个匹配原生 `6d256b9` 的 Git blobs；归档 SHA-256 为 `b94e1f0de73cff81585a13048519bd46beabd824af2de9d732ff7305f33dea4c`。旧轮的1,112文件归档及上一轮的1,387文件归档分别保留。已有274份 `MOM_INV_STEP` 基线新增文件仍位于本任务导入闭包之外，归档中存在它们不构成编译证据；本批没有新的基线整合。

### 上轮六份修复逐项观察

| 上轮修改模块 | 本轮原生观察 |
| --- | --- |
| `Expansion.ActualOuterTailSums` | fresh Built，arithmetic日志 127065：`ℹ [15453/15472] Built Expansion.ActualOuterTailSums (5.7s)` |
| `Expansion.ActualPrincipalSweepDecay` | 无 fresh Built 事件，也没有该文件的原生根诊断；不推断编译成功或失败。 |
| `Expansion.ActualPrincipalUniformDecay` | 无 fresh Built 事件，也没有该文件的原生根诊断；不推断编译成功或失败。 |
| `Expansion.ActualPrincipalVerticalRemainders` | fresh Built，arithmetic日志 126975：`ℹ [15446/15468] Built Expansion.ActualPrincipalVerticalRemainders (6.9s)` |
| `Expansion.PhysicalRecipeRemainders` | 仍报告原生根错误，arithmetic 共2条；当前候选继续修复。 |
| `HeckeSkeleton.ExpansionModels.LargeRowSum` | 仍报告原生根错误，arithmetic 共1条；当前候选继续修复。 |

三个 actual 分组都明确 Built `ActualOuterTailSums` 与 `ActualPrincipalVerticalRemainders`。它们的原负幂归一化及局部余量核归约已得到原模块编译确认；失败组尚未完成全声明审计。上轮 `UniformDecay / SweepDecay` 的五处静态幂修复已经包含在 `6d256b9`，本批未重复修改它们，也没有把无 fresh Built 事件当作通过。

### 本轮四个原生根及当前修复

| 原生根 | 原生位置／诊断数 | 当前证明修复 |
| --- | --- | --- |
| `HeckeSkeleton/ExpansionModels/LargeRowSum.lean` | 150:8；1条 | 向 `tsum_subtype` 明确传入原行集合与原核范数函数，使用同一等式的对称方向并化简原局部定义。 |
| `Expansion/ActualPrincipalResidueIdentification.lean` | 46、47、106、107、176、162；6条 | 用现有公开范数 API 从原范数严格小于1导出分母非零，并将原 tuple 注入性定理写成完整命名空间；没有新增假设。 |
| `Expansion/ActualPrincipalInitialTransport.lean` | 174:81；1条解析错误 | 为原解析乘积组合补齐闭括号，保留全部原乘法因子。 |
| `Expansion/PhysicalRecipeRemainders.lean` | 108:8、94:81；2条 `whnf` 超时 | 对两次原有限分组求和显式给出 Row、Label、M、原行集合和分类函数，避免未定参数引发宽泛归约；没有增加 heartbeat 预算。 |

三个共享源模块与19个原名目标的严格 gate 均为 `not_executed_after_build_failure`；未因生成 audit 文件或前置模块 Built 而将它们记作通过。公理白名单仍只允许 `propext`、`Classical.choice`、`Quot.sound`，原名检查仍包含类型依赖。

### 当前四份候选与验证边界

本批四文件 proof 候选固定于 GitHub 不可变对象 [`5ddc668`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/5ddc66867d4947eafe30e08a02b3f302c90c58a4)，其父提交为原生 `6d256b9`。完整树 `beae7e55badd5f4de78bd63929196e5928e16991` 与本地观察 HEAD `5a947cfdf1a18be4525ecb24c9a33c855e21b0f1` 逐字一致；本记录时对象已创建，分支仍指向 `6d256b9`，候选尚未取得新的原生结果。

当前335份选定源码的哈希重新计算后，331份与本轮原生清单相同、4份为上述候选；pure 的112份源码保持相同。当前新增静态后继补丁数为0，旧两份静态记录及本轮无 fresh Built 事件的事实仍单独保留。`HeckeEndpointTarget.lean` 的最终主定理、`HeckeSkeleton/Main.lean`、工作流、验证器、全部原 imports、335源码范围、19原名目标和三个共享源模块均未改变。

62条旧 CI 记录、11份旧历史快照和257份既有公理记录逐项保留；追加后为67条 CI 记录、12份历史快照，公理记录数量不变。原始义务仍为 `closed = false`，PR 尚未达到可审查标准；需继续完成四份候选及其后继的原生构建和严格公理审计。

## `3c0f712` 的原生复验与五份候选证明修复

提交 `3c0f712627c8cc195c814cceec56de4a24d0862d` 的 [run `41269662581`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41269662581) 五组已全部结束。五份官方 ZIP SHA-256、原日志摘要及335份选定源码哈希均已独立核验；每组归档中的生成 audit 输入也逐字匹配原版验证器。原生源码、当前候选及外部分支背景分别记录。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13068658444 |
| actual-arithmetic | failure；构建失败，未执行公理审计 | 116 | 3／13 | 13068894415 |
| actual-physical | failure；构建失败，未执行公理审计 | 39 | 3／13 | 13068864488 |
| actual-contours | failure；构建失败，未执行公理审计 | 56 | 3／13 | 13068938973 |
| skeleton | failure；构建失败，未执行公理审计 | 12 | 3／13 | 13069777257 |

四个失败分组的三个根模块、十三条诊断及完整上下文逐字一致。完整 compiler context 只保存在 Actions artifacts 与本地诊断目录；仓库保留单行摘要、位置及 detail SHA-256。

arithmetic artifact 的 `sources.tar.gz` 包含1,387个文件，全部逐个匹配原生 `3c0f712` 的 Git blobs；归档 SHA-256 为 `a87b870a6a3445eea286cab5260d6e57d711bb0d0f0b63179e17a2a871145032`。历轮1,112／1,387文件归档分别保留。274份既有 `MOM_INV_STEP` 基线新增源码不计入本批 EXPANSION 修改；本批没有新增基线合并，也不把归档文件存在计作闭包外模块编译成功。

### 既有修复与静态消费者的原生观察

| 跟踪模块 | 本轮原生观察 |
| --- | --- |
| `Expansion.ActualPrincipalInitialTransport` | fresh Built，arithmetic日志 127193：`⚠ [15466/15477] Built Expansion.ActualPrincipalInitialTransport (9.3s)` |
| `Expansion.ActualPrincipalResidueIdentification` | fresh Built，arithmetic日志 127126：`⚠ [15462/15477] Built Expansion.ActualPrincipalResidueIdentification (8.0s)` |
| `Expansion.PhysicalRecipeRemainders` | fresh Built，arithmetic日志 126729：`⚠ [15438/15452] Built Expansion.PhysicalRecipeRemainders (9.0s)` |
| `HeckeSkeleton.ExpansionModels.LargeRowSum` | 报告原生根错误，arithmetic 共1条；当前候选继续修复。 |
| `Expansion.ActualPrincipalUniformDecay` | 无 fresh Built 事件，也没有该文件的原生根诊断；不推断已编译、未编译或通过。 |
| `Expansion.ActualPrincipalSweepDecay` | 报告原生根错误，arithmetic 共4条；当前候选继续修复。 |
| `Expansion.PhysicalOuterRowPartition` | 无 fresh Built 事件，也没有该文件的原生根诊断；不推断已编译、未编译或通过。 |
| `Expansion.ActualLargeInfiniteTransport` | 无 fresh Built 事件，也没有该文件的原生根诊断；不推断已编译、未编译或通过。 |

InitialTransport 与 ResidueIdentification 已明确通过原模块编译；RecipeRemainders 也在 arithmetic／physical 中 fresh Built，两处先前的 `whnf` 超时已经消除，未提升 heartbeat。三个成功模块不替代其所在失败分组的穷尽公理审计。

旧 `ActualPrincipalSweepDecay` 的本轮根发生在命名空间解析及其后继目标，位置不同于此前两处字面数字幂修复；因此本轮按真实根处理。旧 `ActualPrincipalUniformDecay` 继续保留无 fresh Built 事件的事实。两份当前静态消费者的原版在本轮也均无 fresh Built 或原生根诊断，不能并入十三条原生错误。

### 三个原生根与两份静态消费者

| 类别／模块 | 原生位置或依据 | 当前修复 |
| --- | --- | --- |
| 原生根 `LargeRowSum` | 149:4；1条类型不匹配 | 同一显式 `tsum_subtype` 恒等式改用 `using!`，明确原 indicator 化简，保留原行集合、核范数及等式方向。 |
| 原生根 `ActualPrincipalSweepDecay` | 47:27、48:52、74:43、87:67；4条 | 仅补 `open HeckeSkeleton.HighBinContinuation`，解析现有 margin、正性和原 exterior-prime 范数引理。 |
| 原生根 `ActualPrincipalTruncatedShifts` | 150、151、154、155、215、216、219、220；8条 | 四个 `hbound` lambda 补齐括号与布局，化简原局部 `f`，明确相同实坐标到复数的强制转换。 |
| 静态消费者 `PhysicalOuterRowPartition` | 本轮没有该文件的原生错误 | 对原 `actualLargeTargetBoxes_eq_actualLargeRetained` 明确给出相同 Set 与 kernel，沿正向 `tsum_subtype` 使用 `using!`。 |
| 静态消费者 `ActualLargeInfiniteTransport` | 本轮没有该文件的原生错误 | 对原 `norm_actualLargeTargetBoxes_le_absolute` 明确给出相同 Set 与核范数函数，沿正向 `tsum_subtype` 使用 `using!`。 |

固定 Lean 的 [Simpa 实现](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Elab/Tactic/Simpa.lean)已交叉核对：`using!` 在最后的 `isDefEq` 使用 default transparency，`using` 使用 reducible；本轮 LargeRowSum 的原生类型差异位于 Set predicate 包装。当前 LargeRowSum 文件与外部分支固定提交 [`5736a06`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/5736a06d8c64cd81823e608285694794225f5a05) 的发布源码逐字相同，候选 SHA-256 为 `88ab4ae2270048101615b9122f72c759179e89613aa0e7e50e751a75fdc1be26`、Git blob 为 `60afbf4e56596a7eac111e1c65733ef294b5cd92`。外部分支和静态核对只作修复背景，不计为本 PR 的原生门通过。

本批五份改动均未改变原行范围、指数、核、目标陈述或假设。三个共享源模块及19个原名目标的严格 gate 仍为 `not_executed_after_build_failure`；白名单保持 `propext`、`Classical.choice`、`Quot.sound`，原名审计包含类型依赖。

### 当前五份候选及历史保留

三份原生根修复先固定于 [`d5db674`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/d5db6748c7adb00ec2daedbae4297eb7dbde4d25)；两份静态消费者随后固定于 [`0390a60`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/0390a605a1cb47f4f84ce5d59e75a6800606955d)。候选链为 `3c0f712 → d5db674 → 0390a60`；完整树 `450bb79cbbea12bf705682e80285139e1f0adc61` 与本地观察 HEAD `783c2b18533abe14df9d1a38fe80e88a139430c8` 逐字一致。本记录时这些不可变对象已创建，分支仍指向 `3c0f712`，候选尚无新的原生通过证据。

335份当前选定源码已重新计算哈希：330份与本轮原生相同、5份为候选；pure 的112份源码保持相同。最终主定理所在 `HeckeEndpointTarget.lean`、`HeckeSkeleton/Main.lean`、工作流、验证器、335模块范围、19原名目标和三个共享源模块均未改。

67条旧 CI 记录、12份旧历史快照及257份既有公理记录逐项保留；追加后为72条 CI 记录、13份快照，公理记录数量不变。原始义务仍为 `closed = false`，PR 尚未达到可审查标准；仍需原版构建及严格审计验证这五份候选和后继模块。

## `abac74b` 的原生复验与六份候选证明修复

提交 `abac74b111202a5e7907e7b76ed180e9900ab6c2` 的 [run `41273254359`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41273254359) 五组已全部结束。五份官方 ZIP SHA-256、原日志摘要及335份选定源码哈希均已独立核验；每组归档中的生成 audit 输入逐字匹配原版验证器。原生运行、当前候选与外部分支背景分别记录。

| 分组 | 原生结果 | 清单模块数 | 根模块／诊断数 | Artifact |
| --- | --- | ---: | ---: | ---: |
| pure | success；完整严格审计通过 | 112 | 0／0 | 13069924747 |
| actual-arithmetic | failure；构建失败，未执行公理审计 | 116 | 2／3 | 13070846438 |
| actual-physical | failure；构建失败，未执行公理审计 | 39 | 2／3 | 13071280831 |
| actual-contours | failure；构建失败，未执行公理审计 | 56 | 1／1 | 13071245237 |
| skeleton | failure；构建失败，未执行公理审计 | 12 | 2／3 | 13070577604 |

arithmetic、physical、skeleton 的两个根模块、三条完整诊断逐字一致；contours 只含同一条 Uniform 诊断，是前三组的精确子集。三条不同诊断为 Uniform 300:68 的欠定不等式，以及 PhysicalOuterRowPartition 88:8、170:10 的 subtype 求和改写失败。完整 compiler context 留在 Actions artifacts 与本地诊断目录；仓库只保留单行摘要、位置及 detail SHA-256。

arithmetic 的 `sources.tar.gz` 含1,387个不同文件，路径集合恰好等于工作流规定的 `git archive` 范围，逐一匹配原生 `abac74b` 的 Git blobs；归档 SHA-256 为 `e51a9e7de744f4019c2208a1b7c16c2c642ac081cd6c8ec4a08ca349d32c72ec`。这是工作流规定的源码归档范围，不是整库编译证明。274份既有 `MOM_INV_STEP` 基线新增源码与本批六份 EXPANSION 修改分开记录；本批没有新增基线合并，也不把归档中的文件存在计为闭包外模块编译成功。

### 上轮五份修复与旧静态后继的原生观察

| 跟踪模块 | 本轮 arithmetic 原生观察 |
| --- | --- |
| `Expansion.ActualLargeInfiniteTransport` | fresh Built，日志 126275：`⚠ [15397/15409] Built Expansion.ActualLargeInfiniteTransport (6.6s)` |
| `Expansion.ActualPrincipalSweepDecay` | fresh Built，日志 127366：`⚠ [15468/15477] Built Expansion.ActualPrincipalSweepDecay (19s)` |
| `Expansion.ActualPrincipalTruncatedShifts` | fresh Built，日志 127385：`⚠ [15469/15477] Built Expansion.ActualPrincipalTruncatedShifts (7.7s)` |
| `Expansion.PhysicalOuterRowPartition` | 该文件报告2条原生根诊断；当前候选继续修复。 |
| `HeckeSkeleton.ExpansionModels.LargeRowSum` | fresh Built，日志 126203：`⚠ [15390/15397] Built HeckeSkeleton.ExpansionModels.LargeRowSum (5.9s)` |
| `Expansion.ActualPrincipalUniformDecay` | 该文件报告1条原生根诊断；当前候选继续修复。 |
| `Expansion.ActualPrincipalResidueTails` | 没有 fresh Built 事件或该文件的原生根诊断；不据此推断已编译、未编译或通过。 |
| `Expansion.ActualPrincipalResidueAssembly` | 没有 fresh Built 事件或该文件的原生根诊断；不据此推断已编译、未编译或通过。 |
| `Expansion.ActualPrincipalExpansion` | 没有 fresh Built 事件或该文件的原生根诊断；不据此推断已编译、未编译或通过。 |
| `HeckeSkeleton.Base` | 没有 fresh Built 事件或该文件的原生根诊断；不据此推断已编译、未编译或通过。 |

LargeRowSum、Sweep、Truncated 的上一轮原生根已通过原模块编译；InfiniteTransport 也在 arithmetic／physical／skeleton 分别 fresh Built（6.6秒／9.3秒／7.5秒）。PhysicalOuterRowPartition 的本轮根位于88/170，区别于上轮静态修改的后继恒等式。旧 Uniform 数字幂修复之后现在出现300:68欠定目标。上述 Built 均来自失败分组，不替代穷尽公理审计。

### 两份本 PR 原生根与四份外部诊断指导的后继

| 类别／模块 | 依据 | 当前候选修复 |
| --- | --- | --- |
| 本 PR 原生根 `ActualPrincipalUniformDecay` | 本轮300:68，1条；完整上下文与先前外部同源诊断一致 | 先给出有明确类型的 `hZ45 : Z ^ (4 : ℝ) ≤ Z ^ (5 : ℝ)`，再由原 `gcongr` 处理乘积单调性。 |
| 本 PR 原生根 `PhysicalOuterRowPartition` | 本轮88:8、170:10，两条 | 88处用显式 Set、fN/f 与 indicator 中间恒等式连接两条 `tsum_subtype`，保留原逐点分拆；170处明确相同 Set/kernel，沿 `.symm` 使用 `using!` 并化简 `ite_not`。 |
| 外部原生同源后继 `ActualPrincipalResidueTails` | 外部失败源全文与本 PR 原生源相同；21条，其中20条未解析 vertical、1条2²与4的数值归约 | 只打开 `Expansion.FiniteTripleContour (vertical)`；对原 hv 和目标用 `norm_num` 后 `exact hv`。 |
| 外部原生正文同源、作用域有差异的后继 `ActualPrincipalResidueAssembly` | 外部6条诊断；声明／证明正文相同，但外部打开整个 namespace，本候选仅打开 vertical，不能称全文同源 | 保留窄 open；显式参数积分的函数／集合、展开同一 heightBox、给出同一限制测度上的两条 integral_sub、明确实至复坐标和两种既有 vertical 定义。 |
| 外部原生同源后继 `ActualPrincipalExpansion` | 外部失败全文与本 PR abac 相同；46:67、70:2两条 | 明确原 Gaussian 上界的非负外乘子2^N，以 `one_mul` 消除末步残留单位；原指数、常数和尾界保持。 |
| 外部原生同源后继 `HeckeSkeleton.Base` | 外部失败全文与本 PR abac 相同；91:17、326:2两条 | 改写 hnorm/ht 后，以完整原参数 `exact radialNormalization_packet`；在实际 recipe 构造处显式提供原 `haar_isAddHaar` 的逐坐标实例族。 |

Assembly 现已由最初静态 scope 补丁扩展为六处外部诊断指导的证明修复，本批新增纯静态消费者计数为0。当前六文件均未改变原数学声明、条件、域、行集合、归一化、指数或实际核；没有提高 heartbeat 或放宽公理白名单。候选均仍待本 PR 下一轮原生验证。

### 外部证据的身份与适用范围

| 外部对象 | Artifact／ZIP SHA-256 | 实际 checkout／原生 source blob |
| --- | --- | --- |
| `Expansion/ActualPrincipalUniformDecay.lean`，run [41271811190](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41271811190) | 13070445328；`d05813a4a47728ac2b78a84205f7d420e42906a3b945b9c1c3cbc70ce0722040` | checkout `13ebfc28d14b1c0b15a872f23a674feb1d92fc6b`；blob `a8c7a23b7f3ed17f71530dd531d2eb939594ad74` |
| `Expansion/ActualPrincipalResidueTails.lean`，run [41273473300](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41273473300) | 13070395674；`e2f51de491365b42a7b4aa4949174adca0956ac576dba23099c59cf199dc7cfd` | checkout `2907a95399c5a2201abc4026b753f7a87995d781`；blob `ce5a1775c359a0559e73ebe00394d74f086fb338` |
| `Expansion/ActualPrincipalResidueAssembly.lean`，run [41273958918](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41273958918) | 13071255225；`6080f72adef5b5728f95cb288cfa55d64de1160b8703022429f8481d2834da04` | checkout `d88196e408f8484d935b10c205cbe005d2d9c38a`；blob `86cd5fe4a8741e1f824f3082320ab089812931b5` |
| `Expansion/ActualPrincipalExpansion.lean`，run [41274521652](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41274521652) | 13071301000；`313da533966c1d1f3efd73f05b8f4f60d67b6ef1d20d6c04380e424ad60838c6` | checkout `1a27ef3e90b1f205b100761a188ebaf8902a2d9a`；blob `d50b771cc47f78c2539fd898e405fb92174daf8f` |
| `HeckeSkeleton/Base.lean`，run [41274932169](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41274932169) | 13070952479；`57ab4d289c69320b45619b07e81bfa5079b6a8f6833a7f80112c6e2767c9c661` | checkout `ed04a8853e4c0989c4369868db30e2577a6fc8d5`；blob `6735b58046954fe4724ffc6a0430dd5cf63737dc` |

五份外部 artifact 都只有 `build.log` 与 `environment.log`，没有 source manifest 或源码归档。身份依据是官方环境日志记录的不可变 checkout，加上从该 checkout 获取并复算的 Git blob；Lean compiler `470d5ce1400764999581fd26d5d72b00d990b0f4`、Mathlib `0493595ecd5da8ef14742febab99728f98e948e8` 与本 PR 固定环境一致。Mathlib 对照来自本 PR 不可变 `lake-manifest.json`，不声称本 PR pure 环境日志记录了它。相同工作流／缓存流程检查未见源码覆写；外部 action 的实际解析提交未能由 job setup 日志独立恢复，这一证据边界保留。

Uniform 外部原生 blob 与本轮源逐字相同，完整诊断去掉首尾空白后也与本轮完全相同，context SHA-256 为 `830894b8a8dd12a5131901f56c44a4e7b14aa023b51504cfb43fc739764fba1b`。它只作为本轮一条 own 原生错误的交叉证据，不重复增加错误数。

Tails 的失败全文与本 PR abac 相同；当前窄 open 候选与外部 whole-open 修复全文不同。Assembly 外部失败文件既不同于本 PR abac，也不同于修复前窄 open 候选：只替换一行 full/narrow open，后者才逐字相同；去掉外部该 open 则恢复 abac 全文。当前 Assembly 候选与外部固定 `c6c7616` 证明修复也仅有该窄 open 差异，仍不能记为全文 verbatim 或本 PR 原生结果。

ActualPrincipalExpansion 外部失败全文与本 PR abac 相同；两处3行增、2行减的候选与外部固定 `896cec0` 修复全文相同，但候选仍无本 PR 原生通过证据。

Base 外部失败全文与本 PR abac 相同；该 SourceAudit job 已完成失败，取证时工作流仍可能有其他组运行。Base 的6行增、3行减仅调整原证明及定义体中的实例传递；public contract、原 Haar 测度、choice 及所有构造参数不变。外部 ActualPrincipalExpansion 候选全文与本 PR 候选相同，fresh Built 20秒及四个公开标准公理打印已核验，但仍只作背景。

外部 Uniform、Tails、Assembly、ActualPrincipalExpansion 的 Built 和若干标准公理打印仅作背景；五个外部 SourceAudit job 均完成失败。外部21条 Tails、6条 Assembly、2条 ActualPrincipalExpansion 及2条 Base 诊断不并入本轮两根三条，也不计为本 PR 的任何 gate 通过。必要的不可变 SHA、位置、context 摘要与差异边界已写入 validation JSON；完整上下文和临时下载链接没有入库。

### 当前六份候选、严格门与历史保留

候选链为 `abac74b → 09adbf9 → af7f9ab → 7e0207a → 88af45a → c11d6dd`：先提交 Uniform，再提交 Tails／Assembly 的窄 scope 与数值修复，随后加入 PhysicalOuterRowPartition 原生根及 Assembly 外部六处证明修复，接着加入 ActualPrincipalExpansion 两处修复，最后加入 Base 两处外部诊断指导的修复。最终不可变对象为 [c11d6dd](https://github.com/Rogerhu12/hecke-seven-eighths/commit/c11d6dd40b69a80effa6e24aeb2c9b1f51aa882f)，完整树 `03c117e9c3dafc0b7785de8785bcc4624a984836` 与本地观察 HEAD `d51a974ca1a09eb9a1dbcd288375c0335efa7c88` 逐字一致。本记录时对象已创建，分支仍为 `abac74b`，候选未获新的本 PR 原生通过证据。

335份当前选定源码已重算：329份与本轮原生相同、6份为候选；pure 的112份保持相同。最终主定理所在 `HeckeEndpointTarget.lean`、`HeckeSkeleton/Main.lean`、工作流、验证器、335模块范围、19原名目标与三个共享源模块均未改。

三个共享源模块及19个原名目标的严格 gate 均为 `not_executed_after_build_failure`；skeleton 甚至未生成这两类 audit 输入与日志。原名审计继续包括类型依赖，允许公理只含 `propext`、`Classical.choice`、`Quot.sound`。

72条旧 CI 记录、13份旧历史快照及257份既有公理记录逐项保留；本轮始终只追加五组与一份快照，保持77条 CI 记录、14份快照，公理记录数量不变。原始义务仍为 `closed = false`，PR 尚未达到可审查标准；仍需原版构建和严格审计验证这六份候选及后继模块。

## `2661e98` 的两组严格通过与三份原生根修复

提交 `2661e988b206b1ca348daa5d39c112950ecde00c` 的 [run `41275908774`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41275908774) 五组及所有 Post 步骤均自然完成；下一次分支更新以这轮完整结果为依据。五份官方 ZIP、335份选定源码、原生成 audit 输入和1,387文件源码归档均完成核验。工作流、验证器、完整 imports 与公理门保持原版。

| 分组 | 原生结果 | 清单模块 | 严格审计声明／非标准依赖 | 根／诊断 | Artifact |
| --- | --- | ---: | --- | ---: | ---: |
| pure | success | 112 | 2042／0 | 0／0 | 13070374222 |
| actual-arithmetic | failure | 116 | 构建失败，未执行 | 2／2 | 13071615568 |
| actual-physical | failure | 39 | 构建失败，未执行 | 2／2 | 13070408757 |
| actual-contours | success | 56 | 709／0 | 0／0 | 13071645813 |
| skeleton | failure | 12 | 构建失败，未执行 | 3／3 | 13071467551 |

arithmetic 与 physical 的两条完整 compiler contexts 逐字一致，且是 skeleton 三条的精确子集；skeleton 另有 Base 的实例错误。pure 和 contours 无编译根诊断。提取器仅把独立的 Lake 失败目标汇总排除在单条 compiler context 外，原始日志、ZIP 与历史记录没有改写。

arithmetic 归档1,387个不同文件，路径集合与工作流 `git archive` 范围相同，逐个匹配原生 Git blobs；归档 SHA-256 为 `ccc04cb8466109e2776fa8a8ca8867bb11de3a3f05637c7297ffa57a6227b098`。274份既有 MOM_INV_STEP 基线源码仍独立记录；本批没有基线合并，也不把归档存在计为闭包外编译成功。

### 四份 principal 修复已获得本 PR 全声明 gate

| 模块 | contours 原生 fresh Built | 该源的严格审计状态 |
| --- | --- | --- |
| `Expansion.ActualPrincipalExpansion` | 日志126655：`⚠ [15414/15414] Built Expansion.ActualPrincipalExpansion (7.2s)` | 属于56份选定源，实际709声明／0非标准依赖 gate 已通过。 |
| `Expansion.ActualPrincipalResidueAssembly` | 日志126610：`⚠ [15413/15414] Built Expansion.ActualPrincipalResidueAssembly (7.7s)` | 属于56份选定源，实际709声明／0非标准依赖 gate 已通过。 |
| `Expansion.ActualPrincipalResidueTails` | 日志126599：`⚠ [15412/15414] Built Expansion.ActualPrincipalResidueTails (10s)` | 属于56份选定源，实际709声明／0非标准依赖 gate 已通过。 |
| `Expansion.ActualPrincipalUniformDecay` | 日志126579：`⚠ [15411/15414] Built Expansion.ActualPrincipalUniformDecay (32s)` | 属于56份选定源，实际709声明／0非标准依赖 gate 已通过。 |

这些结果现在是本 PR 原模块的完整 contours 严格审计证据，不再只是此前外部分支背景或失败组中的 Built。四份源字节与当前候选保持相同。PhysicalOuterRowPartition 和 Base 没有被 contours 清单选中，不能借用该组成功；它们在本轮其他组仍有真实根错误。

contours 原始 build.log 还明确打印四个 fresh 模块的13个公开名字：Uniform 3个、Tails 2个、Assembly 4个、ActualPrincipalExpansion 4个。逐项核验实际完整名字、源码 SHA、日志行与公理列表后，追加为13条命名记录；全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。709是该组穷尽审计总数，日志没有逐名列出全部709项，因此没有据此制造709条命名记录。

### 三个本轮原生根与候选

| 原生位置 | 原因 | 当前候选 |
| --- | --- | --- |
| `PhysicalOuterRowPartition` 105:22 | 旧调用引入本处没有的 norm-one BorelSpace 实例要求 | 直接使用已有纯算术 `frequencyRowNorm_eq_one_of_principal K Sset u hp`；目标仍是同一个主行范数等于1，不新增 BorelSpace 假设。 |
| `PhysicalInitialTailBound` 63:6 | 泛型 `rw [tsum_subtype]` 无法匹配原 subtype 总和 | 对同一非主行 Set 和 tail kernel 明确证明 subtype-to-indicator 恒等式，再接原 `Summable.tsum_eq_add_tsum_ite`。 |
| `HeckeSkeleton.Base` 329:8 | 原 Haar 证书所用 measurable/Borel 实例族没有先在构造体中固定 | 在已有 Haar letI 之前显式绑定同一个 `probeMeasures.localSpace` 与 `localBorel` 两族；原 Haar 数据、choice 与构造参数全部保持。 |

三份改动合计16行增、4行减；声明、imports、原数学条件、测度数据和常数均未改。没有添加公理、sorry、目标结论前提或更高 heartbeat。本轮没有新增外部指导或纯静态消费者修复；其他分支不同 HighBin 正文的诊断没有迁入本分支。

### 当前源码、严格终门与历史

三份候选固定于 [d2eae81](https://github.com/Rogerhu12/hecke-seven-eighths/commit/d2eae8179496a08411644f20d5e3d5a0555bb652)，父提交为 `2661e988b206b1ca348daa5d39c112950ecde00c`；完整树 `6e998657d57c4a676be07e804a993cf0edb6ced5` 与本地观察 HEAD `1c8ab77ddc76d69fe673cb3fcbaf683779610843` 一致。本记录时分支仍为 `2661e98`，下一提交尚无新的完整原生门通过证据。

335份当前源码已重新计算：332份与本轮原生相同、3份候选待重验。pure 的112份与 contours 的56份具有本轮 exact-source 严格证据；这些记录明确绑定原生266及其当时的 imports，不能视为下一提交整体通过。

skeleton 在编译阶段失败，三个共享源模块及19个原名目标的严格输入／日志均未生成，状态仍为 `not_executed_after_build_failure`。原名 gate 保留类型依赖检查与原三公理白名单。顶层 `GeneralHeckeSevenEighths` 所在文件、`HeckeSkeleton/Main.lean`、验证器、工作流、335模块及原19／3目标集合均未改。

77条旧 CI 记录、14份旧快照及257条旧公理记录的完整前缀逐项保留。本轮仅追加五组与一份快照，得到82条 CI／15份快照；追加上述13条真实命名公理记录后总数为270。原始义务仍为 `closed = false`；三份新修复与下一提交整体的原版构建及严格终门仍须通过，PR 尚未达到可审查标准。

## `d90ff1b` 的四组严格通过与两个骨架根

提交 `d90ff1b079dcff043cb2b03b367023ac500bee90` 的 [run `41277315008`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41277315008) 五组和所有 Post 步骤均自然完成，下一次分支更新以这轮完整结果为依据。五份官方 ZIP、335份选定源码、原生成 audit 输入和1,387文件源码归档均完成核验。

| 分组 | 原生结果 | 清单模块 | 严格审计声明／非标准依赖 | 根模块／诊断头 | Artifact |
| --- | --- | ---: | --- | ---: | ---: |
| pure | success | 112 | 2042／0 | 0／0 | 13070994797 |
| actual-arithmetic | success | 116 | 2110／0 | 0／0 | 13071493791 |
| actual-physical | success | 39 | 808／0 | 0／0 | 13071877396 |
| actual-contours | success | 56 | 709／0 | 0／0 | 13071932420 |
| skeleton | failure | 12 | 构建失败，未执行 | 2／65 | 13071682596 |

四个成功组的原版全声明审计均实际执行，公理依赖只有 `propext`、`Classical.choice`、`Quot.sound`。323份源的严格证据绑定 d90 的源码与依赖环境；没有把 selected 源字节相同解释为后来合并的依赖环境已经验证。

arithmetic 归档含1,387个不同文件，路径集合与工作流 `git archive` 范围相同，逐个匹配原生 Git blobs；归档 SHA-256 为 `ebb70b676e4a6ecae0a047e8e5f912457a4c4c98515144c9e1b7da8735363598`。该范围不含 vendor，不主张从这份归档验证了省略的 vendor 文件。既有274份 MOM_INV_STEP 基线源码继续保留原有证据范围，归档存在本身不等于闭包外编译成功。

### 上一批三根的原生结果与七条实际命名记录

| 模块 | 原生 fresh Built | 该源的严格审计状态 |
| --- | --- | --- |
| `Expansion.PhysicalInitialTailBound` | actual-physical 日志126887：`⚠ [15430/15432] Built Expansion.PhysicalInitialTailBound (18s)` | 属于 physical 的39份选定源，808声明／0非标准依赖 gate 已通过。 |
| `Expansion.PhysicalOuterRowPartition` | actual-physical 日志126931：`⚠ [15432/15432] Built Expansion.PhysicalOuterRowPartition (19s)` | 属于 physical 的39份选定源，808声明／0非标准依赖 gate 已通过。 |
| `HeckeSkeleton.Base` | skeleton 日志130405：`⚠ [15642/15663] Built HeckeSkeleton.Base (8.7s)` | 仅在失败的 skeleton 组 fresh Built；没有成功的该源全声明 gate。 |

physical 原始 build.log 明确打印 InitialTail 的3个公开名字和 PhysicalOuter 的4个公开名字。七项逐条核对实际完整名字、原生源码 SHA、日志位置和公理列表，全部只依赖标准三公理，并且所在两个 fresh 模块由本组全声明 gate 验证。它们以原生 d90 证据追加；Base 的失败组打印不借用其他组成功。5,669是四组穷尽审计总数，未据此制造5,669条逐名记录。

### 本轮两个 own-native 根与修复

skeleton 的 ActualRowEligibility 有4条诊断，HighBin 有61条。后者包含实例不一致引起的后续 elaboration、未知构造名和超时；65条是日志诊断头计数，不表示65个彼此独立的数学缺口。完整 compiler contexts 保留在下载取证目录，仓库只记录位置、单行摘要和上下文 SHA。

| 原生位置 | 根因与当前候选 |
| --- | --- |
| `ActualRowEligibility` 72:17 | 在原 theorem proof 中绑定同一 `probeMeasures.localSpace`、`localBorel`、`haar_isAddHaar` 实例族，恢复现成 Haar 证书的可见性；没有新增数学假设。 |
| `ActualRowEligibility` 156:81／157:2 | 把原 `Models.heights Z T i` 局部函数明确标成 `Fin 6 → ℝ`，使原索引4和 detector 展开取得既有六维模型的预期类型；函数、分量和结论保持。 |
| `ActualRowEligibility` 186:4 | 对同一 inverse-to-paired rows 证明将 `simpa only … using` 改为 `using!`，允许既有定义在最后匹配时展开；原模型和条件保持。 |
| `HighBin` 首报229:53／234:51及后继 | 仅在 `PhysicalPresentationConstructor` 现有 local-instance 块补入 `expansionNormOneSpace` 和 `expansionNormOneBorel`，让原 constructor 使用既有 norm-one 实例；未迁入外部分支不同正文或改动 euler 字段、量词。 |

两份 own-native 修复合计9行增、2行减，imports、options、公开声明、原数学条件与常数保持。没有新增外部指导或纯静态补丁，没有添加公理、sorry、目标结论前提或更高 heartbeat；修复是否清除全部级联诊断仍由下一轮原生 gate 裁决。

### 上游基线合并、当前源身份与严格终门

在两份修复之后正常合并完整上游 base `50f000eb168887afaea4ff7b1583d244f14fc7c2`。150条上游改动路径逐项核对，最终相对 proof 提交实际变化142个路径，其中115份 Lean 源（新增108份）；这些归于上游基线，不计为本任务两份修复。新增107份 LowEnergy 源未纳入本任务335选源。唯一 merge 语义处理为删除重复的窄 Expansion 库注册，最终 `lakefile.toml` 逐字仍与 d90 相同；Lean toolchain、lake-manifest、验证器、原工作流和两份顶层目标文件也都不变。依赖闭包可达的两个 vendor 模块分别新增 `Mathlib.Basic.Real.Sign` 和 `Mathlib.NumberTheory.Modular` import，其新 Git blobs 单列为候选依赖身份。原生 d90 尚未验证这两个新依赖字节及合并后的环境。

两份 own-native 修复固定于 [a346ad9](https://github.com/Rogerhu12/hecke-seven-eighths/commit/a346ad9ff833c90dbc621b8057953f309b49fe19)，父提交为 `d90ff1b079dcff043cb2b03b367023ac500bee90`；最终合并候选为 [0589cd3](https://github.com/Rogerhu12/hecke-seven-eighths/commit/0589cd3442fe868c58858675f823175be2ea00d2)，完整树 `d54bff156636f96076173275cdfe9096bb42e737` 与本地观察 HEAD `ddef928e950f55fda874e43ea81eab5d72a101ab` 精确一致。本记录时分支仍为 `d90ff1b`，新候选尚无完整原生门证据。

335份当前选定源码重新计算为333份与本轮原生相同、2份 own-root 候选待重验；合并带来的其他源码单独列入基线记录，Lake 配置保持原生完整字节。四个通过组的323份 exact-source 严格证据继续绑定 d90，当次源码及依赖环境已过；下一提交及新上游依赖环境整体仍为 pending。

skeleton 构建失败，三个共享源模块及19个原名目标的严格输入／日志均未生成，仍为 `not_executed_after_build_failure`。原名 gate 保留类型依赖检查与原三公理白名单。顶层 `GeneralHeckeSevenEighths` 所在文件、`HeckeSkeleton/Main.lean`、验证器、工作流和335模块／19原名／3严格源集合均未改变。

82条旧 CI 记录、15份旧快照和270条旧公理记录完整前缀逐项保留。本轮只追加五组及一份快照，得到87条 CI／16份快照；追加上述七条实际命名记录后总数为277。原始义务仍为 `closed = false`；两份新修复、上游合并后的完整原版构建及终门仍须通过，PR 尚未达到可审查标准。

## `f606882` 合并基线后的四组严格通过与两个后继根

提交 `f606882b1da6e40f4ec752d568fe361caed28120` 的 [run `41278811681`](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41278811681) 五组和全部 Post 步骤自然完成，下一次分支更新以这轮完整结果为依据。五份官方 ZIP、335份选定源、原生成 audit 输入和1,500文件源码归档均已核验。

| 分组 | 原生结果 | 清单模块 | 严格审计声明／非标准依赖 | 根模块／诊断 | Artifact |
| --- | --- | ---: | --- | ---: | ---: |
| pure | success | 112 | 2042／0 | 0／0 | 13072487903 |
| actual-arithmetic | success | 116 | 2110／0 | 0／0 | 13072203850 |
| actual-physical | success | 39 | 808／0 | 0／0 | 13072913078 |
| actual-contours | success | 56 | 709／0 | 0／0 | 13073291839 |
| skeleton | failure | 12 | 构建失败，未执行 | 2／5 | 13072044635 |

四组共323份选定源、5,669个声明实际严格通过。源码归档现在为1,500文件，逐一匹配 f606 Git blobs，路径集合与原工作流一致；归档 SHA-256 为 `897a9926fe61d674d0c2c4e15ba535834989b7c3307510f68637968602f25762`。增量基线文件已经属于本轮原生 checkout，不能继续把上轮1,387文件计数用于本轮，也不把归档存在当作闭包外编译成功。

上轮正常合并的 base `50f000eb`、107份新增 LowEnergy 源及142路径的集成记录保留，本轮 f606 原生四组已在该环境通过。两份更新 import 的 vendor 模块在 arithmetic 依赖构建中分别 fresh Built57s（M24258cdb51c176f1，日志10234）和13s（Maeacc31f39c2b895，日志9482）。这证明本次原生依赖构建已到达它们；原源码归档仍不含 vendor，也没有单独对所有 vendor 声明做全声明 gate。

### 上一批修复进展与本轮两根

ActualRowEligibility 的原四条诊断不再出现，原模块在 skeleton 日志131412 fresh Built8.2s。它仍属于失败组，本轮没有把其打印公理记为新的成功记录。HighBin 从61条诊断降为三处 Haar family 实例失败，仍没有 Built；其新诊断正文与旧 BorelSpace 错误不同。DetectorProfiles 的两处错误是本轮实际到达的后继根。

| 原生位置 | 当前最小修复 |
| --- | --- |
| `HighBin` 271:2／308:10／322:10 | 在 expansionScheduled_bin 与 actualHighPresentation 的证明局部显式交付原 probeMeasures 的 localSpace、localBorel、haar_isAddHaar 三个实例族；保留原 measure 数据、Haar 证书及 producer 调用。 |
| `DetectorProfiles` 253:8 | plain 分支先展开 plainPolynomial、maskValue、sharedMomentData 的标量投影，消去未使用的依赖证明字段，再改写 detectorHeights_presentation；原数学对象不变。 |
| `DetectorProfiles` 259:82 | commonPhysicalPoint 的指标证明先明确原有边界 j.val < 6，再用 omega；原三坐标映射与维数定义不变。 |

两份 own-native 根修复共19行新增、5行删除，公开数学声明、条件、域、measure 数据、常数、imports 和 options 均保持；没有新增公理、sorry、native_decide 或 heartbeat 调整。交叉审查及静态逐字核对已经完成，候选尚未接受下一轮原生编译与严格 gate。

### 480条新实印公理记录

对四份成功 strict 组的原始日志，逐条核对完整名字、完整多行公理列表、选源 SHA、源码中的实际 #print 行、日志行与 fresh Built 事件。按完整名字排除历史已记录名字，并在本轮全局去重，得到 pure 11、arithmetic 232、physical 93、contours 144，共480条；全部只依赖标准三公理。arithmetic 中两次额外 AuditSaturation 打印作为重复位置保留取证，不重复入账。

这些是日志真实出现的名字，并非从5,669个声明的汇总生成。每条 reporting_module 指打印所在模块，不推断声明归属。旧277条记录含165个不同名字，其历史重复记录全部原样保留；新增480条均未出现在旧名字集合中，总记录数为757。失败 skeleton 中的任何打印均未进入本批新增记录。

### 当前候选、严格终门与历史

取证完成后正常合并最新 base `b46a22e0834748bda242e4fd2010434b68ebeddb`。相对本轮已通过四组的 50f 基线，这只是一个上游提交、两个 shell 文件各2行新增／2行删除：restore 与 prune helper 的 release 日期字段及排序键由 createdAt 改为 publishedAt。两文件与 b46 Git blobs 完全一致；没有新增或改动 Lean 源、没有冲突或人工解冲，README 与原验收配置不变。历史 50f 的150个上游路径、142路径集成及108份新增 Lean 仍归属上一轮记录；本次 b46 增量为0份 Lean、2份脚本。原工作流仍引用 restore-lake-cache@ci/lake-cache-test，本仓库 helper 差异本身不证明外部 action 引用运行时解析发生变化。b46 与两份证明修复组成的下一完整 head 仍待原版原生验收。

两份 own-native 修复固定于 [f2b5fa4](https://github.com/Rogerhu12/hecke-seven-eighths/commit/f2b5fa400abc0891a2aecc8451e3b1c564eb4d17)，父提交为 `f606882b1da6e40f4ec752d568fe361caed28120`。正常合并最新 b46 基线后的最终候选为 [a378db7](https://github.com/Rogerhu12/hecke-seven-eighths/commit/a378db72058df2ccbea74e293c3e3b4595b9013d)，双亲为 `f2b5fa400abc0891a2aecc8451e3b1c564eb4d17` 与 `b46a22e0834748bda242e4fd2010434b68ebeddb`；完整树 `a2aedae92e0ef5628d90360c61224c3b89970c20` 与本地 HEAD `27ad98ca24d533df85bf9cc21501ab1027636c78` 精确一致。本记录时分支仍为 `f606882`。335份选源重新计算为333份原生同源、2份候选；四个成功组的323份源证据绑定本次 f606 及其当时的环境，下一提交整体仍待验证。

skeleton 构建失败，三个共享源模块与19个原名目标的严格输入／日志均未产生，仍为 `not_executed_after_build_failure`。原名 gate 的类型依赖检查和标准三公理白名单完整保留。顶层 `GeneralHeckeSevenEighths` 所在文件、`HeckeSkeleton/Main.lean`、验证器、原工作流、toolchain、Lake 配置与包清单均未改变，335／19／3原验收集合保持。

87条旧 CI、16份旧快照、277条旧公理记录完整前缀逐项不变；本轮只追加五组和一份快照，得到92条 CI／17份快照，再追加480条实印记录得到757。原始义务仍为 `closed = false`；当前两个源修复及完整原版终门尚须通过，PR 仍未达到可审查标准。

本轮 PR 说明与评论已读至88条／`6554586321`；最近重述的旧 Base 上下文与外部 Calibration 评论没有记作新的本 PR 原生根、产物或候选。
