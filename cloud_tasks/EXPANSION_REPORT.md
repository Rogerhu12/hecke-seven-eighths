# EXPANSION：实际展开、同源检测配方与验证状态

分支 `codex/expansion-detector-20261030`，PR #5，基线 `dtests-handoff`。

**任务仍在进行，原始目标尚未全部通过。** 下文把实际成功的编译与已经写成但尚待编译的源码分开列出。辅助模块通过不替代 `expansionRecipeRaw`、原始 EX 定理及其类型依赖的严格验收；达到全部标准后才将 PR 标为可审查。

## 原始目标与实际对象

最终展开必须作用于原 `normalizedProbe - principalLineProbe`。它由主行三项余量、小行、绝对大行、固定缓冲壳层块及真实高度尾组成。物理字符、完整理想掩码、有限素数窗口、全部 selected/unselected compensation 和原 primeNormalizer 都留在同一核中。族参数始终允许 `7/8 < B ≤ 1`，没有新增 `B ≤ 11/12` 或 `delta ≤ 5/6`。

原小行界的 saving 为 `1/50`；主行两条竖线保留 `23/960` 与 `13/9600`，第三项保留原 `principalSlotSaving`；大行目标保留 `63/800`。顶层 `GeneralHeckeSevenEighths` 的声明未改。

## 同一真实源生成见证与矩模型

共享 `HeckeSkeleton.SourceData` 固定显式全尺度 E，`SourceMomentIndexFor / ModelsFor / PolynomialCalibrationFor / RowEligibilityFor / WholeMomentProfileControlFor / UniformMomentBoundFor` 全部使用它。`recipeMomentSourceData` 使用同一 `RecipeExpansion R`；actual aliases 最后选择 `expansionRecipeRaw`。模型行宽是 `1+log 2/log U`，精确覆盖原 `U<N(u)≤2U`，多项式长度基数仍为 U，capacity 上端仍为 1。

实际 detector 端点从原 Hecke 零点、有限高度 buffered zero bounds、原删除系数和固定 cutoff 推出 terminal source、同频率 inverse/plain 乘积、两因子饱和及长度条件。它们不接受最终多项式上下界。Fourier 环境集取 `6H`，源本身不变；真实 `2pi` 频率消耗已纳入高度缓冲。有限背景取消行的纯范数极点由实际算术角色的有限纤维阈值排除。

`PhysicalAmplitudeSource / Provenance` 从原素数多项式数值构造有限 amplitude fibers，在同一物理高度盒中选择最大行数样本，并保留所有原标签及其精确来源。`PhysicalRecipeSchedule / Assembly` 固定壳层、互斥 buffered selector、sector 与标签族；每个块的值在所有尺度上都是原 shifted rowContourBox 的真实有限和。小尺度默认见证也不改这个值。

`physicalRecipeExpansion_geometry` 给统一 `MomentGeometry 22`，包括无选中行的标签；实参数范围为 8，虚参数为 `1+||heights||`，原高度锚不变。`exists_physical_recipe_parameters` 先选检测宽度、标签宽度、ceiling 与计数常数，再允许选择 tau 和尺度。新增独立正 cap 令内部 e 同时服从两项外部损失；通过同一 WitnessCover 的 loss 单调性放宽到 lamA，原壳层上端仍由 lamA 控制。没有因 lamB 很小而错误缩短壳层。

这些 actual 配方源码还须通过当前 native build，并与原 `expansionRecipeRaw` 项最终识别。

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

环境：Lean `4.35.0-rc3`，compiler `470d5ce1400764999581fd26d5d72b00d990b0f4`；Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`；项目原 implicit 选项不变。所有当前 CI 使用维护者最新 README 指定的官方 `restore-lake-cache@ci/lake-cache-test`。自定义恢复/重编译驱动已移除；编译日志、源码清单和公理输出只放 Actions artifacts。

- `5bf0cbc` 的 EXPANSION pure job `124511697073` 完整成功：穷尽审计 **1,996 个声明，0 个非标准公理依赖**。actual/skeleton 当时均被同一 physical residue cancellation 化简超时阻挡。
- `2cba624` 修复该消去证明后，skeleton 日志明确新编译 `PhysicalProbePrincipal`（14秒）、`HeckeAxiom.ProbeNormalization`（6.1秒）、`HeckeSkeleton.Base`（6.3秒）。这三项成功不表示骨架无 admissions。
- `2cba624` 的 Theta run `41193234078` 完整成功。
- `2cba624` 的 pure 新失败是 PhysicalInitialHeight 的 pi volume 实例不匹配，已改为真实 product measure-preserving 等价；skeleton 新失败集中于旧 DetectorProfiles 的 namespace、Fin6 数值实例与支持集证明，修复已写入。两组均尚须重验，未执行最终穷尽审计。
- `2cba624` 的 actual job `124514098386` 已完成失败。原始日志逐项定位到有限轮廓 transport、物理 Fourier、主行 punctured limits、小行 reciprocal/Mellin、大行 subtype 重排、实际 Euler/cast 以及 canonical amplitude 的 elaboration 根错误；本批按这些日志修复，并处理相同记号在未编译后继模块中的同形错误。尚须 CI 重验，不据静态检查宣称通过。
- 共享 SourceData 的7个公开接口已在 #12 run `41190828198` 实际 Built 并逐项验证仅三条标准公理；本分支也加入逐声明严格 gate，类型依赖同样接受检查。

历史逐模块记录保留在 `EXPANSION_VALIDATION.json`；历史 pass 不自动覆盖改动后的源码。allowed axioms 仅 `propext`、`Classical.choice`、`Quot.sound`。failed、cancelled、仅打印 Ran 或尚未编译的声明不计通过。

下一轮保留完整 source manifest 与传递公理检查，将原 actual 审计任务按 arithmetic、physical、contours 三组分配；每个模块恰归一组，所有原 imports 仍由 Lake 构建。pure 与 skeleton 各保留独立任务，skeleton 中的共享 SourceData 严格 gate 不变。拆组仅用于缩短反馈时间，未删除声明、放宽公理白名单或改变验收标准。

## 完成标准尚需接通的部分

1. 把同一真实参数选择、原四分量和上述真实尾填回 `Base.expansionRecipeRaw`，并提供该项的 `MomentGeometry 22`。
2. 接通原物理 probe 恒等式、主行/小行/大行三项目标，以及由同一 schedule 得出的 blocks 和 count；统一 A、ceiling、k、Z0。
3. 将原 hmove 的 whole-bin boundary 作为同一 tail 的一项，完成真实原始 EX-TAIL，不改变它的量词。
4. 与 #7 识别同一 raw recipe 的 actualHighPresentation 与每个实际标签 piece；不以任意可加分块替代。
5. 全部原名编译、公理检查连同类型依赖只含标准三条，更新精确验证记录与 PR 说明，再标为 ready for review。
