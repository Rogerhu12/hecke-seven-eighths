# MOM_UNIFORM_AMPLIFY

本任务实现有限扇区重排、覆盖素数窗口的剖面接口、有限对数损失传播、
实际行的最终资格、完整理想行的六次方掩码，以及独立尺度到见证尺度的统一校准。
新证明均位于本目录。编译日志与公理报告由专用 Actions workflow 保存为 artifact。

## 证明入口

| 文件 | 结论与输入 |
| --- | --- |
| `FiniteSectorCore.lean` | 任意非负有限能量通过 `(ideal, sector)` 注入所有扇区的行集合。 |
| `FiniteSectorReindex.lean` | 仓库真实 `inverseEnergy`、`pairedEnergy` 和 unmarked ball 的三个适配器；输入为原始逐行多项式等式、行资格和注入性。 |
| `ProfileControl.lean` | 同一 `ModelProfileIndex` 覆盖 inverse、两份 plain 和全部 prime window；共同 Euler 积分界推出仓库的 `testSeminorm` 界。统一控制可重索引、可合并索引族。 |
| `FinitePropagation.lean` | 固定有限树中的加法、乘法、非负实幂、有限和/积，以及具有共同上界的归一化有限外层求和，传播明确的尺度、对数和高度次数。任意预先给定正损失吸收任意后来固定的有限对数次数。 |
| `SourceGeometry.lean` | 从真实 `BlockSource`／`WitnessCover` 提取统一长度区间、正下尺度、选中槽长度非负和原始行包含；从任意 `TargetData` 传递其原有的 2U 范数截断。 |
| `Eligibility.lean` | 严格逆矩区域、完整 κ≤1 配对区域、原行注入与六次方自由性；由实际算术字符的有限纤维构造统一底行范数阈值，同时处理 `pairedRows` 两个分支。 |
| `SixthPowerMasks.lean` | 证明实际 `decomposedZeroSlotMomentData` 的全部三项六次方掩码身份；适用于与该算术构造逐字段一致的任意 `MomentData`。 |
| `WitnessCalibration.lean` | 在整个 `0≤r≤R` 上先选放大参数与损失，后选 U、r；建立高度 ceiling 与 `∃A ceiling, ∀τ, ∃Z₀ k, ∀Z i` 的统一见证校准。 |
| `IndependentAmplification.lean` | 复用实际完整商行的 `actualTargetScaleSup_independentOrbitEnergy`，从完整行共同尺度上界推出真实多项式的见证估计。 |
| `InterfaceObstructions.lean` | 一个可机检的数值反例：所有严格区域上恒零的能量仍可违反独立尺度放大界，说明必须提供跨尺度结构。 |
| `PureAudit.lean` | 单独检查纯数值证明及其全部传递公理，允许在完整算术依赖编译期间取得独立证据。 |
| `Audit.lean` | 递归审计本任务命名空间的所有声明，包括定义、私有辅助和结构生成声明；仅准许三条标准公理。 |

## 主结论及量词

有限扇区重排针对任意真实 `MomentData` 族，保持全部扇区和原始行零掩码。
其三个不等式只使用实际有限和、逐行等式和成员关系，不假设最终能量估计。

完整理想行掩码定理证明：对外部理想乘子 a，若 u 是原模型允许的完整行，则

* `u*a^6` 仍被允许；
* 行 Hecke 字符保持相同；
* 原 mask 乘以 `if IsCoprime I a then 1 else 0`。

该定理首先对仓库已有构造证明；通用适配器的三个前提是 `allowedRow`、
`rowCharacter`、`commonMask` 与该构造的等式，不含解析矩估计。

正确的独立放大种子是已有
`ActualTargetZeroSlotScaleSupInput`：一个共同 majorant 控制范数截断内的**全部完整商行**，
并对缩短后的多项式尺度及固定紧谱参数集同时有效。
在这个明确的规范逆归纳输入下，实际放大定理给出

\[
 E(U,D)\le C\max\{U,U^{1/6}D^{5(1+a)/6}\}(UD)^\varepsilon.
\]

新见证校准在固定有界区间 `0≤r≤R` 上一致取 `D=U^r`，得到

\[
 E(U,U^r)\le C U^{\max\{1,(1+5r)/6\}+\mathrm{loss}}.
\]

保留外部高度的版本另明确使用 `U≥Z^d`（d>0）、有界见证长度和
`height≤Cht(1+T)^B`，再选足够小的 τ ceiling。内部次数先于后续外部 tail order。

## 原六个骨架义务所需的修正

基础提交：`182769d49e5c184547c0949ddc328b9e7a87e6f7`。
任务说明允许把其他任务的结果作为显式假设，并要求指出缺少必要假设的陈述。
本目录没有把未证明的源兼容性装成最终矩估计。

1. **PROFILE-UNIFORMITY。** 原 `WholeMomentProfileControl` 只枚举三份 ideal test，
   没有素数窗口。`ModelProfileControl` 已用四类实际索引补齐。
   `SourcePolynomialCalibration` 只检查实际选取的高度/shift 和有限多项式的值；
   它没有说明所有其他 ξ、σ、τ 的光滑性或统一导数界，也没有共同 Fourier 测度、
   混合参数导数和逆向阶数选择。因此实际 `moment_profile_control` 仍需 EXPANSION
   给出整个源剖面族的解析构造。有限树代数传播是已分离的证明，不声称自行构造这些解析边。

2. **FIBER-ELIGIBILITY。** `WitnessSubdivision` 的长度和 `ModerateBlock.shell`
   是裸实数；原 hcal 没有非负长度、正 shell 或 `BlockSource` 前提。
   已通过 `SourceGeometry` 从真实 `BlockSource` 证明了所需长度与下尺度界；
   原目标必须接入这个源证书。实际 finite-character exclusion 还需要底行范数
   大于一个固定阈值，不能仅给完整理想 `u*a^6` 的大范数。
   此外现有 `rows_in_norm_envelope` 只给范数 ≤2U，原 `inverse_rows` 要求 ≤U；
   需要明确统一截断或补真实更强支撑。母集的上界也不能提供趋大的底行下界。

3. **FINITE-SECTOR-REINDEX。** 三个参数化真实模型定理证明了有限和步骤；
   原名字的适配器使用同一组 hcal/hrows 调用这些定理。
   原类型仍引用尚含 admission 的 `momentModels`。`SourceMomentIndex` 的字段又经
   `targetData` 引用 `highExpansion`；`SourceMomentModels` 的构造子含有该索引。
   Lean 的公理收集会递归检查定理类型和归纳类型构造子，所以即使适配器证明体已完成，
   或只把 M 改成 `SourceMomentModels` 参数，也不能消除这条 `sorryAx` 依赖。
   原名字的传递公理与不引用这些源类型的参数化定理必须分别报告。

4. **SIXTH-POWER-ZEROS。** 原 hcal 的 `mask` 字段只覆盖 inverse/paired，
   没有 unmarked；字符校准也只覆盖物理六次方自由行。
   已证明的完整理想行身份可在 unmarked 的三个算术字段被实际源构造识别后接入。

5. **INDEPENDENT-AMPLIFICATION。** 原 `StrictUnmarkedMomentBound` 的
   `unmarkedBallEnergy` 已过滤为六次方自由行。非平凡的 `u*a^6` 不属于这些行。
   `sixthPowerFree_mul_sixth_iff` 精确说明：若 u 六次方自由，则其乘 a⁶ 后仍然自由
   当且仅当 a=1。需要用上文的完整行共同尺度种子。
   原 `WholeMomentProfileControl` 也没有约束独立 U,D 的 unmarked 族；
   不相关尺度上的测试不能用一个形式上的 mask 身份串接。
   已复用的算术放大定理针对一个预先固定的紧谱集，其常数可依赖该紧集；它不自动
   给出随高度增长的固定多项式次数。原全族目标另外需要具有统一多项式高度控制的
   完整行／剖面 scalesup 种子。不能逐 Z 扩大紧集，再把依赖该紧集的常数视为固定。

6. **AMPLIFIED-WITNESS-CALIBRATION。** 正确的统一数值定理已经提供。
   `BlockSource` 桥接已给出统一 `d=1/100` 和 `R=3/2+lam`；原源适配器
   仍须提供这个源证书以及 `M.heights`、`realShifts`、
   `imagShifts` 的实际 admissibility 证书。原 hcal/hrows/hprofiles 均未提供这些字段。

## 验证

固定环境：Lean `4.35.0-rc3`，Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`。

```sh
lake build HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.PureAudit
lake build HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.Audit
lake env lean HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/Audit.lean
lake build HeckeSkeleton.Moments
```

允许的传递公理恰为允许集合
`{propext, Classical.choice, Quot.sound}` 的子集。
`Audit.lean` 会因任何额外公理（包括 `sorryAx`）而失败。
原六个名字另在 workflow 中打印并检查；其未解决源依赖会明确使该关卡失败。
编译成功、公理成功及原骨架未解决项分别以实际日志为准。

本轮实现使用 ChatGPT（GPT-6 Astra Pro）协助完成。
