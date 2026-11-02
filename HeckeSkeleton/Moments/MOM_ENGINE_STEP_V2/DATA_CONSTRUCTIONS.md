# 实际数据构造清单

PR #31 评论 6573415153 要求先构造实际数据，再让全部下游陈述接受 CI 检验，最后分组证明。以下“已写实”表示数据已具体定义并推送，不代表其全部 Prop 证书或整个导入闭包已经编译通过。

| 定义 | 实际来源与构造 | 状态 | 构造与接线预算 |
|---|---|---|---:|
| ChildFamily.reindex / sigma | 原数据逐字段重编号和依赖有限和 | 已写实 | 45 |
| FiniteKernelFamily.reindex / sigma | 原正测度及同一核逐字段运输 | 已写实 | 22 |
| Output.toConclusion | base PairedEngineConclusion.ofFintype，同一 child/kernel/四项 terminal | 已写实，早期 CI 已编译此构造 | 26 |
| SourceRequest.sourceData | 原 node.down.property.admissible 已有 CompleteSourceBudgetData | 已写实，早期 CI 已编译 | 9 |
| preparedSourceData | 原 CompleteSourceBudgetData.mellinStrictModel | 已写实，早期 CI 已编译 | 14 |
| preparedNormProfiles | 原 Node.mellinStrictModel_normProfileRecipe | 已写实，早期 CI 已编译 | 10 |
| strictBranch / selectedStrictFamily | 原节点 invariant 的几何证书与同一实际输出 | 已写实，下游 CI 待完整通过 | 75 |
| leafMassBudget | 同一 normalized leaf 的有限核 mass，sum bound 单独证明 | 已写实 | 9 |
| selectedSchedule | VolumeChoices 的真实 supported-volume orders；ProfileChoices 合并 Euler、volume、κ 以及原 atom 和两轮 source orders 后作 backward rank 递推 | 已写实，正在修 CI universe/quantifier 问题 | 800–1,600 |
| selectedBounds | 原 physical first/second constants、supported exceptional、direct/pooled mass、Mellin profile coefficients；有限 rank max 与四类 threshold 的实际 max | 已写实，全部依赖待 CI | 1,200–2,500 |
| selectedCall | 原节点 Mellin model、actual rawAmplitude^(14cap+10)、engineScalar=1+2first+2second+exceptional+mass(rank)；实际 reference/raw-window 来自已证原 Mellin theorem | 已写实，全部依赖待 CI | 800–1,600 |
| selectedExpansion | SelectedSource/Stages/Predicates/Leaves 构造 original direct 或同 pool main/1/6/7，实际 keys.equivFin，真实两次 source 与四 terminal；空行是空有限族 | 已写实，全部依赖待 CI | 4,000–10,000 |
| selectedNormalization | 真实 selected key dispatch 到同一 covered chart/row/allocation；SelectedLeafPacket 保存原 metadata+两侧 LiteralInput；共享 covered production 保留原核与 scalar，沿 actual source_eq 连接 NormalizedFamilyAdapter | 最终接线进行中；通用实际构造链已推 | 10,000–18,000 |

这些构造预算属于 PLAN.md 的模块预算，不能重复相加。最新全项目估计是现有模块 68,920 行加 helper/证明预留 8,000 行，共 76,920 行；当前 25,778 行仍含证明占位，不能当作已完成证明的最终比较。

## 真实构造模块闭包

物理链为 FirstGaussData → FirstSource/FullSupportParameters → FirstGeometry/SourceCoordinates/PrimitiveFirstSource，再经 direct/pooled stages、源 support/gates、原 terminal 与实际 finite covered leaves。第一、第二 source 保留原物理行和 Fourier 核。

共享规范化链为 LiteralAtoms → LiteralTransforms → LiteralProfiles/Atlas/Phases → Windows/Passive/Capacity/Calibration → Production。LiteralCovered/Strip/Production 将同一 covered chart 的实际 row、二次 common label、allocation 和当前解析 window 连接起来。SelectedLiteralInputs 明确 direct/main 与 valuation 1/6/7 的 branch、union prime support、prime power 和 phase 2n。SelectedProfileData 使用已证明的 mellinStrictModel_rawWindow，保持同一原代表元、actual raw profiles 与原行中选择的 reference。

数值链为 RawTerminalData/PhysicalConstants、AnalyticChoices、MassIndexChoices、MassProfileChoices、ExceptionalChoices。contour/radius、finite-index harmonic constants、supported-volume constants 均来自已合入且已证明的原定理；系数乘积、有限 max 和 threshold 都是实际表达式。新 theorem 的占位不能作为数据 existence chooser 的依据。

## 验收顺序

1. 所有数据写实、每批即推；当前仍在此阶段。
2. 在精确 head 上编译全部真实对象及下游声明，才能登记正式陈述骨架里程碑。
3. 先完成 G1 八模块证明并以无 sorry 与递归三公理门禁验收。
4. 最终全目标清空占位并通过全项目门禁后再申请审查。
