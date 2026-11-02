# 数据构造清单：先构造，再验证下游陈述

按 PR #31 评论 6573415153 调整。本文件区分实际数据字段与 Prop 证明字段；新的存在定理加占位后再取 choice，不算完成数据构造。只有来自已存在节点证书或已证明原始分析接口的 choice，才作为具体构造来源。

## 当前数据定义

| 定义 | 真实构造来源 / 方案 | 状态 | 预计构造与接线行数 |
|---|---|---|---:|
| ChildFamily.reindex / sigma | 原数据逐字段重编号 / 依赖有限和 | 已具体定义 | 45 |
| FiniteKernelFamily.reindex / sigma | 同一个原核逐字段运输 | 已具体定义 | 22 |
| Output.toConclusion | base PairedEngineConclusion.ofFintype，原 child、kernel、terminal、bound 同时传入 | 已替换占位，待 CI | 26 |
| SourceRequest.sourceData | 原 node.down.property.admissible 已有的 CompleteSourceBudgetData 证书 | 已替换占位，待 CI | 9 |
| preparedSourceData | base CompleteSourceBudgetData.mellinStrictModel | 已替换占位，待 CI | 14 |
| preparedNormProfiles | base Node.mellinStrictModel_normProfileRecipe | 已替换占位，待 CI | 10 |
| strictBranch / selectedStrictFamily | 已具体组装；四个几何字段取原节点 invariant，实际输出仍须下游生产构造完成 | 已去掉局部几何占位，待 CI | 75 |
| leafMassBudget | 直接计算同一 normalized leaf 的有限核 mass；真正的 sum bound 独立保留 | 已替换占位，待 CI | 9 |
| selectedSchedule | base StrictProfileRange / StrictProfileOrder 的真实有限 Euler 阶数；配合原 supported-volume chooser 与 backward rank 递推 | 正在构造；不是任意阶数 | 800–1,600 |
| selectedBounds | A 线 first/second physical terminal、supported exceptional、direct/pooled mass 的实际数值常数取有限 max；统一 threshold 先于 moving 数据 | 正在抽取最小数值依赖 | 1,200–2,500 |
| selectedCall | 原节点 ranked profile 证书上的实际 Mellin model control；同一原 order/window/normalizer 和实际 engine C/control | 正在构造 | 800–1,600 |
| selectedExpansion | 原 CanonicalJointFirstSource / 原 covered second stage / 原 direct+main+1+6+7 实际叶子，保留两 independent common/divisor 与同一个 pool | 正在迁移具体数据链 | 4,000–10,000 |
| selectedNormalization | base CurriedNormalizedFamily → ActualNormalizedPairFamily，carrier 保留两 passive divisor 与 rectangle bits；真实 literal side frames/profile/capacity factory | 正在迁移并合并变体 | 10,000–18,000 |

数值与数据估计包含原模块计划中的额度，不应与原预计完成行数重复相加。这些范围仍须以实际迁移闭包校正，不能把删去数据内容后的包装行数当作压缩成果。此前 57,620 行是初步总预算，尚非已落实的比较结果。

## 本批具体源数据

新增 CoveredStage（165 行）直接从 A 线 ActualGaussFiniteLeaves 提取共用的实际 carrier 和 leaf 构造，只依赖已经合入的 CoverHybridPhaseIntegral / HybridFiniteLeaf。保留 common pair、mask divisor、Cartesian cover、row label、两侧 support、inner divisor、finite phase、两组 allocation；叶子继续使用原 physical rows 与两个 Fourier kernels，并按实际 fibre multiplicity 缩放。文件没有数据或证明占位。

## 顺序与门槛

1. 实现所有数据构造及其需要的数据 helper，及时推送；当前处于此阶段。
2. 在实际对象上重新编译全部 V2 声明，记录真实 head、完整模块覆盖和结果；达到后才登记正式骨架里程碑。
3. 按最终校正的分组计划填 theorem/lemma 证明；本会话首先完成原 G1 八模块。新增构造 helper 放入对应构造组，不把未证构造算入已完成组。
4. 最终入口的全部占位清空、三公理审计及全项目门禁通过后，才可转为可审查。
