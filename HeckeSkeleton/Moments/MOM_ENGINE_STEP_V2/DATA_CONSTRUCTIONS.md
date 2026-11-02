# 蓝图实际数据

本清单随 2026-11-02 的蓝图方向调整重置。旧 selectedSchedule / selectedBounds / selectedExpansion / selectedNormalization 等完整实现已经移出活动模块，不再要求第一阶段写出所有生产数据。

| 数据 | 真实来源 | 验证状态 |
|---|---|---|
| SourceRequest.sourceData | base node invariant 已有 CompleteSourceBudgetData | 相同构造在旧 CI run 41419581282 编译；本批重验 |
| PreparedCall.model | base Node.mellinStrictModel | 相同构造已有 CI；本批重验 |
| preparedSourceData | 原 complete source 的 mellinStrictModel | 相同构造已有 CI；本批重验 |
| preparedNormProfiles | 原 Node.mellinStrictModel_normProfileRecipe | 相同构造已有 CI；本批重验 |
| OriginalInput.raw | 原 arithmeticAtoms.constantAtoms.raw | 仅保留实际 finite raw source；本批重验 |
| Blueprint.Call | 原 frame/schedule/profile constants/request/prepared/frequency 的记录 | 新接口，等待本批 CI |
| Call.source / normProfiles / original | 同一 request 的原 Mellin source/profile | 新接口，等待本批 CI |
| Call.localizedData / localizedSource / localizedNormProfiles | base localizeOriginalParent、localized、localizedNormProfileRecipe | 新接口，等待本批 CI |
| Call.domain / geometry | base mellinStrictModel_domain 和原 node invariant | 新接口，等待本批 CI |

这里没有 transformed source、规范化 child、terminal estimate 或 kernel estimate 的占位数据字段。之后的论文任务通过明示的存在/估计陈述提供这些对象；完整组装定理把任务证明作为参数，在证明内逐层取得并连接它们。

所有常数与源选择都保持原目标的先后量词。单点 Call 只是任务的输入包装，不声称任意 schedule/PreparedCall 都符合所有未来阶段的数值要求；这些要求将在固定的 uniform certificates 和 eligibility 中明确写出。

`AssemblyCore.parameterOutput / strictBranch / strictFamily` 已给出完整实现，只接收显式实际 frequency outputs 和外 Mellin budget。它们不 import 任何占位任务，随本批接受三公理递归审计；完整论文任务到原目标的组装将在后续批次接入。

本批也保留陈述确实使用的 SourceData / RawLeafData / NormalizedData：它们只包装 base 对象和真实有限表达式。canonicalSourceParameters 是正 min/除法构造；raw leaf 来自原 source class key、两次独立 allocation 和 base fullCorrelationHybridLeaf；不存在新的 admitted existence + choice。EstimateData 和 UniformContracts 的资格条件为明确的 orders inclusion、threshold 与原 profile window，证书不能自行选择空谓词。

第二批修正 CallData 中两处原 localization 构造的命名空间，并把原 empty-row 情形明确分出。新增全局 ProfileFormula/ProfileDictionary 和真实 passive finite carrier，防止只约束有限ideal点、任意增加Schwartz bump或重复labels/放大weights。它们仍是具体定义；只有独立的 U1/N5a 证明文件保留明确 sorry。
