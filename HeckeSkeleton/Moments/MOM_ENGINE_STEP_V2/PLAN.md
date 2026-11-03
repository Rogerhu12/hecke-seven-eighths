# MOM_ENGINE_STEP_V2：论文步骤蓝图

## 原目标与当前阶段

依据更新后的任务说明及 PR #31 [方向调整](https://github.com/Rogerhu12/hecke-seven-eighths/pull/31#issuecomment-6574713757)，本阶段交付必要中间陈述、显式假设下无 sorry 的完整组装和独立证明任务清单。原目标保持：

```lean
EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c
```

不更改 base 定义、mesh、supported-volume 假设或原始量词。各任务证明单独置于 Tasks 文件；数据、命题类型和组装不能导入占位任务证明。

## 当前进度

本批 68 个活动 Lean 模块，5884 物理行；g0: 53；g1: 14；g2: 1。源端六项陈述及其 SourceAssembly、四终端证书接口及 TerminalAssembly 已写出；规范化后半陈述、完整 conditional assembly 与最终入口仍在接线。**尚未宣告完整蓝图编通。**

前一轮 b2fa7c15 的 CI 已完成且日志已读：AssemblyCore、NormalizationAssembly、UniformAssembly 和 U1 陈述/依赖已编过；仅 SourceData 缺少 CanonicalRowBallChart import、CalibrationData 的 NNReal 记号导致两处上游根错误，本批逐项修复。N5a 与 U1 均已在 PR 宣告冻结。

候选数据同时修正真实 passive carrier：恢复原 smooth supports，保留 fixed cS 与 paidSupport 的 mask，只对 residualDeletion 做有限 Möbius 展开。唯一标签来自真实 divisor/occurrence allocation；不能引入重复标签或任意缩放 profile/normalizer。该规范化接口尚未冻结。

## 独立任务与冻结纪律

完整的 **24 项**任务及预计陈述、依赖、论文行号、规模见 [TASKS.md](TASKS.md)，亦已提前贴到 [PR #31](https://github.com/Rogerhu12/hecke-seven-eighths/pull/31#issuecomment-6575698539)，不再等待全部组装完成才分发。

- N5a：已冻结于 d4568a30。独立会话只修改 ProfileFormulaTask.lean 及相邻新建私有 helpers。公开陈述或其类型含义变更先提 PR 评论。
- U1：已冻结于 b2fa7c15，包含原问题允许的 Hp 非负和严格 child profile 所需最小 Cp，并通过独立模块编译；公开陈述或依赖类型含义不得默改。
- 其余任务：当前均为草案。定稿后逐项宣布冻结，不能默改已交付的签名。

## 精确组装与预算

组装先按原 pairedRows 是否为空分支；空行由 base 的真实零输出解决。非空分支必须沿同一原 source trace、同一 allocation/refinement、同一 normalized family 与 kernels，取得四 terminal 及实际 mass，并恢复 child 的全部五项 recursive invariant。最后通过原 Mellin 外层 budget 构造 PairedStepHypothesis。

条件组装的三公理通过不代表各数学任务已证明。实例化 sorry Tasks 的最终入口必须公开保留其 sorryAx 状态，直到每项任务被实证替换。

24 项预计证明总规模为 **65,000–92,500 行**（包含各私有 helper）；另加公共蓝图数据与组装。此前不完整草图 57,620 行、旧迁移方案 76,920 行均保留为历史基准，不能改名隐藏增长。未实现的通用化不预记节省，完整成品仍以 <100,000 行为上限。

旧 90 模块实现中的86个文件已从活动目录移除，可在 Git 历史查询；不复制到新 reference 编译目录。

## 验证与推送

只在 GitHub CI 编译，不在本地运行 Lean/lake。完成一批即通过 GitHub 直接提交，等待该轮专用 CI 完成并读日志才推下一批。CI 精确 checkout head、检查 manifest 覆盖所有模块，并在 fresh Lean 中递归审计 g0 全部 V2 声明，只允许 propext、Classical.choice、Quot.sound。g1 显式任务占位与 g2 聚合入口不冒充最终证明。

PR 保持 [不合并] draft；完整蓝图与无 sorry 条件组装在同一 head 编通后登记阶段里程碑，随后继续各独立任务的实证工作。


本批补入明确的 T3a/T3b 及 N8a：T3a 只处理由原 leaf 计算的实际可贡献异常行，含删除零项的精确恒等式；T3b 消费 T3a 与同一 N8a。源端 S6 的有限 carrier 修为原 Live ∧ class.Active。纯 RefinementAssembly 将真实 passive labels 与两 comparison bits 恰计一次，以 base sigmaCombine 聚合为同一 NormalizedData；ProfileAssembly、KernelMassAssembly、LocalAssembly 显式消费输入证明，未导入任何 Tasks。

N8 拆分前后预算分别为 63,000–89,500 与 65,000–92,500；公共蓝图及组装需控制在约7k行内，接近总上限的风险已在 PR 公开。规范化后半陈述和最终全链组装仍未完成，不把这些局部已实现的包装当成最终 conditional assembly。
