# MOM_ENGINE_STEP_V2：论文步骤蓝图

## 生效要求

按任务文件 2026-11-02 18:20 的“方向调整”及 PR #31 [协调评论](https://github.com/Rogerhu12/hecke-seven-eighths/pull/31#issuecomment-6574713757)，第一阶段改为**必要中间陈述、完整组装证明、逐陈述任务清单**。原目标仍是：

```lean
EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c
```

不修改 base 的定义、原量词、mesh 或 supported-volume 假设。各证明任务的主体暂用 `sorry`；组装模块显式接收这些任务的证明，不能使用 `sorry`，也不能导入已占位的任务定理。

## 第 1 批：只保留真实输入

当前提交是蓝图的输入层，不是已完成的蓝图里程碑。活动 Lean 文件仅为：

| 文件 | 实际行数 | 必要角色 |
|---|---:|---|
| `SourceFrame` | 140 | 原 annulus/reflection、schedule/bounds、原 recursive request |
| `OriginalInput` | 45 | base CompleteSourceData、原 NormProfileRecipe、原 finite parent atoms |
| `PreparedCall` | 117 | 原 Mellin preprocessing、同源 source/profile 运输及外 Mellin 成本 |
| `CallData` | 111 | 单次原输入及其 localization、domain、geometry 的实际派生 |
| `ArithmeticData` | 71 | 同一 target 的 base arithmetic choice、unit subgroup、Haar measures |
| `UniformData` | 67 | 原量词顺序下的 schedule/bounds/prepared 与外 Mellin budget |
| `EstimateData` | 126 | 固定 rank/annulus、真实原 RawProfileWindow、具体 orders/threshold 资格 |
| `SourceData` | 196 | 原 first/second source 数据、小正 loss/cutoff 的实际构造 |
| `RawLeafData` | 214 | base covered physical carrier、实际 allocation 与 full-correlation leaf |
| `NormalizedData` | 98 | 同一个 base normalized family、原两个 Fourier kernel、实际有限质量表达式 |
| `UniformContracts` | 93 | 纯 numerical funding 及 uniform preparation 命题类型，无占位定理 |
| `AssemblyCore` | 130 | 参数嵌入、exact universal child labels、Mellin strict family |
| `OutputAssembly` | 102 | 同一 normalized family 接入原 ofFintype 与 exact recursive admissibility |
| `NormalizationAssembly` | 49 | base source_integral 把同源预算运到同一 child/kernel |
| `BudgetAssembly` | 101 | 四 terminal 加总及算术/Fourier 两份质量的纯数值组装 |
| `UniformAssembly` | 76 | 显式 prepare/produce 下完整恢复原目标量词 |
| `Interface` | 24 | 活动模块聚合入口；完整论文任务入口随后接入 |

以上数据及派生定义全部具体构造，不从新 admitted existence 中选择数据。尚未使用的原 `OriginalInput` 证明陈述也已移除。原始 source 的存在证书来自 base 的 node invariant；Mellin/localization 直接调用 base 已有构造。

旧 90 模块实现闭包中的 **86 个文件已从活动目录移除**；Literal/physical/selected 数值实现不进入蓝图。可通过 [旧 head 0b30d8e](https://github.com/Rogerhu12/hecke-seven-eighths/tree/0b30d8e371be1fe4028306e24c86fef3b3c5588f/HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2) 或 A 线历史查阅，不复制到新的 reference 编译目录。

## 下一批：固定任务陈述并证明组装

源端按论文步骤拆为：原始系数与第一变换、第一轮范数预算、一次 prime pool、第二完整相关式、宽度下降、两轮除子分配。规范化侧另行区分原子字典、被动 whole-product 分解、capacity/clipping、profile、同一 child invariant、同核 integrability/mass 与实际四终端。

每个任务先固定具体的 Lean 陈述及依赖，目标证明规模 3000–5000 行以内。统一 orders/constants/threshold 的证书必须先于移动输入；输入资格只能由明确数值与几何条件定义，不能用任意可为空的谓词代替。统一选择任务只构造输入数据与资格，不能把最终 child/output 当作前提。

纯数据及任务命题类型与占位任务证明分开。无占位组装模块只 import 纯类型和 base，显式取得每项任务证明后，逐层取得同一 source/leaf/child/kernel，最终构造原 `PairedStepHypothesis`。实例化这些任务的顶层入口另行记录其仍有 `sorryAx`，不把条件组装的三公理通过误报为最终目标已证明。

## 预算基准

原 19 模块草图预算 **57,620 行**；旧实现方案后来重估为 **76,920 行**，增加 **19,300 行**，尚未通过完整 CI。该实现方案已经停止，不再作为蓝图路线继续扩展。

本批 **17 模块、1,760 物理行**，全部为真实输入、纯任务命题类型或已完成的公共组装。这个数字是蓝图输入层体量，不是完整证明规模，也不是完成压缩的证据。完整蓝图会按每个任务列出预计证明行数、真实依赖、论文位置与 A 线参考，汇总后继续以 100,000 行为上限。未实现的通用化不提前计算节省。

## CI 与执行节奏

只用 GitHub CI 编译；每批完成即推送，等待该轮结果并读完日志才推下一批。专用 CI 精确 checkout head，验证 manifest 覆盖全部活动模块，并对 `proved` 组在 fresh Lean 中递归审计所有 V2 声明，只允许 `propext`、`Classical.choice`、`Quot.sound`。本批全为无占位真实数据及公共组装，作为 `g0` 审计。

全部任务陈述与完整无占位组装在同一 head 编通后，发布正式逐任务清单供协调员安排并行会话。PR 保持 [不合并] draft；最终原目标无占位、三公理与 integration gate 通过后才进入审查。
