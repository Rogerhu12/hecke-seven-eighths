# MOM_ENGINE_STEP_V2：论文步骤蓝图

## 生效要求

按任务文件 2026-11-02 18:20 的“方向调整”及 PR #31 [协调评论](https://github.com/Rogerhu12/hecke-seven-eighths/pull/31#issuecomment-6574713757)，第一阶段改为**必要中间陈述、完整组装证明、逐陈述任务清单**。原目标仍是：

```lean
EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c
```

不修改 base 的定义、原量词、mesh 或 supported-volume 假设。各证明任务的主体暂用 `sorry`；组装模块显式接收这些任务的证明，不能使用 `sorry`，也不能导入已占位的任务定理。

## 当前批次：真实输入、候选任务陈述及完整组装辅助

当前提交仍在固定蓝图接口，尚未登记完整蓝图里程碑。第一轮 CI 的 CallData 两个 namespace 错误已修正（原 localize/profile 构造位于 EngineInduction）。新增候选陈述只表达论文中间步骤；已存在的两个独立任务证明明确保留 sorry，完整组装辅助与数据不含占位。

| 文件 | 当前物理行 | 角色 |
|---|---:|---|
| `ArithmeticData` | 71 | 同一base arithmetic choice |
| `AssemblyCore` | 130 | Mellin strict family组装 |
| `BudgetAssembly` | 101 | 四terminal/同核mass数值组装 |
| `CallData` | 111 | 同一call及localization |
| `EmptyAssembly` | 41 | 真实空原rows的零输出 |
| `EstimateData` | 126 | 原profile、rank与明确数值资格 |
| `FirstCauchyContracts` | 224 | S2实际first Cauchy carrier/allowance |
| `FirstSourceContracts` | 137 | S1原first source与规范原子身份 |
| `InputDemands` | 93 | 明确orders/threshold的并集与max |
| `Interface` | 36 | 聚合入口，完整任务组装仍待接入 |
| `NormalizationAssembly` | 49 | base source_integral运输 |
| `NormalizedData` | 98 | 同一base normalized family与原核 |
| `OrdinaryData` | 94 | 原ordinary binding |
| `OriginalInput` | 45 | 原finite parent atoms |
| `OutputAssembly` | 102 | 同一family→原PairedEngineConclusion |
| `PassiveData` | 99 | 原residual-mask有限divisor/allocation carrier |
| `PreparedCall` | 117 | 原Mellin preprocessing |
| `PrimitiveAssembly` | 45 | 精确recursive invariant五项组装 |
| `ProfileDictionary` | 96 | 固定父representative及完整profile字典 |
| `ProfileFormula` | 111 | 全实数原profile变换公式 |
| `ProfileFormulaTask` | 21 | N5a统一profile公式估计（sorry） |
| `RawLeafData` | 214 | 原covered keys/allocations及真实full-correlation leaf |
| `RawRectangleData` | 70 | 原two-rectangle逐项公式 |
| `SourceData` | 219 | source数据、正loss/cutoff、空row分支 |
| `SourceFrame` | 140 | 原始量词与source request |
| `TasksUniform` | 28 | U1统一输入准备（sorry） |
| `UniformAssembly` | 76 | 原目标量词包装 |
| `UniformContracts` | 93 | 原输入准备的纯任务类型 |
| `UniformData` | 67 | uniform输入准备 |

以上数据及派生定义全部具体构造，不从新 admitted existence 中选择数据。尚未使用的原 `OriginalInput` 证明陈述也已移除。原始 source 的存在证书来自 base 的 node invariant；Mellin/localization 直接调用 base 已有构造。

旧 90 模块实现闭包中的 **86 个文件已从活动目录移除**；Literal/physical/selected 数值实现不进入蓝图。可通过 [旧 head 0b30d8e](https://github.com/Rogerhu12/hecke-seven-eighths/tree/0b30d8e371be1fe4028306e24c86fef3b3c5588f/HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2) 或 A 线历史查阅，不复制到新的 reference 编译目录。

## 下一批：固定任务陈述并证明组装

源端按论文步骤拆为：原始系数与第一变换、第一轮范数预算、一次 prime pool、第二完整相关式、宽度下降、两轮除子分配。规范化侧另行区分原子字典、被动 whole-product 分解、capacity/clipping、profile、同一 child invariant、同核 integrability/mass 与实际四终端。

每个任务先固定具体的 Lean 陈述及依赖，目标证明规模 3000–5000 行以内。统一 orders/constants/threshold 的证书必须先于移动输入；输入资格只能由明确数值与几何条件定义，不能用任意可为空的谓词代替。统一选择任务只构造输入数据与资格，不能把最终 child/output 当作前提。

纯数据及任务命题类型与占位任务证明分开。无占位组装模块只 import 纯类型和 base，显式取得每项任务证明后，逐层取得同一 source/leaf/child/kernel，最终构造原 `PairedStepHypothesis`。实例化这些任务的顶层入口另行记录其仍有 `sorryAx`，不把条件组装的三公理通过误报为最终目标已证明。

## 预算基准

原 19 模块草图预算 **57,620 行**；旧实现方案后来重估为 **76,920 行**，增加 **19,300 行**，尚未通过完整 CI。该实现方案已经停止，不再作为蓝图路线继续扩展。

本批 **29 模块、2,854 物理行**；除两个独立任务证明的显式 sorry 外，数据、纯命题类型及公共组装均已具体实现。这个数字是蓝图输入层体量，不是完整证明规模，也不是完成压缩的证据。完整蓝图会按每个任务列出预计证明行数、真实依赖、论文位置与 A 线参考，汇总后继续以 100,000 行为上限。未实现的通用化不提前计算节省。

## CI 与执行节奏

只用 GitHub CI 编译；每批完成即推送，等待该轮结果并读完日志才推下一批。专用 CI 精确 checkout head，验证 manifest 覆盖全部活动模块，并对 `proved` 组在 fresh Lean 中递归审计所有 V2 声明，只允许 `propext`、`Classical.choice`、`Quot.sound`。`g0` 只含真实数据、纯命题类型与完整组装辅助，并单独递归审计；`g1` 两个独立任务暂为显式 sorry；`g2` 聚合入口不计为最终任务组装完成。

全部任务陈述与完整无占位组装在同一 head 编通后，发布正式逐任务清单供协调员安排并行会话。PR 保持 [不合并] draft；最终原目标无占位、三公理与 integration gate 通过后才进入审查。

## 已固定的独立任务（清单尚未完整）

| 名字 | 文件 | 输入/依赖 | 论文行号 | 预计证明行数 | 参考 |
|---|---|---|---|---:|---|
| `Blueprint.Tasks.uniformPreparation` | `TasksUniform.lean` | 六个固定UniformCost families、具体demands；只产生原输入及funding | 3043–3073 | 2,500–4,000 | base StrictProfileOrder、MellinSourcePreparation、ActualEngineProfiles；A finite-rank uniform choices |
| `Blueprint.Tasks.profile_formula_control` | `ProfileFormulaTask.lean` | 固定global formula、positive support与dilation/power/phase bounds | 3043–3073 | 2,000–3,000 | base CanonicalLogProfiles；A原uniform log-profile calculus |

其他 source/normalization/terminal 陈述及完整 `pairedStepHypothesis_of_blueprint` 仍在接线与审核，不作为已可分发的最终任务清单。
