# LOW-REFLECTED-ENERGY：实现与验证报告

## 当前结论

**94 个新增 Lean 模块中，84 个当前源文件与已完成 round 11 的原生 Lake
`Built` 事件匹配；当前修复后的完整依赖图及两个最终目标仍未验证通过。**
这些是固定源码上下文中的真实编译观察。整次 Lake 构建以 exit 1 失败，
两个最终公理门均未启动，不能据此宣布任务完成。

最近完成并纳入证据的 [run 41194215379](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41194215379)
的 actual job 为 `124517149642`，实际 checkout 为
`0c47c707eeb3e05caa1934d3da6cf0f4d6e1ce52`，不是 GitHub PR 事件的 merge SHA。
本轮请求构建全部 94 个清单模块以及 `HeckeSkeleton.Principal`。
原生 Lake 进程运行 **760.616 秒**后以 **exit 1** 结束，没有触发进程墙钟超时。

| round 11 的实际观察 | 新增模块数 |
|---|---:|
| 真实 `Built` 事件（执行时的源码） | 84 |
| 失败构建事件（执行时的源码） | 2 |
| 没有终结构建事件 | 8 |

`Principal` 不在上述 94 个新增模块内，也没有完成构建事件。
84 个成功构建块包含 **319 项公开声明公理打印**，均在
`propext`、`Classical.choice`、`Quot.sound` 的允许集合内。
相比 round 9，四个新增成功构建模块如下：

| 本轮新增 `Built` 模块 | 公开声明公理打印数 |
|---|---:|
| `ActualSourceReindex` | 6 |
| `InactiveWindows` | 8 |
| `TargetDictionary` | 0 |
| `TargetSieveDictionary` | 3 |

`TargetSieveDictionary` 已实际编译通过，原来的 identifier/heartbeat 错误未重现。
共有七个成功模块没有打印公开声明报告：`ActualReflection`、
`ActualSymbolProducts`、`IdealMajorant`、`ActualHybridEntry`、`GaussianTheta`、
`TargetDictionary` 与 `LowFrozenCube.Valuations`；这里只记录它们的构建成功。
单个模块的打印不代替两个所需最终声明的严格审计。

本轮仅有 **两个失败模块、三条源码错误诊断**：
`ActualDyadicReflection` 在第 53 行缺少显式范数定义化简、第 162 行含多余 `rfl`；
`TargetGaussian` 在第 105 行对六次单位不变性进行 rewrite 时未匹配应用表达式。
当前已分别补充范数定义化简、移除多余 `rfl`，并用乘法的 `congrArg`
直接传递不变性等式。原数学陈述和假设保持不变，两个修复版本仍待下一轮 CI。
其源码 SHA-256 分别为：

- `ActualDyadicReflection`：`407d2c085691973553239577a74fb4c1ce87cdf25a0fb4202cff452afaa47370`。
- `TargetGaussian`：`8b083364b55a7ba8e8bed5fb0a0bc763ecaf140e4f64df86fce4c8ecf0119010`。

当前源码的匹配、修改和未完成事件分类见下方待验证更新；上述已归档运行结果保持不变。
完整日志未观察到旧依赖文件编译错误或 heartbeat 超时。
失败输出中的编译器占位 `sorryAx` 只保留为失败证据。
两项最终公理门均为 **`not_started`**；没有最终审计文件或完整构建后的输出清单。

工作分支 `codex/low-reflected-energy-ade19eee` 已纳入
`dtests-handoff` 的 `e66f7384bc08d1124d1a9a4e7dcc21e4facffab0` 基线，
包括 MOM_BASE 与 THETA_GLOBAL 的新构造。合并检查点为
`7629f9852b725d5f0f93ec47fb39796585bd5c16`，父提交分别是
原能量 head `9f5c25feee565ba605034fb6a80ede4b21cd7c4f` 与该上游基线。
干净合并保留全部 94 个任务模块源码；两项能量终点仍保留固定 `F` 和两个原筛输入。
上游 `Base`、`Theta` 和库配置已变化，因此旧上下文的 Built 观察只说明对应源文件曾编译，
不能验证当前合并后的完整依赖图。此前 66 个旧文件的 import 恢复记录继续作为历史保存。
本报告所归档 actual 使用固定官方缓存与原生 Lake，构建前检查没有恢复的 `HeckeSkeleton` 输出。
后续源码修复与新上游构造不属于该历史 checkout 的执行证据范围。

逐模块状态见 [VERIFICATION_LEDGER.md](VERIFICATION_LEDGER.md)，
当前源码哈希与完整历史见 [source_manifest.json](source_manifest.json)。
本轮证据集中于 [native_lake_round11.json](native_lake_round11.json) 与
[原始验证 ZIP](evidence/native_lake_round11.zip)。
此前的 [round 9 原生记录](native_lake_round9.json)、[原始 ZIP](evidence/native_lake_round9.zip)，
以及 [aggregate_evidence.json](aggregate_evidence.json) 内五个历史逐模块阶段全部保留。
历史 **786 个直接成功记录**和 **1,794 个旧配置原生依赖验证**不与本轮 84 个
新增模块相加，也不授权当前修复版本或最终目标通过。

<!-- pending-source-refresh:status:start -->
### 当前源码待验证分类

已归档批次仍记录 84/94 个 Built 观察；当前源码匹配数为 84/94，已修改待验证 6 个，源码匹配但无终结事件 4 个。后续诊断不增加已完成构建数；当前完整依赖图和最终目标仍未验证。
<!-- pending-source-refresh:status:end -->

**Pending source update — 2026-10-31T11:31:07.249463+00:00** (run 41196034806; job 124522578454; source_head 2850c225f246ebf9d535ef0bf1031debd8fe360a).

`ActualAnnularBlockEnergy`, `ActualFrozenAggregation`: current hashes updated; repairs await compilation. This note is diagnostic context only, with no completed-run or final-audit claim.

> Round 12 partial diagnostics belong to exact checkout 2850c225f246ebf9d535ef0bf1031debd8fe360a, run 41196034806, actual job 124522578454. ActualDyadicReflection has a fresh Built event (3.8 seconds); this is a partial observation, not a completed batch or final audit result.
> 
> ActualAnnularBlockEnergy reported errors at the executed source's lines 370 and 399: positivity could not infer the sign of the opaque exterior norm, and Finset.tsum_subtype could not infer the intended function through the local Row/G aliases. The repair explicitly supplies the nonnegative factors and the complete ideal-to-real function.
> 
> The identical opaque exterior-norm factors in ActualFrozenAggregation's hE and hcard proofs are also replaced with explicit Real.rpow_nonneg arguments. This is a preventive repair of the same proof pattern, not a claimed compiler failure in that module.
> 
> Statements, hypotheses, coefficients, cutoffs and constants are unchanged. These repairs still require compilation. The latest archived complete native evidence remains round 11; both final target audits remain unverified.

**Pending source update — 2026-10-31T13:30:16.139166+00:00** (run 41204593530; job 124547337675; source_head 9f5c25feee565ba605034fb6a80ede4b21cd7c4f).

`ActualFrozenAggregation`, `ActualTupleReconstruction`: current hashes updated; repairs await compilation. This note is diagnostic context only, with no completed-run or final-audit claim.

> Round 13 partial diagnostics belong to exact checkout 9f5c25feee565ba605034fb6a80ede4b21cd7c4f, run 41204593530, actual job 124547337675. ActualAnnularBlockEnergy has a fresh Built event (7.9 seconds); this is a partial observation, not a completed batch or final audit result.
> 
> ActualFrozenAggregation reported an unavailable tsum_eq_zero identifier (and a no-goals consequence) plus a finite-sum normalization mismatch at the executed source's lines 87, 88 and 207. The zero-row proof now uses a typed pointwise zero identity and tsum_zero. The energy proof explicitly unfolds its local Classes alias before the unchanged product-sum/cardinality normalization.
> 
> ActualTupleReconstruction contained two further calls to the same unavailable identifier. Its zero-row proof now directly simplifies the already established coprimality-zero atom and tsum_zero. This is a preventive same-pattern repair, not an observed compiler failure in that module.
> 
> Statements, hypotheses, coefficients, cutoffs and constants are unchanged. Both repairs await compilation in the newly integrated e66f7384 dependency context. The latest archived complete native evidence remains round 11; both final energy audits remain unverified.

**Pending source update — 2026-10-31T13:45:00.313727+00:00** (run 41205984586; job 124551256989; source_head d6f5ce52bc4aee5578233b779871412ff027f1bd).

`ActualFrozenReconstruction`, `ActualTupleReconstruction`: current hashes updated; repairs await compilation. This note is diagnostic context only, with no completed-run or final-audit claim.

> Round 14 partial diagnostics belong to exact checkout d6f5ce52bc4aee5578233b779871412ff027f1bd, run 41205984586, actual job 124551256989. ActualAnnularBlockEnergy and ActualFrozenAggregation have fresh Built events (8.6 and 5.0 seconds). These partial observations do not certify the completed batch or final energy audits.
> 
> ActualFrozenReconstruction reached the default 200000-heartbeat limit while elaborating the hB summability transport at executed line 106. The missing theorem reported at line 190 is downstream fallout. The repair cancels the known nonzero inactive weight with its inverse through a bounded simp-only list, avoiding higher-order congruence elaboration and leaving annularDualRow opaque. The heartbeat limit is unchanged.
> 
> ActualTupleReconstruction also receives three localized rw-to-erw changes where ordinary actualMarkedDatum record fields must reduce to the empty puncture and M.image t. This is a preventive application of the previously confirmed dependent-field rewrite pattern, not an observed compiler failure in that module.
> 
> All statements, hypotheses, factors, cutoffs and constant quantifiers are unchanged. These repaired source versions await native compilation. The latest archived complete native evidence remains round 11, and both final energy audits remain unverified.

## 目标、假设与调用方

目标的行、截断、标记权重与六次单位商均沿用原定义。结论仍为：
对每个 `B > 0` 和 `ε > 0`，存在先于 `Z`、窗口中的 `p` 与 `J` 选定的
`C > 0` 与 `Z₀ ≥ 1`，使原始轨道能量不超过
`C * Z ^ (5/6 + ε) / q ^ 2`，其中 `q` 是原选中素理想乘积的范数。
未把 surviving marks 的求和提前移到范数平方之外。

公开目标显式取三个输入：

1. 原 `MarkedCoefficientReflectionInput`，包括实际系数反射、其绝对收敛性及有限 Mellin 核数据。
2. 原 `HeckeSkeleton.QuadraticSieveBound K c`。
3. 原 `HeckeSkeleton.CubicSieveBound K c`。

添加两个 sieve 参数是任务明确允许的陈述修正。`TargetSieveDictionary` 中的
两个 `Iff.rfl` 给出它们与实际 exterior-kernel 输入的定义相等，未加强假设。
`principalSource` 的调用已提供 `moment_quadratic_sieve` 和 `moment_cubic_sieve`。
最终目标没有额外的 completed-energy、分离块能量、行主项界或等价分析结论假设。
数值模块可以有明确的几何不等式前提；实际适配层负责从真实范数、窗口和截断证明这些前提。

`Principal.completedMarkedEnergy` 的有限 Mellin 数据改为隐式参数
`{F : FiniteMellinData K S}`，可由 `hreflection` 的类型自动推断。
这是对原数据参数的泛化，能量结论及其窗口和轨道定义不变。
常数可依赖固定的 `F` 及其反射/核数据；未声称同一个常数对所有 `F` 统一。
这样条件能量定理独立于特定 `finiteMellinData` 提供者的实现。此前归档快照中的该提供者
尚未实现；新上游 `Theta.lean` 已给出 `FiniteSkeletonSource.data K c (localHighKMellinInput K c)`
的构造。原 `principalSource` 仍显式取 `(F := finiteMellinData K c)`，保留原流程。
合并后的上游构造与完整调用链仍须由真实编译和公理检查确认，不能由源码存在推断已经通过。

固定版本 Lean 的[公理收集器](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Util/CollectAxioms.lean)
会递归检查声明类型及证明项；未实现的数据即使只出现在参数类型中，也不能避开公理审计。
固定 `F` 的处理明确了条件定理的范围，最终实际公理门仍不可省略。

主要公开定理的逐字签名与环境见 [THEOREMS.md](THEOREMS.md)。
每个辅助定义及全部证明项保存在相应 `.lean` 文件中。

## 从真实定义到目标的连接

| 层 | 主要模块 | 实际职责 |
|---|---|---|
| 符号与原始筛 | `ActualSymbols`, `ActualSieveDictionary`, `ActualRawHybrid` | 实际六次符号的二次/三次幂、碰撞零点、互反律与两个原筛 |
| 原始混合行 | `RawIdealHybrid`, `HybridScaling`, `MellinHybrid` | 保留原平方自由行和两道互素掩码；保持系数对移动行及活动标记的独立性 |
| 冻结局部因子 | `ActualLocalWeylTable`, `ActualFrozenCharges`, `ActualFrozenStateCount` | 真实局部表、minimum/cube 分解、范数代价和状态数的小幂界 |
| 物理尺度 | `ActualSeparatedBlock`, `ActualBlockEnergy`, `PhysicalBlockPolynomial` | 从真实反射项得到 Mellin 块及其完整四尺度多项式 |
| 高斯与双重 dyad | `ActualAnnularBlockEnergy`, `PhysicalGaussianEnergy`, `ActualFrozenAggregation` | 所有环带和全部双列范围；绝对收敛、有限 Hilbert 能量及统一常数 |
| 原 marked row | `ActualFrozenReconstruction`, `ActualMarkedTupleEnergy`, `ActualTupleReconstruction` | 真实窗口、共轭 Hecke 权重、活动/不活动标记和 literal row 的精确重构 |
| 完整理想行 | `ActualResidualDyadicEnergy`, `ActualCompleteIdealEnergy` | 固定 powerful part 上的残差行单射、原能量分割、Rankin 质量及精确 q⁻² |
| 原轨道目标 | `ActualCompletedMarkedEnergy`, `Principal` | 有限理想范数球乘所有六次单位扇区，精确还原原轨道 tsum |

关键代价和量词如下。

- 原始混合能量的四尺度界为 `(K*N*B*L)^ε (K+N*B) B (N+L+(N*L)^(2/3))`。
  模块对所有有限支撑及允许系数统一选常数，保留两道掩码与产品纤维重数。
- 物理核尺度包含不活动标记范数，并只在实际标记尺度处消去一个活动范数。
  未把真实行替换成另一个商行，也未丢弃非平凡单位扇区。
- 冻结系数留下 `N(f)^(-1/2)`。状态数平方用任意小幂 `N(f)^ρ` 支付。
  随后调用真实 powerful-ideal 的半范数质量估计，没有再乘一次 powerful 行数。
- 无界双列尺度上的 sieve 小幂在尾部不等式中支付；不能把这些长度预先当作 `Z` 的固定小幂。
  Gaussian 环带保留原窗口尺度，环带平移只改变物理核尺度。
- 活动标记范数所在的 dyad 数至多 `slots + 1`，其代价为固定常数；
  不活动标记用真实逆素范数加权的 L1 质量平方；所有相位仍在原行中。
- 残差行 dyad 互不相交，因此外层求和是能量求和。
  原截断在 `Z ≥ max(2,B)` 下落在 `N(I) ≤ Z²`，无需改变原截断。
- 最后用 `Z^d ≤ q ≤ 2^slots * Z^d`，其中 `d = |J|/(6*slots)`，恢复原 `q⁻²`。
  空选中集和单位理想由同一公式覆盖。

实际最外层分配 `δ = min(1, ε/100)`、`ε_inner = ε/100`、
`ε_outer = ε/2`、`ρ = ε/24`，从而
`23δ + 2ε_inner + ε_outer ≤ 3ε/4 ≤ ε`。
这是不同模块损失的总预算；每个模块不会各自耗用一整份最终 `ε`。

## 编译、审计与复现

固定环境为 Lean `4.35.0-rc3` 与 Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`。
每次原生批次的源码、配置、日志与进程结果单独保存，
不把旧汇总重新标成新运行结果，不从 `Built` 文本伪造逐模块退出码或 schema-2 receipt。

| 已纳入阶段 | run / job | 验证 artifact | 结果范围 |
|---|---|---|---|
| actual 历史记录 | `41167618537` / `124438820042` | `13030181239` | 534 个直接成功记录 |
| core 历史记录 | `41169613835` / `124444524127` | `13030830729` | 66 个源模块均为精确缓存成功 |
| actual 历史记录 | `41169613835` / `124444524100` | `13030109450` | 575 个直接成功、1,794 个原生依赖复用 |
| actual 历史记录 | `41171430364` / `124450025149` | `13031561006` | 634 个直接成功、1,794 个原生依赖复用 |
| actual 历史记录 | `41188282678` / `124499578347` | `13038675514` | 786 个直接成功、1,794 个原生依赖复用；最终门未运行 |
| 原生 actual，round 9 | `41191387620` / `124509013422` | `13039132601` | 80 个新增模块 Built、4 个失败、10 个无终结事件；exit 1，最终门未启动 |
| 最新原生 actual，round 11 | `41194215379` / `124517149642` | `13040671465` | 84 个新增模块 Built、2 个失败、8 个无终结事件；exit 1，最终门未启动 |

最新原生验证 ZIP 大小为 **205,075 字节**，SHA-256 为
`f14065da37fc7ae0b515b34491e73644276af7e215e8e9c6bde75d5b96d70d14`，
按原字节保存于 [evidence/native_lake_round11.zip](evidence/native_lake_round11.zip)。
原生 `lake-build.log` 的 SHA-256 为
`194df97130b4ba8f4b604cd2f36361afb886e75704597a89764be0f7cc41b702`；
完整 GitHub job 日志 SHA-256 为
`b52e895dd19ce4bb0167cbbf9b1fe3e7833db88161c78bce1237d806869ef3c1`。
源码预检使用的清单 SHA-256 为
`879614299412b9182f5e44adf3b7f17d9cac211c2af44ccd800584f12fd53a7d`。
全部 94 个预检源码哈希与该精确 head 的保存清单一致，
预检与最终失败报告中的源码和配置快照一致，实际命令含全部 95 个构建目标。
当前文件核对确认 84 个成功构建模块的源码哈希仍匹配；
生产入口的 `source_snapshot` 再次检查了全部 94 个当前文件哈希及新增源码 admission 限制。
后一个检查是源码一致性检查，不是 Lean 编译或证明证据。

ZIP 保存五个原始文件：`SHA256SUMS`、`lake-cache-manifest.json`、
`lake-build.log`、`prepared.json`、`report.json`。
独立 JSON 保留原始 preparation/report、所有成员文件哈希、
84 个成功及两个失败模块的完整编译输出块与打印报告。
便于阅读的输出块只去除 ANSI 转义并统一换行，原始日志仍在精确 ZIP 内。
本轮真实进程退出码是 1，没有单独逐模块进程退出记录，
也没有未执行的最终审计或未生成的完整输出清单。

此前 423 组新增模块原始记录与完整输出仍分布于五个历史阶段，保持不变；
这些组跨阶段重复同一模块，不能视为不同证明的数量。
round 9 原生 JSON/ZIP 也原样保留，aggregate 只追加不同运行的原生引用。
历史 round 8 的 786 个直接成功记录由 634 个精确缓存和 152 个新编译组成。
历史结果只适用于其实际 checkout 和依赖上下文，不验证当前修复后的完整目标。
被取消的 round 10 只保留取消状态及未返回的原生 checkpoint，未加入成功计数。

历史原生记录采用独立的 `native-lake-foundation-v1` 来源，
保留原 foundation run、artifact/catalog 哈希及
Lake `--rehash --no-cache --no-build` 验证日志。
round 8 的 receipt 与 round 7 字节相同，SHA-256 为
`8068f22f97aa984f78412e459dbe8fc2e163ef8a0ce598a347e01bde85fb95a0`。
其 1,794 个旧依赖只在 receipt 记录的源码、配置、输出和依赖哈希上下文内有效；
基线合并已改变 `lakefile.toml`，旧 receipt 不构成新配置的验收。
它们不用于新增模块或 `Principal`，也没有进入新的 actual 成功判定。
本文档审计只下载小型验证 ZIP；没有下载或重新哈希大型编译缓存。

本轮 actual 路径固定使用官方
[`lake-cache-76c696e`](https://github.com/Rogerhu12/hecke-seven-eighths/releases/tag/lake-cache-76c696e)
发布，源提交为 `76c696e20ee1f201a6507dde8b1d832a928ac71a`。
缓存 manifest 排除 `HeckeSkeleton`、`ThetaGlobal`、
`DedekindZetaChallenge`、`DedekindZetaSolution`，并列明三个跳过的 stale 模块。
原生验证记录检查了固定 cache metadata 哈希及构建前为空的证明输出目录。
发布 manifest 的模块数不是本次目标的通过数，恢复的 `HeckeSkeleton` 输出不能供给本轮证明。
完整 build 成功后仍必须审计
`ActualCompletedMarkedEnergy.completedMarkedEnergy` 与
`HeckeSkeleton.completedMarkedEnergy`：
编译成功退出、所需声明实际打印、所有打印公理均属于标准三公理集合。
round 11 未到达这两项审计。

复现时使用仓库固定的 toolchain、`lake-manifest.json` 和基线配置，
按 [workflow](../../.github/workflows/low-energy-verify.yml)
固定的 manifest/part 哈希恢复官方缓存，再执行原生 Lake 构建与最终审计。
core 的既有源码验证命令为：

```sh
python3 scripts/low_energy_verify.py core
```

actual 入口在工具链及缓存恢复前检查精确 checkout 并保存源码快照；
固定 restore action 完成后构建和审计：

```sh
python3 scripts/low_energy_lake_verify.py prepare \
  --expected-head "$EXPECTED_SOURCE_HEAD"
# 按 workflow 恢复固定官方缓存及其原始 manifest/SHA256SUMS。
python3 scripts/low_energy_lake_verify.py verify \
  --expected-head "$EXPECTED_SOURCE_HEAD" \
  --cache-metadata-dir "$RUNNER_TEMP/lake-cache-download"
```

`EXPECTED_SOURCE_HEAD` 为 workflow 选定的精确 PR head；本地复现需提供同一提交
及缓存 metadata 目录。本轮入口要求全部新增模块和 `Principal` 通过原生 Lake 构建，
再用固定隐式参数选项执行两项所需声明的公理审计。
来源、原始日志和成功条件独立于旧逐模块调度器保存。

旧的 `python3 scripts/low_energy_verify.py actual` 调度器及
`--diagnostic-seconds 600` 属于本文保留的历史分模块运行。
它在启动时重置阶段汇总；只有来源完全匹配的精确缓存和已验证原生依赖
可在诊断截止后保留，未验证的编译任务明确跳过。
正在运行、被中断或未返回的任务都不算通过。

同一 round 9 的 core job `124509013480` 成功：66 个精确缓存记录、
209 项允许公理打印，118 个 Python 回归测试通过。
Python fixture 覆盖解析、缓存调度、原生 receipt、导入器和 Lake 入口边界，
不构成 Lean 证明证据，也不代替实际最终门。测试命令为：

```sh
python3 -B -m unittest discover -s tests -p 'test_low_energy_*.py'
```

## 仓库依赖、上游缺口与剩余验收

本工作使用 `Rogerhu12/hecke-seven-eighths` 的真实定义和依赖。
ZIP 未包含的 `ClassFieldTheory`、`FLTReuse`、`TauCetiReuse`、`OAI`、
`SkeletonInputs`、`GramCoreInputs`、`GramAssemblyInputs` 等源码已按真实仓库接入。
[source_manifest.json](source_manifest.json) 的 `base_commit` 保留初始开发基线作为历史；
本次合并基线及最近完成验证的源码快照列在本报告开头。
当前修复提交以 PR 中的链接为准。

在先前 `5f3c782680be2c74365b4d8e5760fc16f1f222c5` 基线上，66 个已有文件曾恢复为
精确上游 imports；当时所有非 import 字节，包括定义、证明体及注释，
由机械比较确认未改动。该结论限于当时的恢复操作；当前接受新基线的相应源码变化。
完整历史导入调整、比较结果及恢复哈希保留于
[IMPORT_RESTORATION_20261031.json](IMPORT_RESTORATION_20261031.json)；
[vendor_import_changes.json](vendor_import_changes.json) 现为空列表，表示没有保留这些旧文件的导入改动。
原 `FLTReuse.ExplicitMathlibImports` helper 在全部 54 个消费者恢复后已无用途，已删除。
该恢复是依赖和缓存兼容性修复，不是数学证明改动；
恢复后的完整构建仍须取得真实结果。

较早归档快照中的 `finiteMellinData`、`finite_valuation_cutoff`、
`finite_valuation_decay`、`marked_reflected_absolute` 和 `marked_reflection`
包含上游 admissions。当前 `e66f7384` 基线已为这五项提供构造和证明体；
它们在合并后依赖图中的编译及递归公理状态仍须实际检查。
本任务的条件能量定理取给定反射输入，保留固定 `F` 的接口。
两项最终能量公理门只审计条件目标本身，不能据此宣称全局 `principalSource` 已无 admissions。

新增证明文件未加入 `sorry`、`axiom`、`admit` 或 `native_decide`。
已有 admissions 不能作为本次目标获证的依据；编译错误产生的占位项或
`sorryAx` 输出也不算成功证据。除显式列出原两个 sieve 输入并泛化 Mellin 数据参数外，
目前未确认原目标数学陈述存在反例或错误。

剩余验收是固定环境下合并后的完整实际适配链、
`ActualCompletedMarkedEnergy.completedMarkedEnergy` 及
`HeckeSkeleton.completedMarkedEnergy` 的编译和实际 `#print axioms` 审计。
必须检查是否经由任何既有 admission 引入 `sorryAx`。
在此之前，不把源码中的 `by` 块、缓存恢复或上传成功作为目标通过；
任务不能宣布完成，PR 不应标为 ready。

AI-assisted development；本报告的证明结论限于所保存的实际 Lean 记录。
