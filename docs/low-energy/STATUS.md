# LOW-REFLECTED-ENERGY：实现与验证报告

## 当前结论

**94 个新增 Lean 模块中，76 个有与当前源文件 SHA-256 匹配的直接成功证据；
完整实际适配链及最终目标仍未验证通过。** 原始
`HeckeSkeleton.completedMarkedEnergy` 已在源码中接入证明链，
但最终目标公理门尚未运行，不能据此宣布任务完成。

最近完成并纳入证据的 [run 41171430364](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41171430364)
的 actual 阶段有 **634 个直接成功记录**（575 个精确缓存、59 个新编译），
另有 **1,794 个原生 Lake 旧依赖复用记录**。两类记录分别保存；
原生依赖复用不计为新增证明模块通过。结合已保存的 core 证据并按模块去重，
当前 94 个新增模块的分类为：

| 当前源码证据 | 模块数 |
|---|---:|
| 最近选用的成功证据为精确缓存 | 73 |
| 最近选用的成功证据为新编译 | 3 |
| 已修改，旧失败记录不验证当前源码 | 2 |
| 最新实际阶段跳过，尚无当前源码成功证据 | 16 |

本轮新增通过的是 `ActualReflectionReindex`、`ActualFrozenCharges`、
`ActualHybridEntry`。前两者分别打印八项、三项公开公理报告，
均只含 `propext`、`Classical.choice`、`Quot.sound`；
`ActualHybridEntry` 有真实编译成功记录，但没有打印公开定理公理，
因此这里只记录编译成功。

该次 actual 阶段记录 **六个编译错误、一个诊断预算中断、1,123 个跳过模块**
（969 个受依赖阻塞、154 个因预算耗尽），最终公理门未运行。
`IntegralCompletionTrace` 的预算中断没有形成证明结果。
`ActualSeparatedBlock` 与 `ActualFrozenStateCount` 的四项 `sorryAx` 输出
属于失败编译，未计为成功公理证据。

当前已按原陈述修复上述两个证明模块；其余四个失败的已有依赖
`PrimitiveCharactersByCRT`、`NormSeries`、`TraceNormalization`、
`CompactCoordinateAnnihilators` 只补入官方 imports，旧证明体保持不变。
当前 workflow 的依赖构建列表也已补齐对应 leaf 模块。
**这两项证明修复和四项导入修复仍等待下一轮 CI，未记为通过。**

最近完成验证运行所用的源提交是 `58986fd9264c59427e71268b1c5e00eb1a2e5964`。
工作分支为 `codex/low-reflected-energy-ade19eee`，
已通过 `fe8d84e5` 合并 `dtests-handoff` 的 `182769d4` 基线。
随后上游基线推进到 `a217322c47d13ea08c02d50eaa270e2b7ca09852`；
这批后续基线改动不在 round 7 的证据覆盖范围内，其依赖和配置仍须重新验证。
当前修复提交将由 PR 链接标识，尚未取得新的完整目标验证结果。

逐模块当前状态见 [VERIFICATION_LEDGER.md](VERIFICATION_LEDGER.md)，
当前源码哈希、历史记录与失效说明见 [source_manifest.json](source_manifest.json)，
原始记录及完整公开公理输出集中于 [aggregate_evidence.json](aggregate_evidence.json)。

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
这样条件能量定理不必实例化原 `Theta.lean` 中尚未实现的 `finiteMellinData` 定义。
原 `principalSource` 仍显式取 `(F := finiteMellinData K c)`；这保留原流程，
不把上游数据构造的缺口包装为本次已经完成的证明。

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
本次证据以以下已完成运行及其真实 job 日志为依据；历史原始记录与引用继续保留，
不把恢复的旧汇总重新标成新运行结果。

| 已纳入阶段 | run / job | 验证 artifact | 结果范围 |
|---|---|---|---|
| actual 历史记录 | `41167618537` / `124438820042` | `13030181239` | 534 个直接成功记录 |
| core | `41169613835` / `124444524127` | `13030830729` | 66 个真实源模块均为精确缓存成功 |
| actual 历史记录 | `41169613835` / `124444524100` | `13030109450` | 575 个直接成功、1,794 个原生依赖复用 |
| 最新 actual | `41171430364` / `124450025149` | `13031561006` | 634 个直接成功、1,794 个原生依赖复用；最终门未运行 |

最新 actual 的实际 checkout merge 为
`9cc743c032a2424252e64aa8c8933e505387d446`；
验证 ZIP 大小为 10,430,603 字节，SHA-256 为
`40e64075404b4c76e4e3ed66ec3d730a617c03c2f2a724545d2e27eaf4dd137a`。
每个已执行模块均与该次 job 日志中的实际执行事件对应。
完整来源、日志哈希、编译选项与依赖指纹保存在 aggregate 中。

本快照核对了最新 actual 的全部 634 个直接成功源文件、1,794 个原生依赖源文件、
1,764 个非原生模块日志和 7,349 条依赖指纹边；没有记录一致性错误。
六个失败模块已修复，当前源码哈希与该次失败记录不同；旧失败输出作为历史保留，
不替代当前修复的验收。331 组新增模块原始记录与完整输出保留于四个已纳入阶段，
这些组会跨阶段重复同一模块，不能当作互不重复的证明数。
源文件成功证据只适用于记录中的上下文；单个模块或一般核心通过并不验证完整目标。

原生记录使用独立的 `native-lake-foundation-v1` 来源，保留原 foundation run、
artifact 哈希、catalog 哈希与 Lake `--rehash --no-cache --no-build` 验证日志。
本轮复用的 receipt 与前一轮字节相同；验证器核对当前源码、配置、输出及依赖哈希，
不会把继承的 receipt 重新标成此次新编译或新增公开定理公理审计。
它不用于新增模块或 `Principal`。本次文档审计只下载并核对小型验证 ZIP，
没有下载或重新哈希大型编译缓存；原始编译 artifact 的哈希保留为来源记录。

复现时先安装仓库锁定的 Lake 依赖和匹配的 Mathlib cache；
actual 阶段还需构建当前
[workflow](../../.github/workflows/low-energy-verify.yml)
列出的官方 Mathlib leaf 模块与固定的 TauCeti `PrimeIdealTheorem`。
随后运行：

```sh
python3 scripts/low_energy_verify.py core
python3 scripts/low_energy_verify.py actual
```

CI 为 actual 的失败后诊断设置 `--diagnostic-seconds 600`；
需要相同诊断范围时使用该选项。可选的旧依赖复用由
`python3 scripts/low_energy_native_foundation.py actual` 执行；
只有真实 Lake 验证通过且来源、当前源码、配置和依赖哈希全部匹配时才可使用。
精确缓存与已验证原生依赖可在诊断截止后保留，未验证的编译任务会明确跳过。
启动阶段清空阶段汇总，避免把恢复的旧 aggregate 误记为新运行的执行结果。

验证器按真实依赖顺序编译，使用仓库的隐式参数选项与单 Lean 进程，
记录源码哈希、完整编译输出和公理清单；CI 分别保留 core 与 actual artifacts。
修改源码后必须重新取得匹配记录。正在运行、被中断或未返回的任务都不算通过。

106 个 Python 回归测试已通过，覆盖解析、缓存调度、原生 receipt 与导入器边界；
测试中的模拟编译记录不是 Lean 证明证据。可用以下命令复现测试：

```sh
python3 -B -m unittest discover -s tests -p 'test_low_energy_*.py'
```

## 仓库依赖、上游缺口与剩余验收

本工作使用 `Rogerhu12/hecke-seven-eighths` 的真实定义和依赖。
ZIP 未包含的 `ClassFieldTheory`、`FLTReuse`、`TauCetiReuse`、`OAI`、
`SkeletonInputs`、`GramCoreInputs`、`GramAssemblyInputs` 等源码已按真实仓库接入。
[source_manifest.json](source_manifest.json) 的 `base_commit` 保留初始开发基线作为历史；
已合并基线及最近完成验证的源码快照列在本报告开头；当前修复提交以 PR 中的链接为准。

66 个已有文件的调整仅涉及 imports，旧定义和证明体保持不变；
原始/当前哈希与补入的真实依赖见
[vendor_import_changes.json](vendor_import_changes.json)。
导入收窄和补齐仍须经过完整依赖编译，不能靠新增公理填补缺失接口。

确认的上游缺口是 `HeckeSkeleton/Theta.lean` 中标记为 `TH-KP-DATA` 的
`finiteMellinData` 仍为 admitted 定义。`finite_valuation_cutoff`、
`finite_valuation_decay`、`marked_reflected_absolute`、`marked_reflection`
也保留原 admissions。本任务的条件能量定理取给定反射输入，不调用这些未证提供者；
全局 `principalSource` 仍依赖它们。最终公理门审计条件目标本身，
不能据此宣称全局 principal source 已无 admissions。

新增证明文件未加入 `sorry`、`axiom`、`admit` 或 `native_decide`。
已有 admissions 不能作为本次目标获证的依据；编译错误产生的占位项或
`sorryAx` 输出也不算成功证据。除显式列出原两个 sieve 输入并泛化 Mellin 数据参数外，
目前未确认原目标数学陈述存在反例或错误。

剩余验收是固定环境下完整实际适配链、
`ActualCompletedMarkedEnergy.completedMarkedEnergy` 及
`HeckeSkeleton.completedMarkedEnergy` 的编译和实际 `#print axioms` 审计。
必须检查是否经由任何既有 admission 引入 `sorryAx`。
在此之前，不把源码中的 `by` 块或缓存上传成功作为目标通过，
任务不能宣布完成，PR 不应标为 ready。

AI-assisted development；本报告的证明结论限于所保存的实际 Lean 记录。
