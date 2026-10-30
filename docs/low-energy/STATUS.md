# LOW-REFLECTED-ENERGY：实现与验证报告

本分支直接以 `Rogerhu12/hecke-seven-eighths` 的真实定义为基础。
基线是 `dtests-handoff` 的 `503ad9895e5f8affef55b22fea082e251bf33aa7`，
工作分支是 `codex/low-reflected-energy-ade19eee`。

## 当前结论

原始目标 `HeckeSkeleton.completedMarkedEnergy` 已在源码中接到完整证明链；
`Principal.lean` 的这一个 `sorry` 已由对新端点定理的调用替换。
**源码连接完成不等于 Lean 已验证目标。当前新端点及完整实际适配链尚未通过完整编译，
本 PR 保持草稿状态，不能据此宣布 LOW-REFLECTED-ENERGY 已经形式化完成。**

当前清单包含 94 个新增 Lean 模块，
其中 55 个有与当前源文件 SHA-256 匹配的成功编译记录，
另 39 个没有。记录按模块区分；成功验证一个一般核心不被当作
已经验证实际适配层。运行中的任务、资源中断和未返回的编译均不算通过。

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

固定环境：Lean `4.35.0-rc3`，Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`。
`source_manifest.json` 保存当前文件哈希、模块状态及已执行的公开定理公理输出。
[VERIFICATION_LEDGER.md](VERIFICATION_LEDGER.md) 是便于人工检查的模块清单。
已核对的纯核心公开定理审计只出现 `propext`、`Classical.choice`、`Quot.sound`。
这不是未编译实际端点的公理审计结果。

安装仓库固定 Lake 依赖及对应 Mathlib cache 后运行：

```sh
python3 scripts/low_energy_verify.py core
python3 scripts/low_energy_verify.py actual
```

脚本按真实依赖顺序编译、使用仓库的隐式参数选项、记录源码哈希和原始编译输出。
GitHub Actions 分别运行 core 与 actual。日志作为 workflow artifacts 保存。
任何源文件编译错误必须修复后重跑；不能把 CI 已排队或已启动记成 PASS。
本地采用单 Lean 进程，减少共享环境内存压力；资源限制不被解释成定理成立或不成立。

新增证明文件未加入 `sorry`、`axiom`、`admit` 或 `native_decide`。
仓库已有其他任务的 admissions 保持原状，它们不代表本次新目标已经获证。
目标的最终 `#print axioms` 仍必须实际运行，检查是否经由任何既有 admission 引入 `sorryAx`。

## 仓库依赖与范围

ZIP 未包含的真实依赖已从所指定 GitHub 仓库读取；未用替代声明补接口。
完整仓库有 `ClassFieldTheory`、`FLTReuse`、`TauCetiReuse`、`OAI`、
`SkeletonInputs`、`GramCoreInputs`、`GramAssemblyInputs` 等真实源码根。
这些依赖不是待用户手工提供的占位内容。

54 个 vendored 模块的 `import Mathlib` 被替换为仅含显式官方 Mathlib imports 的
`FLTReuse.ExplicitMathlibImports`，另 2 个原仓库模块也收窄了 imports，
以缩小本地验证所需缓存。其定义与证明未改变，全部 56 项的
原始和修改后哈希列在 `vendor_import_changes.json`。
这一导入收窄也需要完整依赖编译验证；失败时应补齐真实 import，而不是加入新公理。

除原目标需显式列出两个 sieve 输入外，本轮尚未确认目标数学陈述本身存在反例或错误。
发现的工程问题主要是 ZIP 缺少真实 vendor/assembly 源码、导入头解析必须忽略注释，
以及宽泛 Mathlib 导入的缓存体积。实际源码已据真实仓库接线。

## 尚未完成的验收

完整实际适配链、`ActualCompletedMarkedEnergy.completedMarkedEnergy` 和
`HeckeSkeleton.completedMarkedEnergy` 必须通过固定环境编译及公理审计。
在这项验收通过前，报告不把源码中的 `by` 块算作已检查证明，PR 不应标记为 ready。
当前 CI 的精确结果、最新修复和剩余具体错误以 PR 描述及提交对应的日志为准。

AI-assisted development；本报告中的验证结论限于所记录的实际 Lean 检查。
