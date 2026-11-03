# 交接：2026-10-30 晚（最新一节在前）

## 夜间：GR-07、GR-10 关闭；GR-12 开始移植

直接 sorry 降到 49（按各文件 `sorry` 计数，未重跑 Audit）。剩余分布：Moments 16、Expansion 9、Theta 8、HighBin 6、Principal 4、Base 3、Gram 2（GR-11、GR-12）、Descent 1。

**已关闭**
- GR-07：`HeckeSkeleton/GramExceptionalCount.lean`。按（理想，单位类）计数，不经过 `ProbeData`。
- GR-10：`HeckeSkeleton/GramRowBall.lean`。直接用核心库 `ActualGramRowBallOrbitalMajorant`。

**GR-12 的计划与移植**（详见 [TASK_GR12.md](TASK_GR12.md)）
- 核心库已给出零频率项 C·Q/Y 和行球 Poisson 约化，剩下的是非零对偶频率的界。旧仓库把它拆成八个目标，见 `.cache/hard-splits-20261029/gram-gr12-splits.md`。
- 提供者闭包共 193 个模块、约 2.7 万行，分三部分：
  - 无见证部分 112 个，已复制进新库 `GramAssemblyInputs/`（在 `lakefile.toml` 登记；顺序编译器 `GramAssemblyInputs/build_driver.py`，状态在 `.port/`）；
  - 旧见证 `ActualAdjustedGeneratorWitness` 的闭包 30 个，不移植；
  - 依赖旧见证的消费者 22 个。
- **注意**：按旧缓存的原生回执核对，135 个待移植模块中只有 22 个曾经编译成功，其余都只经过静态审查，从未编译。所以这是真正的修错工作，不是机械搬运。
- 旧见证只通过 `w.D`、`w.S` 和补群 C6 的几条性质被使用。计划换成抽象结构 `GeneratorMaskWitness`，再由 Axiom 的 `AllowedRecipe` 实例化：它同样是"生成元的 S 局部六次方类落在单位像的补群里"。
- 子代理（Sonnet）正在做阶段 1、2（编译修错、抽象见证）。阶段 3（Axiom 实例化）和阶段 4（最终装配，旧仓库也没有）之后再派。

**进行中的代理**
- GR-11：小半径链移植到 `HeckeSkeleton/SmallRadius/`，Sonnet；
- LOW-CAUCHY：Opus，按 [TASK_LOW_CAUCHY.md](TASK_LOW_CAUCHY.md)，新文件 `HeckeSkeleton/LowCauchy*.lean`；
- GR-12 移植：Sonnet，只动 `GramAssemblyInputs/` 和 lakefile 的 roots；
- Moments 簇移植规划：只读，产出移植批次计划。
- 另外，Codex 在 `CubicSieve/` 移植 openai 的三次大筛（用户自己派的）。

**内存**：高峰时提交量到过 90.3/90.7 GB（页面文件自动扩到约 60 GB）。物理内存里其他程序约占 21 GB，所以只能同时全速跑约 2 个 lean。已建议用户关掉不用的程序，并把页面文件设为固定 64 GB。

## 晚间：Gram 簇、下降接口与并行

直接 sorry 从 60 降到 51（中途计数，以最新 Audit 为准）。

**已关闭**
- GR-03、GR-04、GR-05、GR-08、GR-09；
- PR-PRINCIPAL-WINDOW-ERROR；
- DE-ARTIN-CHARACTERS、DE-TRIVIAL-FACTOR、DE-POLE-MATCHING（Codex 完成，报告见 [DESCENT_CODEX_REPORT.md](DESCENT_CODEX_REPORT.md)）。

**接口改动（用户同意）**
DE-EULER 改成删除型。`HeckeSkeleton/Descent.lean` 的 `deletedEulerFactorization` 是存在形式：两边各删去有限个素位后的 Euler 恒等式，不要求分歧素位处的精确局部因子。`descend` 用通用的 `meromorphicZeroFreeOn_of_factorization` 推出：删除多项式在 Re s > 0 上不为零，零极点阶也不变。

**新库**
- `GramCoreInputs`：旧缓存 `actual-gram-core-native-20261012` 最后一次原生运行的 39 个模块，原样编译通过。另有 2 个与 `HeckeSkeleton` 中同名文件逐字相同，已改为引用后者。
- `HeckePort`：移植试点。

**新模块**
| 模块 | 内容 |
|---|---|
| `HeckeSkeleton/GramDyadic.lean` | GR-08 |
| `HeckeSkeleton/GramIdealShell.lean` | GR-09 |
| `HeckeSkeleton/GramCorrelation.lean` | 骨架 `correlation` 等于核心库的原始完整相关和；由此得 GR-03、GR-04 |
| `HeckeSkeleton/GramMeanZero.lean` | GR-05，子代理完成 |
| `HeckeSkeleton/ActualPrincipalWindowError.lean` | 旧缓存中原生编译过的模块，给出 PR-PRINCIPAL-WINDOW-ERROR |
| `HeckeSkeleton/Descent/ArtinFactors.lean`、`HeckeSkeleton/Descent/PoleMatching.lean` | Codex 完成 |

**进行中或待派**
- 子代理在做 GR-11，以及 GR-10、GR-07。
- [TASK_LOW_CAUCHY.md](TASK_LOW_CAUCHY.md)：LOW-CAUCHY-COMPENSATION 的任务说明，指数核对已写在其中；等内存允许时派出。
- [CODEX_TASK_DESCENT_2.md](CODEX_TASK_DESCENT_2.md)：删除型 Artin Euler 恒等式，做完 DE 就全部关闭。
- [CODEX_TASK_PIT.md](CODEX_TASK_PIT.md)：PR-NORMALIZER 两项，需要窗口中的素理想定理。Mathlib 里没有素数定理；可以从 Axiom 的 Re s > 31/32 零点自由半平面出发。

**旧缓存里已验证、可以直接用的成果**（`C:\Users\Boyang\Desktop\Math\Hecke L\.cache\`）
- `actual-grouped-theta-native-20261012`：35 个模块，有完成封条。内容是带标记 theta 的共同 Fourier 环形重构，可能用于 LOW、TH。
- `actual-gram-gcd-mobius-assembly-20261012`：7 个模块，有完成封条。是 GR-12-04 需要的 gcd/Möbius 重排。
- `actual-gram-small-radius-profile-20261012`：27 个源文件，原生只编到第 13 个，用于 GR-11。
- `gram-witness-resume-20261029`：30 个模块编译通过，可能对应 GR-12-05。
- `gr12-fixed-S-*`、`refprobe-*`、`gram-probe-*`：GR-12-02 的参考截面与理想探针。

**内存**
每个 lean 进程约占 3.3 GB 工作集、8.4 GB 提交，提交上限 71 GB。本晚同时开 2–3 个编译代理时，提交量一度到 67.8 GB。并行前先看 `\Memory\Committed Bytes`。

# 交接：2026-10-30 下午

这一轮做了四件事：判断剩余距离、审计 openai/math 中 Q 的形式化、关闭 D-TESTS 簇、做第一个移植试点。骨架的直接 sorry 从 64 个降到 60 个；剩余部分估计约 40 万行 Lean（区间 28–54 万，依据见 [PORT_PILOT.md](PORT_PILOT.md)）。项目背景、已关闭的义务和构建方法见 [HECKE_PORT.md](HECKE_PORT.md)，这里只写接下来做什么。

## 先读

1. [HECKE_PORT.md](HECKE_PORT.md)：项目来源、本项目已关闭的 20 项、新模块表、构建方法。
2. [ROADMAP_7_8.md](ROADMAP_7_8.md)：论文附录的十步与骨架义务的对应。
3. [OPENAI_REUSE_AUDIT.md](OPENAI_REUSE_AUDIT.md)：Q 的完整 Lean 形式化（openai/math）的规模、完整性和能复用什么。
4. 旧仓库 `skeleton/OBLIGATIONS.md`、`skeleton/HARD_STATUS.md`、`skeleton/hard-frontiers.json`：义务清单（4.34.1 基线 80 项），以及 10 个困难父项拆成的 54 个数学子目标。
5. [PORT_PILOT.md](PORT_PILOT.md)：第一个移植试点的实测数据（推广系数、每行 token），以及剩余行数的分块估计。

## 剩余 60 个 sorry 的分布

| 步骤（论文附录） | 状态 | 剩余 |
|---|---|---|
| 1–2 算术与 Gauss 校准 | 已关 | 0 |
| 3 轨道 Poisson 与 Gram | GR-01/02/06 已证 | 9（GR-03…GR-12） |
| 4 theta 与标记反射 | 缺 | 8（TH-*） |
| 5 反射能量与两条数域大筛 | 缺 | 3 |
| 6 两次逆变换递推 | 缺 | 4（MI-I-*） |
| 7 素数前提 | 部分 | 2（MI-P-PRIME-*） |
| 8 四阶矩递推 | 缺，最难 | 3 |
| 9 物理估计、高频与 Euler 补偿 | 部分 | 21（EX 9、HB 6、PR/LOW 4、D-EXPANSION、D-SUPPORT） |
| 10 指数比较与闭合 | 条件形式已有 | 0 |
| 矩模型与网格 | — | 6（MI-M 模型类 5、D-MESH） |
| 阿贝尔下降 | 经典类域论，与分析核心无关 | 4（DE-*） |

困难的部分集中在 10 个困难父项：GR-12、HB-NORMFORM、TH-KP-DATA、TH-MARKED-REFLECTION、LOW-REFLECTED-ENERGY、EX-DETECTOR-WITNESSES、MI-I-CANONICAL-RECURSION、MI-P-POSITIVE-SLOTS 两项和 MI-P-ZERO-SLOT。D-MESH 不能单独关：它要在几何和目标之前选定，主库现有来源只到 5/6，要等第 8 步推到端点 1 才能确定。

## 已完成：D-TESTS 簇

关闭了 `Base.lean` 的 `probeTests`（D-TESTS），以及 `Principal.lean` 的 `principal_fourier_zero`、`principal_normalization_real`、`principal_normalization_positive`。新增四个模块：`ProbeUnits`、`ProbeFourier`、`ProbeTestChoice`、`ProbeNormalization`，各自内容见 HECKE_PORT.md 的模块表。

做法的要点：

- 加法测度取 Axiom 的 `poissonAdditiveMeasure`，用骨架自己的局部测度构造；单位群上的测度取骨架范数一 Haar 测度的 sheet 测度。这样 `ProbeSheet.HaarDisintegration` 按定义成立，Axiom 的 `probe_fixed_weight_construction` 和 `probe_sheet_mellin_estimates_of_disintegration` 可以直接套用。
- 后者给出"先在范数一层上积分、再做径向 Mellin = fourierMellin"，可积性也已证好。所以原计划的第三块字典（乘法测度）不用再写。
- 骨架的测试函数由 Axiom 张量的环形坐标构造，阿基米德因子乘以常数 a。它的 Fourier 与 Mellin 变换都是 Axiom 的 a·κ 倍；取 a = conj M/‖M‖，1/6 处的 Mellin 值就是正实数 ‖M‖。

后面写桥接时用得上的 Lean 经验：

1. 骨架 `selfDualProbeMeasures` 的字段（`localSpace`、`normOneSpace`）在实例透明度下展不开。在 HeckeAxiom 里和 Axiom 的引理一起用时：
   - 局部可测结构直接写 `borel _`；
   - 测度写成同一测度、borel 类型的 `localHaar`。

   否则 σ-有限、乘积 Haar 这类实例会找不到。接回骨架时用 `exact` 或项证明，默认透明度能对上。
2. 混合空间上的 `volume` 和复位子类型的 `Fintype` 需要 `open scoped Classical`（骨架文件都开着）。
3. 定义里写成 `((∑ ...) : ℂ)` 的类型标注，会把求和直接展开在 ℂ 里；对这种定义陈述恒等式时要按复数和写。
4. `integral_fintype_prod_eq_prod` 要显式给出类型族 `E`，否则推断失败。
5. 局部记号别用单字母 `R`，它会吞掉命名参数 `(R := ℝ)`。引用其他局部记号的记号需要 `set_option quotPrecheck false`（`Principal.lean` 也这样做）。
6. 本文件、其他 HeckeAxiom 文件和 Axiom 内部各有自己的 `borel` 局部实例常量。`rw` 常因实例项写法不同而匹配失败；这时改用 `calc` 或 `exact`（默认透明度），或者先把目标改写成本文件里的项。

## 之后的顺序（建议）

1. **第二个移植试点**：第一个已做（中心矩底层 7 个模块，新库 `HeckePort`，见 [PORT_PILOT.md](PORT_PILOT.md)）。与域无关和 Dedekind 通用的代码推广系数约 1.0–1.1，每行约 130 token。下一个选账本递推模块，其中行是 O 的元素、对有限单位群求和，连同它实际用到的定义一起移植，例如 `CommonMaskChildCapacity`。注意 `AllocatedChildCapacity` 本身只有 320 行，但它在 `Moments` 内部的依赖链有 2.8 万行。
2. **theta 评估**：三方对照 Axiom 的 `Theta/`、`Metaplectic/`（一般域、无标记），openai 的 `Reflection/`（有标记、ℚ(ω)），以及论文命题 3.2 与定理 3.5。核心问题是：Axiom 的 theta 反射能不能在复位上换成 K-型为 m 的向量（论文用升算子取 φ_m = E^m φ°）。
3. **三次大筛（MI-M-CUBIC-SIEVE）**：照 Axiom 把 openai 的 `QuadraticSieve/` 推广成 `goldmakherLouvel` 的做法，推广 openai 的 `CubicSieve/`（ℤ[ω] 上 Heath-Brown 式，`HasSieveExponent.improve`）。目标是论文引理 `lem:exterior-cubic-sieve`（BGL 定理 1.3，n = 3）。这项不依赖骨架的其他部分，可以并行做，只在新目录 `CubicSieve/` 下工作。
4. **阿贝尔下降 DE-*（4 项）**：经典类域论，独立于分析核心，随时可以做。

二次大筛那条（MI-M-QUADRATIC-SIEVE）上游已经有 `rm_hgl_oriented`，剩下的是论文 §4.3 第一段的族识别，即构造一个 `QuadraticHeckeFamily`。上游是否已有这个构造还没查。

## 论文与外部材料

- 论文修订稿 `weil_seven_eighths_revised.tex`，作者本人提供，放在项目根目录，但不入库。骨架义务引用的节号和它对得上。
- 稿中有一处与上游不一致：第 146–149 行说 Cureton–Thorner 证明的是 Re s > 1 − 1/6000，但上游 Lean（`Challenge/DedekindZetaChallenge.lean:32`）和 README 写的都是 31/32。待作者核对。
- 附录 A 末段说第 6、8 步按位置引用 Q §§17–18。这两节的 TeX 有 3,268 + 2,508 行，比整篇论文还长；不过它们在 openai 里已经有 ℚ(ω) 上的 Lean 证明。
- Q 和 P 的 TeX：旧仓库 `.cache/upstream/papers/quasi-riemann.tex`，以及同目录下的 `primitive-*.tex`。
- openai/math 的克隆：旧仓库 `.cache/openai-math-fd4aeeb2/`。这是部分克隆，只稀疏检出了 `lean/OAI/NumberTheory/DirichletL` 和 `lean/docs`，检出的是最新提交 `4eaee875`，其中 DirichletL 与钉住的 `fd4aeeb2` 完全相同。这是外部数据：只读，不要在里面运行构建或脚本。
- 用户还有一份 AI 生成的结构简化稿 `C:\Users\Boyang\Downloads\weil_structural_simplification.tex`。它对形式化剩余的影响很小：没有 sorry 因此消失，大约省掉 1 个困难子目标（TH-MARKED-REFLECTION 的 UNFOLDING）。它关于闭合只需固定 B 的说法，骨架早已采用（`TIPInput` 先量化 B，以及 `tipFinalSaving`）。它对论文修订有用。

## 注意事项

- 构建命令是 `LEAN_NUM_THREADS=4 lake build HeckeAxiom HeckeSkeleton SkeletonInputs`。每个 lean 进程约占 3 GB 内存；内存紧张时偶尔报 "failed to read file …olean"，重跑即可。不要同时跑两个大构建。这条限制的是全量构建（每个同时开 4 个 lean 进程），不是会话数。2026-10-30 实测：检查一个导入 HeckeGeneral 的移植模块，lean 进程峰值工作集 3.3 GB、提交 8.4 GB；本机 12 核 24 线程，提交上限 71 GB（31 GB 内存加 40 GB 页面文件）。多个会话并行时，各自用 `lake env lean` 或 `tools/compile435.py`（各设一个 `COMPILE435_WORK`）编译，全量 `lake build` 只由一个会话在其他会话不编译时跑。
- 单个新模块可以用 `lake build HeckeAxiom.<模块名>` 构建，比全量快得多；只做类型检查、不写 `.lake` 时，可以用 `python -I tools/run_lean435.py <scratch 目录> <文件>`。
- `HeckeSkeleton` 的 `Base`、`Theta`、`Principal.lean` 和旧仓库不同，从旧仓库同步时不能覆盖。
- 旧仓库的 `.cache` 不能删：本项目 `.lake/packages` 里有 9 个包是指向它的链接，openai 的克隆也在那里。
