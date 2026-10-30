# 以 AxiomMath 为底座的 Hecke L 工程

本项目是 Hecke L 7/8 形式化在 Lean 4.35 上的主线。它是
[AxiomMath/DedekindZetaZeroFree](https://github.com/AxiomMath/DedekindZetaZeroFree)
的副本，原有的 Hecke L 主库迁移到它之上。上游证明了任意数域的 Dedekind ζ 在
`Re(s) > 31/32` 无零点，并推广到有限阶 Hecke L 函数（Cureton–Thorner，AxiomProver 生成证明）。

2026-10-30 从旧仓库 `C:\Users\Boyang\Desktop\Math\Hecke L` 的 `axiom/` 目录原样迁出（同盘改名，构建缓存保留）。
旧仓库保留为 Lean 4.34.1 的历史基线：主库 `formal/`、主骨架 `skeleton/`（80 个 sorry，提交 `404bf6c`）。
下文“旧仓库”均指它。路线图见 [ROADMAP_7_8.md](ROADMAP_7_8.md)。

## 来源

- 提交 `09afbb4ce6570c1615d58509dc197fc9f0956b7d`，Apache-2.0，许可见 [LICENSE](LICENSE)。
  从旧仓库 `.cache/dedekind-zeta-reuse-20261013/archive` 的存档复制，只删去 `.github`。
  本项目的第一次提交就是这一存档的原样导入（含上游原版 `lakefile.toml`）。
- 工具链 Lean `v4.35.0-rc3`，mathlib `0493595ecd5da8ef14742febab99728f98e948e8`，
  TauCeti `c197d7bdbae257e85d23443c89aa7cd34c13410b`，类域论包在 `vendor/class-field-theory`。
- 上游 Lean 源码未改动。`lakefile.toml` 只有两处添加：
  - 根包的 `weakLeanArgs = ["-j2"]`：每个 lean 进程少开线程，降低内存峰值。weak 参数不进构建哈希。
  - 下面列出的新库。

## 新增的库

| 库 | 来源 | 说明 |
|---|---|---|
| `HeckeGeneral` | 旧仓库 `formal/HeckeGeneral` | 原主库，416 个模块，与旧仓库逐字相同 |
| `FLTReuse`、`Zeta23`、`OAI`、`TauCetiReuse` | 旧仓库 `formal/vendor/*` | 原 vendored 代码，FLT 有 12 处适配（见下） |
| `HeckeAxiom` | 新写 | 到上游的桥接，以及骨架数据的 Axiom 构造 |
| `HeckeSkeleton` | 旧仓库 `skeleton/HeckeSkeleton` | 待证骨架的 4.35 版，`Base`/`Theta`/`Principal` 与旧仓库不同（见下） |
| `SkeletonInputs` | 旧仓库 `skeleton/*Inputs` 的源 | 骨架的外部输入，在同一次构建中从源码编译 |
| `HeckePort` | 新写 | openai/math 模块到一般数域的移植；目前只有试点 `CenteredMoment`（见 [PORT_PILOT.md](PORT_PILOT.md)） |

旧仓库 `formal/vendor/cft` 里的两个幂剩余模块没有复制：上游类域论包里有同路径的模块，
同时存在会冲突，现在统一用上游的版本。

## 为新版本做的改动

mathlib 新版的 `WithZeroMulInt.toNNReal_neg_apply` 结论变成 `e ^ WithZero.log x`
（旧版是 `e ^ toAdd (unzero hx)`）。vendored FLT 中 12 处依赖旧形式的改写相应改用
`WithZero.log_exp`：

- `M9997a08e2e613141`：改用文件内已有的 `valued_eq_exp_neg_ordNat`；
- `M0da9a4a2a3715e8f`、`M3e65066309eb12af`、`Mbc9d4338a4e2d269`、`Md02bd5b7bd5ecd46`、
  `Md54a214d9c9f2103`、`Mdb8d5743b601b219`：`h, toAdd_ofAdd` 改为 `WithZero.log_exp`；
- `M21c6e4c58058e8ac`、`M57d0c029832fef58`、`Ma50593c61082c6fc`、`Mea34a23e4d889544`：
  去掉 `show exp _ = ↑(ofAdd _) from rfl` 和 `unzero_coe`，直接用 `exp_ne_zero` 与 `log_exp`；
- `M0178bf39c5ada6d0`：`simp only` 列表改用 `WithZero.log_exp`。

## 桥接 `HeckeAxiom`

| 文件 | 内容 |
|---|---|
| `RayCharacter` | 导子的素因子刻画，理想系数的零点集，单位理想取 1 |
| `RaySpan` | 有限阶时，全正且 `α ≡ 1 (mod 导子)` 的生成元系数为 1；`toRayClassCharacter` |
| `SeriesBridge` | 级数对应、恒等定理、`s = 1` 处理；条件定理 `zeroFree_of_rayOutput` |
| `FiniteOrderZeroFree` | 调用上游 `heckeL_ne_zero`：有限阶特征及其范数扭曲在 `Re s > 31/32` 无零点 |

最终定理以原有的 `heckeContinuation` 和 `MeromorphicZeroFreeOn` 表述，
不是原目标 `GeneralHeckeSevenEighths`：指数是 31/32 而不是 7/8，且只覆盖有限阶特征及其范数扭曲。

## 骨架 Base 数据的 Axiom 构造

按旧仓库 `.cache/a435-base-construction-route/ROUTE.md` 的路线，用 Axiom 的同一次算术选择给出骨架
`Base.lean` 里尚未实现的数据，并证明由它决定的义务。下列模块都在 `HeckeAxiom.lean` 根和 Lake 目标里，
零警告，所列定理的 `#print axioms` 只有 `propext`、`Classical.choice`、`Quot.sound`。

| 文件 | 内容 | 对应骨架义务 |
|---|---|---|
| `ArithmeticAdapter` | 两库外部理想的同构；由允许生成元 recipe 构造 `ThetaArithmeticData`，生成元即 recipe 的生成元 | D-ARITHMETIC 的形式 |
| `AllowedGeneratorAdapter` | recipe 生成元的乘法相容性（积的生成元 = 单位六次方 × 生成元之积） | AR-ALLOWED-MULTIPLICATIVE |
| `ArithmeticChoice` | `exists_arithmeticChoice`：含给定初始集与 different 支撑、类群平凡、主特征且 idele 校正平凡的一般算术上下文；由上下文自身的允许整生成元得到 recipe | D-S、D-ARITHMETIC |
| `SignalAdapter` | 校正特征 Λ、G 作为 Hecke 特征；G 有限阶；Λ、G 在所选集合外非分歧 | D-SIGNALS、AR-G-FINITE-ORDER、AR-LAMBDA-UNRAMIFIED、AR-G-UNRAMIFIED |
| `LambdaInfinityType` | 标准复坐标下 Λ 在每个复位的角权为 ±1、径向参数为 0 | AR-LAMBDA-ANGULAR、AR-LAMBDA-RADIAL-ZERO |
| `SexticSymbolDictionary` | 两库的六次剩余符号一致（素理想层与理想层）；选定生成元的理想符号互反律 | AR-ALLOWED-RECIPROCITY |
| `TraceCharacterDictionary` | 每个有限位上骨架的 `psiLocal` 等于 Axiom 的 `localTraceCharacter`：远离 v 处整的元在 K_v 中稠密，两边的整体乘积公式在这些元上都给出 e(−Tr)；因而骨架的 `sLocalPrincipalPhase` 就是 Axiom 的 `fieldTraceCharacter` | Gauss 和字典的加法特征部分 |
| `GaussDictionary` | 骨架的 `thetaGamma J j`（0<j<6）等于 Axiom 的 `idealGauss`，生成元为选定的允许生成元：同一个商环、同一个范数、六次特征与加法特征逐项相同 | 校准的前提 |
| `GaussCalibration` | 素理想处用上下文的 `gammaTwo_cube`、`gammaOne_gammaTwo`，在局部单值化子的 idele 上取值，这一取值就是骨架的素系数；互素乘积用 `idealGauss_squarefree_crt`，互反律使两个 CRT 相位相等，校准只看到它的六次幂；按互素分解归纳到全部无平方因子理想 | AR-CUBE-CALIBRATION、AR-MIXED-CALIBRATION |
| `DenominatorAdapter` | Axiom 的实环形权 `W1` 作为骨架的 `DenominatorTest` | D-TESTS 的分母部分 |
| `MeasureAdapter` | Borel 结构与 Axiom 的自对偶局部 Haar 测度 `localNormalizedHaar`（局部整数的体积为 N(𝔇_v)^(−1/2)） | D-MEASURES |
| `ProbeUnits` | 骨架的 S-局部乘法群与 Axiom 的 `A.G` 作为拓扑群同构；骨架的乘积范数是 Axiom 的范数（所有无穷位都是复位），范数一子群互相对应，骨架的径向截面是 Axiom 的 `radialSection`；因而 Axiom 在 T 处、范数一元 t 上的 sheet point 就是骨架的 t·截面(T) | D-TESTS 的单位群字典 |
| `ProbeFourier` | Axiom 的无穷位相位就是骨架的标准混合特征；对由局部测度 μ_v 构成的 Axiom Poisson 加法测度，张量 g∘R·∏f_v 的 Axiom Fourier 变换 = 2^{r₂} × g 的骨架阿基米德变换 × 各 f_v 的骨架局部变换（`psiLocal`，同一 μ_v） | D-TESTS 的 Fourier 字典 |
| `ProbeTestChoice` | 取 μ 为骨架自对偶局部测度的 Poisson 测度、ν 为骨架范数一 Haar 测度的 sheet 测度，套用 `probe_fixed_weight_construction` 与 `probe_sheet_mellin_estimates_of_disintegration`；由 Axiom 张量的环形坐标构造骨架的加法测试（阿基米德因子在迹模型中，乘以常数 a）。其加法 Fourier 与 Mellin 变换是 Axiom 的 a·κ 倍，κ = 2^{−r₂}∏μ_v(𝒪_v)⁻¹；取 a = conj M/‖M‖ 使 1/6 处的 Mellin 值为正实数 ‖M‖ | D-TESTS、PR-FOURIER-ZERO |
| `ProbeNormalization` | 极点消去的 Dedekind ζ 在 1 处的值是残数（连续性加 Mathlib 的右极限）；平凡特征的删去 Euler 多项式在 1 处是 ∏(1 − N𝔭⁻¹)；分母测试在 1 处的 Mellin 值是 W1 的正积分；故 `physicalResidueNormalizer` 为正实数 | PR-NORMALIZATION-REAL、PR-NORMALIZATION-POSITIVE |

`AR-ALLOWED-GENERATOR-NORM` 对任意 `ThetaArithmeticData` 都成立（`HeckeSkeleton.AllowedGeneratorNorm`）。
Proposition 3.1 的 11 项 AR 义务在本项目里全部关闭，D-TESTS 簇（D-TESTS、PR-FOURIER-ZERO、
PR-NORMALIZATION-REAL、PR-NORMALIZATION-POSITIVE）也已关闭。Base 里剩下的 D-MESH、D-EXPANSION、D-SUPPORT
依赖矩估计与高频展开，不由 Axiom 的算术选择决定。

与旧仓库 `experiments/Axiom435Intake/`（提交 60a5a2a、e4ad402 的未验证候选）的对应：其 README 构造顺序的
第 2–5 步（初始集、单一 recipe 选择、算术数据与信号、生成元律、六次符号与互反律、分母测试、目标或其共轭的
选取）在本项目由上表模块原生编译并接入骨架，可取代那里的对应候选；那里的 `AngularThirdBesselMellin`
（已原生验证）与角向 Whittaker 词仍属第 6 步（TH 簇），本项目尚未使用。

### 与旧仓库 `skeleton/` 的差别

本项目的 `HeckeSkeleton` 原本与旧仓库 `skeleton/HeckeSkeleton` 逐字节相同。下列三个文件接上了上面的构造；
以后从旧仓库同步时不要覆盖它们。

- `Base.lean`：新增 `targetRamifiedPlaces`、`complexEmbedding`、`axiomChoice`（一次选择，根取 family 的
  `root12`）和 `target_unramified_outside`；`excludedPlaces`、`arithmeticData`、`signalCharacters` 取自
  这一次选择，`probeMeasures` 取自 `MeasureAdapter`。目标先去掉整体范数扭曲（`untwisted`：取目标的一个
  分解 θ·ω^e·N^{it}，去掉 N^{it}），Axiom 选择以它的分歧集为初始集；`representative` 按修订稿 §3
  （Prop. 3.2 之前）的定向：若 conj(Λ)·conj(G)·θω^e 在某个复位的角权非零就取 θω^e，否则取其共轭
  （共轭与范数扭曲都不改变分歧集和零点实部集合）。`untwisted`、`representative` 及其定向引理与旧仓库
  逐字相同。`probeTests` 取 `ProbeTestChoice.exists_probeTest` 选出的加法测试，分母取 Axiom 的
  `probeRealBumpWeight`。D-S、D-ARITHMETIC、D-SIGNALS、D-MEASURES、D-TESTS 只在本项目不再是 sorry。
- `Theta.lean`：AR-LAMBDA-UNRAMIFIED、AR-G-UNRAMIFIED、AR-G-FINITE-ORDER、AR-LAMBDA-ANGULAR、
  AR-LAMBDA-RADIAL-ZERO、AR-CUBE-CALIBRATION、AR-MIXED-CALIBRATION、AR-ALLOWED-MULTIPLICATIVE、
  AR-ALLOWED-RECIPROCITY 由同一次选择给出；TH-MARKED-EXTERIOR-UNRAMIFIED 由周期
  conj(Λ)·conj(G)·ψ 各因子在 S 外非分歧给出。
- `Principal.lean`：PR-TARGET-UNRAMIFIED 由初始集给出；PR-PERIOD-UNRAMIFIED 由 Λ、G、ψ 的非分歧性给出；
  PR-FOURIER-ZERO 与新增的 `principal_mellin_positive` 是 `exists_probeTest` 的性质，PR-NORMALIZATION-REAL、
  PR-NORMALIZATION-POSITIVE 由 `ProbeNormalization.physicalResidueNormalizer_pos` 给出。

两边同时关闭、不依赖 Axiom 的四项：
- D-RAY 取空滤子：修订稿 §6.1 原文为 “All primes outside S are allowed”，§4 的槽也写明 “there is no
  identity-ray restriction”（§4.3 允许的固定有限射线限制未被使用），于是 PR-RAY-FINITEORDER 空真。
- D-REP 与 TH-MARKED-ANGULAR-NONZERO：如上的去扭曲与定向；TH-MARKED-ANGULAR-NONZERO 由 AR-LAMBDA-ANGULAR
  （Λ 的角权 b = ±1）与 AR-G-FINITE-ORDER 推出，因为 k − b 与 −k − b 不能同时为零；由 12 次本原根，
  所有无穷位都是复位。

### 当前计数

2026-10-30 13:42 的 Lake 构建（`LEAN_NUM_THREADS=4 lake build HeckeAxiom HeckeSkeleton SkeletonInputs`，
日志 `.lake/build-logs/skeleton435-20261030-dtests.log`）成功，共 15137 个任务。`Audit` 报告 60 个直接 sorry，
终点公理为 `propext, sorryAx, Classical.choice, Quot.sound`，115 项具名叶子的公理检查只有标准三公理。
D-TESTS 新模块的主要定理 `sheetPoint_normOneEquiv`、`fourier_eq`、`exists_probeTest`、
`physicalResidueNormalizer_pos` 的 `#print axioms` 也只有这三条。上一次计数是 10:40 的 64 个
（日志 `.lake/build-logs/skeleton435-20261030-1035-aligned-retry.log`）。
旧仓库的 4.34.1 主骨架为 80；只在本项目关闭的 20 项是：D-S、D-ARITHMETIC、D-SIGNALS、D-MEASURES、D-TESTS，
AR-LAMBDA-UNRAMIFIED、AR-G-UNRAMIFIED、AR-G-FINITE-ORDER、AR-LAMBDA-ANGULAR、AR-LAMBDA-RADIAL-ZERO、
AR-CUBE-CALIBRATION、AR-MIXED-CALIBRATION、AR-ALLOWED-MULTIPLICATIVE、AR-ALLOWED-RECIPROCITY，
PR-TARGET-UNRAMIFIED、PR-PERIOD-UNRAMIFIED、PR-FOURIER-ZERO、PR-NORMALIZATION-REAL、PR-NORMALIZATION-POSITIVE，
以及 TH-MARKED-EXTERIOR-UNRAMIFIED。

### 下一步

建议的顺序和理由见 [HANDOFF.md](HANDOFF.md)。第一个移植试点已做（[PORT_PILOT.md](PORT_PILOT.md)），下一个试点选
openai 矩递推中的账本模块；然后对照评估 theta 侧（Axiom 的一般域 theta 与 openai 的带标记反射）；
三次大筛（MI-M-CUBIC-SIEVE）和阿贝尔下降（DE-*）可以并行。
openai/math 中 Q 的形式化的复用审计见 [OPENAI_REUSE_AUDIT.md](OPENAI_REUSE_AUDIT.md)。

## 构建

依赖包放在 `.lake/packages`：mathlib 等 9 个包是指向旧仓库 `.cache/u435/formal/.lake/packages` 的目录链接
（其中已有 mathlib 编译缓存，所以旧仓库的 `.cache` 不能删）；TauCeti 是本项目 `.lake/packages` 里的实际目录，
从旧仓库 `.cache/a435-deps/TauCeti` 复制。`.lake/` 与 `vendor/*/.lake/` 是构建产物，不入库。

Lake 5 没有并发参数，并发由 `LEAN_NUM_THREADS` 控制。这台机器上每个 lean 进程约占 3 GB 内存，
构建在内存紧张时偶尔报 “failed to read file …olean”，重跑即可：

```bash
LEAN_NUM_THREADS=4 lake build HeckeAxiom HeckeSkeleton SkeletonInputs
```

`HeckePort` 不被骨架导入，要单独构建：`LEAN_NUM_THREADS=4 lake build HeckePort`。

`HeckeAxiom.FiniteOrderZeroFree` 依赖上游 `HeckeCorollary`，其导入闭包是上游 3,867 个模块中的
3,850 个（约 75 万行），首次编译需要很长时间。

直接编译用 `tools/compile435.py`：不经 Lake、不写 `.lake`，可与 Lake 构建同时运行，按源码与依赖哈希增量重编，
输出目录由环境变量 `COMPILE435_WORK` 指定（默认 `tools/skel435`）；`tools/run_lean435.py <输出目录> <文件>`
在同一搜索路径下运行单个文件，例如 `#print axioms` 审计。
