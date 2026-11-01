# 剩余工作总账（2026-10-31 早更新）

最新 Audit：直接 sorry 45 个（其后关闭 MI-M-QUADRATIC-SIEVE 与 TH-KERNEL 的三项，新增小义务 TH-SIXTH-LOCAL-FINITE，应为 42 个；接入 Codex 的三次大筛后应为 41 个）；终点公理为 propext、sorryAx、Classical.choice、Quot.sound。

**口径**
- 剩余工作拆成大致等量的单位，每个单位约 5,000–10,000 行最终 Lean。
- 估计行数来自三类依据：openai 或缓存中对应证明的行数，乘以 1.0–1.2 的推广系数；论文篇幅；三个只读规划代理的统计。误差约 ±30%。
- 进度按"已关闭单位数 / 总单位数"计，行数只作参考。
- 详细来源：[PLAN_THETA.md](PLAN_THETA.md)；Moments、Expansion 两份规划的要点写在本文件各节里。

**单位的状态**：一个单位关闭，指它对应的 sorry 全部消失、编译通过、只用三条标准公理。表里的"Lean 中"一栏说明这个单位现在是否已经是骨架里的一个 sorry："是"，或者"待拆"（要等定义层移植进来，才能写出精确陈述）。

## 汇总

| 簇 | 单位数 | 估计行数 | 状态 |
|---|---|---|---|
| Gram（GR-12） | 3 | 2.0 万 | 全部关闭 |
| Principal（PR-WINDOW-PIT） | 1 | 0.7 万 | Codex 说明已就绪 |
| Descent（DE-EULER） | 1 | 0.2 万 | Codex 说明已就绪 |
| Theta 与 LOW-REFLECTED-ENERGY | 15 | 8.75 万 | TH-KERNEL 已关闭 |
| Moments（不含三次大筛） | 35 | 26 万 | 规划完成 |
| 三次大筛 | 0 | — | 已关闭（Codex，78 个文件 11,790 行，已接入 Moments） |
| Expansion、HighBin、D-EXPANSION | 13 | 8 万 | 规划完成 |
| **合计** | **68** | **约 50 万** | |

## 进度（2026-11-01 19:00）

总 68 单位（建账时 75，10-30 晚之前已关 7）。已完成约 46.9 个单位，**剩余约 21.1 个**：配对引擎 14 个（PR #9 单步、#12 归纳），逆归纳 6 个（PR #8），小义务 6 的余下部分约 1 个（`paired_primes_below_one` 与三个 MI-P 包装）。骨架只剩 `Moments.lean` 的 5 个 sorry。

| 单位 | 计入 | 说明 |
|---|---|---|
| GR-12-MASK | 1.0 | 已关闭：`AxiomGeneratorMaskWitness` 加 `HeckeSkeleton.GeneratorMask`（实际约 300 行，建账时高估） |
| GR-12-ASSEMBLY | 1.0 | 已关闭：`gram_assembly` 只用三条标准公理；Gram 簇全部完成 |
| GR-12-PORT | 1.0 | 133 模块编译通过，三条标准公理；6 个 SmallRadius 消费者待上游 |
| TH-REFL-ARCH、TH-REFL-EXTERIOR-DIGITS | 2.0 | 已关闭：核心与接线（PR #4，d5cbc31）均已合并 |
| LOW-HYBRID、LOW-FROZEN-CUBE | 2.0 | 已关闭：核心与接线（PR #6，d6fd2cf）均已合并 |
| LOW-COMMON-PROFILE、LOW-ROWCOUNT、LOW-PHYSICAL-ASSEMBLY（LOW-REFLECTED-ENERGY） | 3.0 | 已关闭：PR #3 合并（0ec5096），约 3.3 万行；`Principal.lean` 的 sorry 消失，`completedMarkedEnergy` 改为引理 4.8 一般版，物理版为 `physicalCompletedMarkedEnergy`；三条标准公理 |
| THETA_GLOBAL（TH-KP-DATA-1/2、TH-FINITE-VALUATION、TH-MARKED-REFLECTED-ABSOLUTE、TH-REFL-AUTOMORPHIC/DIRECT/REFLECTED-UNFOLD/MELLIN） | 8.0 | 已关闭：PR #2 合并；Pro 写约 3 万行，本地子代理收口编译；五项义务只用三条标准公理 |
| MOM_BASE（共享底座） | 2.5 | 已关闭：PR #15 合并，引理 4.3、4.4 与实际有限系数（约 4,000 行，建账时高估） |
| MOM_INV_STEP（规范逆归纳单步，逆变换链约一半） | 5.0 | 已合并：PR #13（c9c002c），274 个文件约 5.75 万行；`canonical_inverse_step` 只用三条标准公理。Pro 写主体，本地子代理收口编译。骨架 sorry 要等 MOM_INV_INDUCTION 接线才消失 |
| Moments S0、S1 | 1.5 | ℤ[ω] 专用输入仍为显式假设 |
| HB-EULER-INITIAL、HB-EULER-EXCEPTIONAL | 0.5 | 核心已并入；接线是 PR #1（草稿） |
| Expansion、HighBin、D-EXPANSION 簇其余 12.5 个单位（EX-*、HB-PRESENT、HB-NORMFORM、HB-MOVE-BOUNDARY、HB-EULER 接线） | 12.5 | 已关闭：集成 PR #17（235764f）合入 #5、#7；`Expansion.lean`、`HighBin.lean`、`Base.lean` 无 sorry，三条标准公理 |
| Moments 小义务 2–5（MI-M-MODELS、POLYNOMIAL-CALIBRATION、FIBER-ELIGIBILITY、FINITE-SECTOR-REINDEX、PROFILE-UNIFORMITY、MI-I-SIXTH-POWER-ZEROS、INDEPENDENT-AMPLIFICATION、AMPLIFIED-WITNESS-CALIBRATION） | 4.0 | 已关闭：#5 的共享配方与 #10 的六个目标，经 PR #17 合入；三条标准公理 |
| 小义务 6 增量：MI-P-PRIME-ABSOLUTE-ENDPOINT | 0.2 | 已关闭：#11 的 `paired_primes_endpoint`，经 PR #17 合入 |
| 小义务 6（素数相消） | 0.7 | 核心与接线（PR #14）已合并：`paired_primes_below_one_of_models` 对任意模型成立；剩为实际 `momentModels` 验证 `PrimeSlotModelControl` |
| PR-WINDOW-PIT | 1.0 | 已关闭：Codex 的 `WindowPIT` 接入 `PrimeNormalizer`，编译通过 |
| DE-EULER-FACTORIZATION | 1.0 | 已关闭：Codex，`descend` 只用三条标准公理 |

比之前估计的 40 万多，主要是 Moments 的两条递推比预想的大（约 22 万行）。

## 本晚已关闭的义务

不计入上面的单位。GR-03、04、05、07、08、09、10、11；D-MESH（Moments 第 1 个小单位中的数值调度部分）；MI-M-QUADRATIC-SIEVE（`HeckeAxiom/QuadraticSieve.lean`，套用 Axiom 的 Goldmakher–Louvel 二次大筛）；TH-KERNEL 单位（`HeckeSkeleton/ThetaKernel*`，约 1,600 行，导数界只差小义务 TH-SIXTH-LOCAL-FINITE：S 局部六次方类群有限，约 500 行）；PR-PRINCIPAL-WINDOW-ERROR；PR-NORMALIZER 两项（改由 PR-WINDOW-PIT 推出）；LOW-CAUCHY-COMPENSATION；DE 的三项。

## Gram（3）

| 单位 | 估计 | Lean 中 |
|---|---|---|
| GR-12-PORT：`GramAssemblyInputs` 的 135 个模块修错，加上抽象见证接口 | 1.0 万 | 待拆（以模块编译通过计） |
| GR-12-MASK：用 Axiom 的选取实例化见证 | 0.3 万 | 待拆 |
| GR-12-ASSEMBLY：分普通频率与例外频率两部分装配，以及复值 W 的转移 | 0.7 万 | 是（`gram_assembly`） |

## Principal、Descent（2）

| 单位 | 估计 | Lean 中 |
|---|---|---|
| PR-WINDOW-PIT 窗口素理想定理 | 0.7 万 | 是 |
| DE-EULER-FACTORIZATION | 0.2 万 | 是 |

## Theta 与 LOW（16）

见 [PLAN_THETA.md](PLAN_THETA.md)。

- TH-KP-DATA-1、TH-KP-DATA-2
- TH-FINITE-VALUATION
- TH-KERNEL
- TH-MARKED-REFLECTED-ABSOLUTE
- TH-REFL-ARCH、TH-REFL-EXTERIOR-DIGITS、TH-REFL-AUTOMORPHIC、TH-REFL-DIRECT-UNFOLD、TH-REFL-REFLECTED-UNFOLD、TH-REFL-MELLIN
- LOW-HYBRID、LOW-FROZEN-CUBE、LOW-COMMON-PROFILE、LOW-ROWCOUNT、LOW-PHYSICAL-ASSEMBLY

**先修的结构问题**
1. `finiteMellinData` 改成带规格字段的真实构造。
2. 三个核义务改成对一般数据陈述。
3. `completedMarkedEnergy` 显式加两个大筛假设。

## Moments（35，另有三次大筛 5 个）

**关键发现**
- openai 的四阶矩递推是一个对槽通用的联合归纳。MI-P-ZERO-SLOT、MI-P-POSITIVE-SLOTS-BELOW-ONE、MI-P-POSITIVE-SLOTS-ENDPOINT 是同一个引擎的三个投影。所以新设父义务 MI-P-ENGINE，这三项成为薄包装。
- MI-P-ZERO-SLOT 依赖 MI-P-PRIME-ABSOLUTE-ENDPOINT（κ = 1）。
- D-MESH 很容易：取 `fineMesh 2 0 1 1 lamA`，源自 openai 的 `Energy/WidthSchedule`。填上之后，`TargetContext` 就不再带 sorryAx。这是第一批的内容。
- MI-M-MODELS、MI-M-POLYNOMIAL-CALIBRATION 必须与 D-EXPANSION 一起设计：由同一个见证配方生成，校准就近乎 `rfl`。

**单位**

| 单位 | 数量 | 每个估计 |
|---|---|---|
| MI-I-CANONICAL-RECURSION-1…15：共享底座 S0–S4，加逆变换链 I0–I9 和 Dictionary | 15 | 约 0.7 万 |
| MI-P-ENGINE-1…14：配对递推 P0–P13，出口是 `terminal_certificate` | 14 | 约 0.7 万 |
| 小义务合成 6 个单位 | 6 | 见下 |
| 三次大筛 MI-M-CUBIC-SIEVE-1…5（Codex） | 5 | 约 0.8 万 |

小义务的 6 个单位：
1. D-MESH 加数值调度（第一批），与有限相关和标记（B2）合并，约 0.35 万；
2. MI-M-MODELS 与 MI-M-POLYNOMIAL-CALIBRATION，约 0.45 万；
3. MI-M-FIBER-ELIGIBILITY、MI-M-FINITE-SECTOR-REINDEX、MI-I-SIXTH-POWER-ZEROS，约 0.4 万；
4. MI-M-PROFILE-UNIFORMITY，约 0.5 万；
5. MI-M-QUADRATIC-SIEVE（接 Axiom 的 GL），MI-I-INDEPENDENT-AMPLIFICATION，MI-I-AMPLIFIED-WITNESS-CALIBRATION，约 0.6 万；
6. MI-P-PRIME-CANCELLATION-BELOW-ONE，MI-P-PRIME-ABSOLUTE-ENDPOINT，三个 MI-P 包装，约 1.2 万（可再拆成两个）。

**拆分方法**：openai 模块按四个目录内的导入闭包行数升序排列，每 6,000 行切一刀。这个顺序是导入有向图的线性扩展，所以每一块只依赖它前面的块。

## Expansion、HighBin、D-EXPANSION（13）

| 单位 | 估计 |
|---|---|
| EX-DATA-1：D-EXPANSION、D-SUPPORT、EX-BLOCK-COUNT | 0.45 万 |
| EX-DATA-2：HB-PRESENT、HB-LABEL-HEIGHT | 0.5 万 |
| EX-BUDGET：EX-HEIGHT-BUDGET、EX-CUTOFFS，合并成一条存在性定理 | 0.05 万（并入 EX-DATA-2） |
| EX-IDENTITY-1：带标记的 Poisson 与三重 Mellin 展开（核心至今没有任何证明） | 0.65 万 |
| EX-IDENTITY-2 加 EX-TAIL | 0.6 万 |
| EX-PRINCIPAL | 0.5 万 |
| EX-CORR-LINES（新）：两族直线上的完整修正界 | 0.35 万 |
| EX-SMALL 加 EX-LARGE | 0.65 万 |
| EX-DETECTOR-1：零点检测到 spike，含饱和 | 0.6 万 |
| EX-DETECTOR-2：WitnessCover 与 BlockSource 的组装 | 0.5 万 |
| HB-EULER-INITIAL | 0.5 万 |
| HB-EULER-EXCEPTIONAL | 0.4 万 |
| HB-NORMFORM-1、HB-NORMFORM-2、HB-NORMFORM-3 | 0.5、0.5、0.25 万 |
| HB-MOVE-BOUNDARY | 0.65 万 |

EX-BUDGET 并入 EX-DATA-2 后，共 13 个单位。

**注意**
- `TInputRanges` 和 `TInputFixedBinTransfer` 里有过时常数：Z^(1/100) 应为 1/16，63/800 应为 1/50，11/12 已过时。只能当形状模板用。
- `expansionSource` 的预算要改成"由一条合并的存在定理取 `Classical.choose`"。

## 建议顺序

1. **马上可做，彼此独立：**
   - D-MESH（第一批，顺带去掉 `TargetContext` 的 sorryAx）；
   - PR-WINDOW-PIT（Codex）、DE-EULER（Codex）；
   - TH-KERNEL（先改成对一般数据陈述）；
   - MI-M-QUADRATIC-SIEVE（接 Axiom 的 GL）；
   - LOW-PHYSICAL-ASSEMBLY 中缓存里编译过的 8 个模块。
2. **然后：**
   - D-EXPANSION 与 MODELS 的联合设计；
   - Moments 共享底座 S0–S4；
   - TH-KP-DATA；
   - HB-EULER。
3. **之后**并行三条长链：逆变换链、配对引擎链、Theta 反射链。
