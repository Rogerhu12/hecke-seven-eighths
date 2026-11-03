# 从 31/32 到 7/8：形式化路线图

对照对象是论文 [A seven-eighths zero-free half-plane for unitary Weil L-functions](https://hexagonmath.org/2610.00216v1)
（hexagon 2610.00216v1，2026-10-13），依据其 LaTeX 源码的证明大纲与附录 `app:transfer-map`。
Q、P 分别指 OpenAI 的 quasi-Riemann 预印本（2026-09-30）与 primitive-roots 预印本（2026-10-04）。

## 两个指数的来源

| | 归一化 | 探针（theta 侧）界 | 结果 |
|---|---|---|---|
| 上游（Cureton–Thorner，已形式化） | `Z^{61/100}` | `Z^{287/800+ε}`：一次 Cauchy–Schwarz，Gram 能量 `C/Y` 乘反射行均方 `Z^{438/400}`，`Y = Z^{151/400}` | 61/100 + 287/800 = **31/32** |
| 论文 | `C(s) = s − 11/16` | `Z^{3/16+ε}`：标记反射 + 完整加法 Gram 估计 | 11/16 + 3/16 = **7/8** |

上游的尺度参数都是固定常数（`Moments/Probes/Poisson/Scales.lean`），没有 Euler 侧的矩估计。
论文另需 Euler 侧：零点检测器 + 两个规范矩（逆矩、`κ = 2B − 1 ∈ (3/4, 1]` 的四阶矩）给出固定增益 `η₀`，
最后用 Mellin 闭合排除 `B > 7/8`。

## 论文附录的十步，逐项对照

| 步骤 | 论文依赖 | 上游 AxiomMath | 本仓库主库/骨架 | 状态 |
|---|---|---|---|---|
| 1 生成元与算术索引 | Q；P §3 | `SArithmeticData`、`AllowedGenerators`、`actualComplement` | 骨架 D-ARITHMETIC、AR-ALLOWED-*；`GeneratorInputs`（隔离验证） | 上游有，缺类型字典 |
| 2 Gauss 校准与互反 | P 引理 3.4 | `GaussCorrectionOutput`（Λ、G、η 与素理想 Gauss 律）、六次 Hilbert 互反 | 骨架 D-SIGNALS、AR-* 七项校准 | 上游有，缺 idele 类群字典与平方自由 CRT 组装 |
| 3 轨道 Poisson 与完整相关 | Q §§13, 17–18 | 带限 Poisson Gram majorant、商测度轨道积分（固定参数） | 骨架 GR-10、GR-12 子项 | 部分 |
| 4 theta 与标记反射 | Q §14；P §§5–6 | KP 覆盖、例外表示、`CertifiedPacket`（仅主特征、固定 Gaussian、无标记） | 骨架 TH-KP-DATA、TH-MARKED-REFLECTION、TH-KERNEL-* | **缺**：推广到固定无穷型与标记 |
| 5 反射范数与短逆终端 | Q §§14, 17；GL、BGL 大筛 | 加法大筛、二次族存在性 | 骨架 MI-M-QUADRATIC/CUBIC-SIEVE、LOW-REFLECTED-ENERGY | **缺**：两个数域大筛 |
| 6 两次逆变换与初始化 | Q §17 | 无 | 骨架 MI-I-CANONICAL-RECURSION 等 | **缺** |
| 7 普通反射与素数前提 | Q §18.2 | 射线特征 L 函数的延拓与 Gamma 因子 | 骨架 MI-P-PRIME-* | 部分 |
| 8 四阶矩递推与例外行 | Q §§18.2–18.8 | 无 | 骨架 MI-P-POSITIVE-SLOTS-*、MI-P-ZERO-SLOT | **缺**：最难的一块，且要推到 κ ≤ 1 |
| 9 物理估计与 Euler 补偿 | Q §§5–16；P §7 | 探针、主项比较、零点检测（固定尺度） | 主库 PhysicalProbe*、RowEuler（负 w 修复）；骨架 HB-*、EX-*、PR-*、GR-12 | 部分；强 Gram 界缺 |
| 10 指数比较与闭合 | Q §§19–20、命题 2.1 | Mellin 零点转移（31/32） | 主库 TIP 条件闭合、`MellinZeroDetector` | 已有（条件形式） |

另外两层：

- **阿贝尔下降**（F(ζ₁₂)/F）：上游只对 Dedekind ζ 做了阿贝尔扩张的零点转移；一般连续特征的下降在骨架 DE-* 与缓存候选里。
- **Weil 群推广**（Brauer 归纳）：不在当前形式化目标 `GeneralHeckeSevenEighths` 之内。

## 关键路径

上游能直接提供第 1、2 步（算术层），第 3、7、9、10 步有可用部件。决定成败的是：

1. 第 4 步：把 KP 标记反射推广到固定无穷型（包括无穷阶特征）；
2. 第 5 步：数域上的二次大筛与 BGL 三次大筛；
3. 第 6、8 步：Q §17 的逆变换递推与 Q §18 的四阶矩递推，并推到 κ ≤ 1；
4. 完整的强 Gram 界（论文的 `prop:additive-gram`，骨架 GR-12）。

论文附录写明第 6、8 步对 Q 是"按位置引用，不重写"，所以这几步的形式化需要先把 Q 对应章节的论证
在一般数域上逐条写出。
