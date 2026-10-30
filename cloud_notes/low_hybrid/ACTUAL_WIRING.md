# 混合能量与冻结立方的实际外部理想接线

本任务的统一导入是 `HeckeSkeleton.LowHybridExterior`，递归公理检查是
`HeckeSkeleton.LowHybridExteriorAudit`。代码对接 `dtests-handoff` 的实际定义；
起始提交为 `5e4c85f172c101fd0c201219c13aa28f8b520d42`。

## 混合能量的实际陈述

固定仓库中的 `HeckeAxiom.ArithmeticChoice K S₀ root12 σ`，记其排除素集为
`S`，其 `ThetaArithmeticData` 为 `D`。所有变量均为 `ExteriorIdeal K S`。
记

\[
\chi_J(I)=\operatorname{idealSymbol}(J,D.\operatorname{generator}(I)).
\]

`LowHybrid.Exterior.row` 的定义就是

\[
R_k=\sum_{P\in\mathcal P}\frac{a(P)}{\sqrt{N(P)}}
  1_{(P,k)=1}\sum_{n\in\mathcal N}\sum_{b\in\mathcal B}
  \beta(n,b)\chi_k(nb)^3\chi_P(n)^{-2}1_{(P,b)=1}.
\]

其中两个互素指示函数使用底层理想的 `IsCoprime`，范数使用
`exteriorNorm`，乘法使用 `exteriorMul`。`energy` 是原行的平方范数和。

`LowHybrid.Exterior.hybrid_energy` 证明：对于每个 `ε>0`，存在 `C>0`，
随后对任意 `R,N,B,L≥1`、有限行/标记/列/立方集合及原始系数，若行、标记、
列分别平方自由且范数不超过 `R,L,N`，立方变量的范数不超过 `B`，
并且 `‖β(n,b)‖≤1`，则

\[
\sum_k|R_k|^2\le
C(RNBL)^\varepsilon(R+NB)B
\{N+L+(NL)^{2/3}\}\sum_P\frac{|a(P)|^2}{N(P)}.
\]

`hybrid_energy_with_beta_mass` 允许任意复系数 `β`，右边额外乘以原有限支撑上的
`betaSquaredMass`，即真实的最大平方范数（空支撑取零）。
`hybrid_energy_bounded` 在 `‖a(P)‖,‖β(n,b)‖≤1` 时给出无系数质量的展示式。
三个定理都先选择常数，再量化全部尺度、有限集合和系数。

`completed_quadratic_energy_bounded` 另给出实际原双和的独立引理 4.6：

\[
\sum_k\left|\sum_{n,b}\beta(n,b)\chi_k(nb)^3\right|^2
\le C(RNB)^\varepsilon(R+NB)NB.
\]

其证明只使用二次筛。任意立方变量 `b` 保留原来的支撑条件。

## 基础算术数据已经逐项构造

| 文件 | 实际构造和识别 |
| --- | --- |
| `LowHybrid/ExteriorArithmetic.lean` | 外部理想的交换幺半群，乘法与 `exteriorMul` 一致；限制真实理想素分解得到外部素坐标及逆向素幂乘积；平方自由、互素、整除、范数和线性计数的字典。 |
| `LowHybrid/ExteriorSymbol.lean` | 真实 `idealSymbol J (D.generator I)` 的乘法律、单位值、互反、模界及精确六次幂掩码律；单素位与 `primeEvaluation` 的等式。 |
| `LowHybrid/ExteriorSieve.lean` | 从已有 `HeckeAxiom.quadratic_sieve_bound`、`CubicSieve.Complete.targetBound` 构造两筛输入；从实际算术选择构造 `AllowedGeneratorInput`。 |
| `LowHybrid/ExteriorEnergy.lean` | 模型能量与原实际能量的等式，以及上述四个实际能量定理。 |

生成元的乘法误差始终按 `AllowedGeneratorInput.multiplicative` 的六次 S-unit
处理，并由实际六次符号不变性消去。六次幂律保留共同素位的零值：

\[
\chi_J(I)^6=1_{\operatorname{IsCoprime}(J,I)}.
\]

`allowedInput` 由算术选择的乘法与互反定理，以及
`AllowedGeneratorInput.of_multiplicative_reciprocity` 构造。两筛直接调用其实际
提供者，避免把顶层骨架中的其他义务带入这些能量定理。

## 冻结立方也使用实际对象

| 文件 | 实际构造和识别 |
| --- | --- |
| `LowFrozenCube/ExteriorData.lean` | 从实际有限素集、`Fin 6` digit 和最低指数理想构造完整 `FrozenReduction.Data`；`ofReflectionIndex` 直接取原 `ReflectionIndex` 的数据。 |
| `LowFrozenCube/ExteriorLocalBounds.lean` | 从已证有限域 Gauss 和公式推出首系数、正赋值 prefactor 和零赋值表的三个平方范数界。 |
| `LowFrozenCube/ExteriorLocalTable.lean` | 沿实际剩余域同构重索引 `thetaGamma`；识别 `localTau`、`localWeylScalar` 与冻结普通表，证明实际整个表乘积及全部 `PrimitiveLocalBounds`。 |
| `LowFrozenCube/ExteriorPhases.lean` | 普通素位相位与原 `primeEvaluation`、`localWeylExponent` 的等式；混合相位严格改写为 `reflectedTerm` 中两个真实 `idealSymbol` 因子，保留两个互素掩码。 |
| `LowFrozenCube/ExteriorBounds.lean` | 实际对象的统一加权原行界、源能量账本、变化冻结支撑的全族小幂界及终端节省。带 `actual` 的入口内部代入真实局部标量并证明局部界。 |

`uniform_actual_family_source_energy_subpower` 和
`uniform_actual_family_source_energy_power_saving` 的常数先于全部冻结支撑、digit、
最低指数、有限原行和系数选择。它们对每个冻结对代入真实局部表，因此不要求调用方
重新提供三个局部 Gauss 界。长度、导子、annulus、支撑装配和共同核的标量预算在
定理中明确列出，供 `Principal.completedMarkedEnergy` 的反射能量组装使用。

## 与后续反射能量任务的边界

本任务提供混合能量、冻结立方及其实际算术/局部相位字典。
`Principal.completedMarkedEnergy` 还要把原反射级数、共同 Mellin 核及其支撑和
尺度预算组装到这些有限能量入口；这一调用方的整体分析属于
`LOW-REFLECTED-ENERGY`。接线文件给出可直接使用的实际对象定理和明确的预算参数。

## 环境和验证入口

固定环境为 Lean `4.35.0-rc3`（`470d5ce1400764999581fd26d5d72b00d990b0f4`）和
Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。
标准验证命令：

```sh
lake build HeckeSkeleton.LowHybridExterior
lake build HeckeSkeleton.LowHybridExteriorAudit
```

`LowHybridExteriorAudit` 对所有新增接线命名空间中的定理和定义递归调用
`Lean.collectAxioms`。允许集合为 `propext`、`Classical.choice`、`Quot.sound`，
任一额外公理都会令该模块编译失败。逐入口也保留了 `#print axioms`。
最终实际执行结果另记在 `EXTERIOR_VERIFICATION.md`。

为控制实际依赖体积，部分 `vendor/flt/FLTReuse` 文件的 `import Mathlib`
收窄为实际需要的导入。`EXTERIOR_IMPORTS.json` 记录每个导入头及正文校验值；
这些文件的已有定义和证明正文逐字保留。

本接线由 OpenAI GPT-6 Astra Pro 辅助实现（AI-assisted）。
