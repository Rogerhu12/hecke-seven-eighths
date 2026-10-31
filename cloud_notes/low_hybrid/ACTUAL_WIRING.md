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
| `LowFrozenCube/ExteriorReflection.lean` | 真实平方自由素乘积；原反射行、标记、列系数的分离；`frozenOmega` 的实际局部表分解；原 `reflectedTerm` 与真实 `rawSourceTerm` 的逐项严格等式，保留不活动标记因子、两项平方根权重和原 Mellin 核。 |
| `LowFrozenCube/ExteriorCoefficientBounds.lean` | 从实际 Gauss 和、六次符号及外部未分歧 Hecke 特征证明原反射系数的范数界；`reflectionSourceBlock_annularSupport` 自动填入全部系数和相位条件，调用方只提供支撑、平方自由性和范数截断/annulus 数据。 |
| `LowFrozenCube/ExteriorBounds.lean` | 实际对象的统一加权原行界、源能量账本、变化冻结支撑的全族小幂界及终端节省。带 `actual` 的入口内部代入真实局部标量并证明局部界。 |

`uniform_actual_family_source_energy_subpower` 和
`uniform_actual_family_source_energy_power_saving` 的常数先于全部冻结支撑、digit、
最低指数、有限原行和系数选择。它们对每个冻结对代入真实局部表，因此不要求调用方
重新提供三个局部 Gauss 界。长度、导子、annulus、支撑装配和共同核的标量预算在
定理中明确列出，供 `Principal.completedMarkedEnergy` 的反射能量组装使用。

`reflectionSourceBlock` 将原反射公式的实际系数填入有限源块，
`reflectionSourceBlock_localBounds` 直接证明其局部条件。
`reflectedTerm_eq_rawSourceTerm` 使用原 `MarkedDatum`、`ReflectionIndex`
和真实 `AllowedGeneratorInput`；原有互素字段消去这一个合法反射指标的两个掩码。
该等式没有另加反射能量估计或正常形假设。

系数范数的额外字符条件恰为原反射输入中的 `exterior_unramified`。
`HeckeCharacter` 的值已经位于单位圆，所以这里没有另设 unitary 假设，也没有
将相位或基系数的范数界当作未证输入。

### 冻结出口的指数和显式预算

记

\[
\kappa=-\frac{\max(T-v-3\ell,0)}2,\qquad
s(v,z)=\min\{v,z,(v+z)/3\},
\]
\[
E_{\rm ref}=\frac O2+\max(H,v+\ell)-S_{\rm exp}-B+z-s(v,z)-\ell+\kappa.
\]

对每个 `ε>0`，`uniform_actual_source_energy_ledger` 先选择统一的 `C>0`，
随后对全部冻结数据、尺度及有限源块给出

\[
Z^{O/2} E_{\rm block} Z^\kappa
\le C Z^{E_{\rm ref}+\varepsilon(H+v+\ell+z)}.
\]

这里 `Z≥1`，`H,v,ℓ,z≥0`；源块满足实际 `AnnularSupport`，并且
`Z^(Sexp+B)≤N(chargeIdeal)`。局部表由 `withActualLocalTables` 代入真实值，
三个局部 Gauss 界由 `primitiveLocalBounds` 证明。

对固定 `W>0`、`ε>0`，`uniform_actual_family_source_energy_subpower` 给出
整个原始行族的统一结论

\[
E_{\rm family} Z^\kappa\le C Z^{E_{\rm ref}+\varepsilon}.
\]

除逐块的 annulus 和 `chargeIdeal` 条件外，全族入口明确要求 `O≥0`、
`(H+v+ℓ+z)+(O+Rrad)≤W`，每个原行的强幂因子范数不超过 `Z^O`，
以及 `N(fromSupport base)≤Z^Rrad`。`FrozenFamilyAlignment` 要求每块的
坐标、`base∪support(pow)`、原行集合及 `pow/sup` 数据吻合；其中没有目标能量
等式或估计。强幂计数成本 `O/2` 已在 `Eref` 中，全族左侧不再重复乘这一因子。

`AnnularSupport` 中保留的几何条件包括：原行位于给定有限范数球，剩余行范数不超过 `Z^H`，
标记平方自由、避开完整冻结支撑且范数不超过 `Z^z`，列平方自由且避开
`ordinary`、其范数位于 `[Z^v/2,Z^v]`，以及完整立方变量的范数位于
`[Z^ℓ/2,Z^ℓ]`。输入第一分量支撑在 `ordinary` 内，第二分量避开 `ordinary`。
对实际反射块，`reflectionSourceBlock_annularSupport` 从原始未分歧字符条件
自动填入系数与相位范数界，调用方只需提供这些支撑和尺度条件。

最后，`uniform_actual_family_source_energy_power_saving` 在同一全族条件上，
加入声明中逐项列出的非负性、导子和终端裕度条件，得到

\[
E_{\rm family} Z^\kappa\le C Z^{F-c/4}.
\]

具体尺度关系为 `F=N+V`、`Nstar=N−3bh`、`V,bh≤δ`、`z≤z0`、`H≤M−O`，
两个裕度是 `c≤F−M−Q−z0` 和 `c≤4F−3M−6z0`；导子比较为
`T−Sexp−B≤2M−O+Q+V−Nstar+2z`，保留区间为 `v+3ℓ≤T+τ`，
最后要求 `δ≤c/100`、`τ≤c/8`、`ε≤c/4`。
这些入口中的 `Z^κ` 是明示的共同平方标量。把原 Mellin 核控制成这一标量，
以及全局反射级数的汇总，属于下述后续调用方的工作。

## 与后续反射能量任务的边界

本任务提供混合能量、冻结立方及其实际算术/局部相位字典。
`Principal.completedMarkedEnergy` 还要把原反射级数、共同 Mellin 核及其支撑和
尺度预算组装到这些有限能量入口；这一调用方的整体分析属于
`LOW-REFLECTED-ENERGY`。接线文件给出可直接使用的实际对象定理和明确的预算参数。

`reflectedTerm_eq_rawSourceTerm` 是逐字保留原 `mellinReflectionKernel` 的代数等式。
将该核接到真实正向复位轮廓时，还须遵守最新基线的
[theta-local 径向符号修正](https://github.com/Rogerhu12/hecke-seven-eighths/blob/556fd33068f5914887e850ed2dce9e9272d9b8c2/cloud_notes/theta_local/WIRING_REPORT.md)：原乘子的 Gamma 商为
`archGammaProduct K θ s / archGammaProduct K θ⁻¹ (-s)`，真实正向轮廓需要
`archGammaProduct K θ⁻¹ s / archGammaProduct K θ (-s)`。
新增的 `HeckeSkeleton.ThetaLocal.Project.directReflectionMultiplier` 对此作了适配；
所有复位满足 `archRadial K θ v = 0` 时，也可使用该模块已证明的原乘子相等式。
这一复位 Mellin 识别属于下游组装；本任务的有限位字典与能量不等式保持原有陈述。

### `Principal` 中的具体参数

`Principal` 使用的就是同一个 `axiomChoice K c`：`places K c` 定义归约为该
选择的 `places`，`(probeData K c).arithmetic` 定义归约为该选择的 `thetaData`。
不需要再选择一份算术数据或增加生成元相等假设。在 `HeckeSkeleton` 命名空间、
沿用原有 `K`、`c`、`ε` 和 `hε : 0 < ε` 时，统一常数的调用形状为：

```lean
obtain ⟨Cmix, hCmix, hmix⟩ :=
  LowHybrid.Exterior.hybrid_energy (axiomChoice K c) ε hε

obtain ⟨Cledger, hCledger, hledger⟩ :=
  LowFrozenCube.Exterior.uniform_actual_source_energy_ledger
    (axiomChoice K c) ε hε

obtain ⟨Cfamily, hCfamily, hfamily⟩ :=
  LowFrozenCube.Exterior.uniform_actual_family_source_energy_subpower
    (axiomChoice K c) W ε hW hε
```

这里最后一个调用另有 `hW : 0 < W`。实际反射字符取原来的
`thetaPeriod K (places K c) (probeData K c) (targetCharacter K c)`；
`hreflection.exterior_unramified` 恰好提供 `reflectionSourceBlock_annularSupport`
所需的未分歧条件。`hreflection.allowed_generators` 与
`ExteriorSieve.allowedInput (axiomChoice K c)` 是同一个 `Prop` 的证明，
不会造成算术数据差异。这些片段说明后续组装的参数对应关系；本任务的统一导入
和审计不导入尚有其他义务的 `Principal` 骨架。

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

为控制实际依赖体积，`AllIdealTransfer` 的总入口改为四个实际使用的提供者。
`EXTERIOR_IMPORTS.json` 记录该导入头及正文校验值；已有定义和证明正文逐字保留。
所有 FLT 文件保持原样，沿用其完整 Mathlib 导入。

本接线由 OpenAI GPT-6 Astra Pro 辅助实现（AI-assisted）。
