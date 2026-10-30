# LOW-HYBRID / LOW-FROZEN-CUBE 第二轮接线说明

## 1. 本轮范围与核查状态

本文件替代上一轮 `deliverable/WIRING_NOTES.md` 中关于原行正常形、规范支撑、除数损失和调和损失尚待证明的说明。这些内容本轮已经写成完整的 Lean 构造和证明链；不是继续交给实际项目的接口假设。

**LOW-HYBRID 主链已通过精确版本编译与主定理公理核查。** 环境为 Lean **4.35.0-rc3**、Mathlib **0493595ecd5da8ef14742febab99728f98e948e8**。`hybrid_energy`、`hybrid_energy_with_beta_mass`、`hybrid_energy_bounded` 及其完整构造链均已编译通过；三个主定理的 `#print axioms` 输出均只有 `propext`、`Classical.choice`、`Quot.sound`。这包括用户的无系数质量公式和任意 `β` 的真实最大平方质量公式。

**LOW-FROZEN-CUBE 的完整加权原行出口、统一源能量及终端、实际变化支撑下的全行聚合，也已通过指定版本编译与全包公理核查。** 统一入口先选择常数，再量化全部冻结 `Data`；`UniformAggregateSource` 允许反射支撑随实际强幂部分变化。`UniformAggregateTerminal` 将固定长度预算内的全部小幂合为一个给定 `ε`，并给出全族终端节省。新增独立引理 4.6 入口同样已通过。最终 `LowAudit` 遍历两个新命名空间的 **955 个定理**，包括内部辅助定理，全部公理依赖均属于标准三条。

`TASK.md` 的“云端运行须知”明确允许在项目自有传递依赖不可获得时，交付只依赖 Mathlib 的自包含模块，并报告实际项目接线位置。本轮按该条款实现：新模块不导入缺失的 `HeckeGeneral`、`HeckeAxiom` 或 `DedekindZetaZeroFree` 文件，不声称已经在用户完整工程中编译通过。

下文 `project/` 指输入压缩包内同名目录。所有用户原文件与 `openai_reference/` 均保持只读。本文件列出的“包内可见”是指看到了实际声明或调用，不表示其未随包提供的传递依赖已在这里重新构建。

## 2. 本轮已经在代码中构造的主链

| 原来的接线缺口 | 本轮代码及实际内容 |
|---|---|
| 原始 `hybridRow` 到 `D,r` 块的逐行等式 | `NormalFormAlgebra`、`NormalFormFinite`、`NormalForm`、`NormalFormKernels`。两次完整 Möbius 展开、`P=DQ`、`k=Drλ`、`n=rcm`、`b=rcht²` 的有限重索引均在证明内部完成；`NormalForm.Arithmetic.hybridRow_eq_weightedBlocks` 的结论是原行的严格复数等式。 |
| 抽象完成平方数据的真实实现 | `PrimeArithmetic.arithmetic` 和 `PrimeArithmetic.completion`。从 `coords : A ≃* Multiplicative (ι →₀ ℕ)` 构造素支持、平方自由除数、Möbius 系数、商和规范拆分。Möbius 公式与逐点重建都由坐标证明。 |
| 平方自由性、原始范数支撑、两种好产品集合 | `CanonicalSupport`、`CanonicalInputs`。`canonical_finite_inputs` 从原始行、标记、列和立方支撑自动构造有限截断、矩形支撑、`goodPairs`、`goodMC` 及全部 `FiniteInputs` 字段。 |
| 块中两条任意系数算子界 | `BlockAdmissible.weightedBlock_admissible_from_sieves` 位于 `NormalForm.Arithmetic`。它直接消费给定的二次、三次筛，完成二次方向转置、商行的单射拉回和两个不同产品纤维的估计。没有把块能量或算子界当作新的算术输入。 |
| 非零立方支撑预算 | `NormalFormSupport.blockBeta_cube_support` 与 `BlockAdmissible.blockBeta_budget`。实际 `beta` 非零时继承 `N(r)N(c)N(h)N(t)²≤B`，再推出加权预算。 |
| 原始 `D` 列质量 | `ColumnMass.columnMass_div_eq`、`columnMass_sum_le_divisors` 位于 `NormalForm.Arithmetic`。准确保留 `1/N(D)`，将抽取后的列质量改写回原标记质量，每个标记只付自己的除数个数。 |
| 除数任意小幂 | `SquarefreeDivisors`、`DivisorEnvelope`、`PrimeDivisorBounds`、`ArithmeticLosses`。从素坐标、乘法范数与线性范数计数构造实际除数包络并证明小幂界；无需另向上游索取一个除数渐近式。 |
| 调和任意小幂 | `Counting`、`CountingBridge`、`ArithmeticLosses`。从正自然数范数的线性计数，用有限分部求和推出 `H(X)≤C(1+log X)`，再得到任意小幂。无需猜测或调用一个未见源码的“理想调和和定理”。 |
| 所有损失统一吸收 | `NaturalLosses`、`NormalFormUniform`。自然截断 `D,r≤K` 的损失为 `Δ(K)²Δ(NB)Δ(N)Δ(L)(KNB)^η(NL)^η H(B)³H(N)H(K)`；取 `η=ε/12` 统一吸收，所有常数先于尺度和系数选定。 |
| 原始能量的总定理 | `HeckeSkeleton.LowHybrid.hybrid_energy`，在 `HybridEnergy.lean`。它内部构造上述全部数据，左侧就是 `Rows.lean` 中的 `hybridEnergy`；入口没有正常形等式、`FiniteInputs`、除数界、调和界、块算子界或目标能量界。 |
| 任意 `β` 与无系数质量的任务式 | `Homogeneity` 构造有限支撑上的真实 `betaSquaredMass`，空集取零。`Corollaries` 中 `hybrid_energy_with_beta_mass` 给任意复系数质量版；`hybrid_energy_bounded` 在 `|a|,|β|≤1` 时消去全部系数质量。 |

表中采用“文件名 + 短名”的写法；文件名不自动成为 Lean 命名空间。尤其 `ColumnMass`、`BlockAdmissible` 的相关定理实际位于 `HeckeSkeleton.LowHybrid.NormalForm.Arithmetic`。

无系数质量的最终陈述形状为

\[
E(a,\beta)\le C_\varepsilon(KNBL)^\varepsilon
(K+NB)B\{N+L+(NL)^{2/3}\}.
\]

任意系数版保留

\[
\left(\sum_P\frac{|a(P)|^2}{N(P)}\right)
\max_{(n,b)\text{ 在原支撑}}|\beta(n,b)|^2.
\]

两版的常数均在四个尺度、所有有限集合及系数函数之前选择。主定理不绑定 `TargetContext`。

## 3. 现在剩余的实际项目字典

剩余工作是把用户完整工程的对象与上述自包含主定理的基础数据识别。完成这些字典后，不必重新证明正常形、产品支撑、两条筛的组合、除数损失或调和吸收。

| 自包含主定理的基础数据 | 实际项目应提供的识别 |
|---|---|
| `A` 及 `CommMonoid A` | 取 `A := ExteriorIdeal K S`，证明使用的乘法与包内 `exteriorMul K S` 一致。包内给出了显式乘法，不能仅据此断言完整工程已经注册了同一个幺半群实例。 |
| `coords : A ≃* Multiplicative (ι →₀ ℕ)` | 以外部素理想为坐标索引，给出真实非零外部理想的素指数等价；证明其正向赋值与逆向有限素乘积互逆。这里需要的是标准唯一分解字典，不是一个最终正常形假设。 |
| 坐标 `Squarefree` 与 `Coprime` | 分别识别为实际底层理想的 `Squarefree I.val.val` 和 `IsCoprime I.val.val J.val.val`。坐标定义的支撑及商、完成平方随后全部自动适用。 |
| `normI : A →* ℝ`、`q : A → ℕ`、自然性及 `1≤q` | 取 `q I := I.val.val.absNorm`，`normI I := exteriorNorm K S I`；用非零理想性质和范数乘法性建立字典。 |
| `LinearNormCounting q Ccount` | 将普通理想的线性计数沿外部理想到底层理想的单射转移。自然数截断 `N=0` 由范数至少一处理；正截断调用真实计数提供者。 |
| `symbol : A → A → ℂ` | 取 `symbol J I := idealSymbol K S D J (D.generator I)`，证明两变量乘法性和带共同素位零值的六次幂掩码律。 |
| `QuadraticSieveInput`、`CubicSieveInput` | 将包内已给两条筛按实际 `normI`、平方自由谓词和符号字典传入。二次方向转置在新模块内已证明；三次系数与指数参数的顺序只需逐项对齐。 |

上述符号字典最需要谨慎核对。`idealSymbol` 对元素分子的乘法性，不能直接当作 `I ↦ idealSymbol J (D.generator I)` 对理想的乘法性。允许生成元一般只在六次 S-unit 误差意义下乘法；必须先证明符号消掉这个误差。

主 `LOW-HYBRID` 证明不额外要求全符号互反作为输入：它接受两个变量的乘法律及六次幂掩码律，二次筛方向由有限矩阵转置处理。实际项目若用全互反从一个变量的乘法性推出另一个变量的乘法性，仍须核对那条实际互反律的完整适用范围。冻结相位的外部识别也应沿其实际所需的符号律完成。

## 4. 输入包中实际可见的名称

### 4.1 原始对象及原系数

文件 `project/HeckeGeneral/Analysis/GlobalThetaData.lean`，命名空间 `HeckeGeneral.ThetaSkeleton.Global`。

| 可见名称 | 包内实际内容 |
|---|---|
| `exteriorMul` | 外部理想的二元乘法，以底层非零理想乘法并附外部性证明定义。 |
| `completedIdeal` | 用显式乘法组成完整指数 `c*n³`。 |
| `exteriorNorm` | 定义为底层理想绝对范数转成实数。 |
| `idealSymbol` | 以 `sIntegerSexticIdealEvaluation` 定义的实际六次符号；第二个参数是 `S.integer K` 中的元素。 |
| `wholeIndexMask` | 完整指数与 puncture 互素，且每个标记素理想整除完整指数。 |
| `completedTerm`、`completedThetaSum` | 实际原系数和理想和；原系数包含平方自由、完整指数掩码及范数分母。 |
| `FiniteMellinData`、`finiteMellinFactor`、`mellinReflectionKernel` | Mellin 数据和核的定义。 |
| `FiniteMellinAdmissible`、`MellinKernelInput` | 核可和性、移线及导数界等义务的结构。看到结构不等于已看到完整实例提供者。 |

### 4.2 允许生成元

文件 `project/HeckePort/CenteredMoment/Generator.lean`，命名空间 `HeckePort.CenteredMomentGenerator`。

| 可见名称 | 包内实际内容 |
|---|---|
| `IsExterior`、`toExterior` | 普通理想的外部性条件及外部理想构造。 |
| `isExterior_mul_iff`、`isExterior_top`、`toExterior_mul` | 外部性的乘法封闭、单位及表示相容性。 |
| `SixthPowerTrivial` | 固定剩余特征对六次 S-unit 幂取值一的条件。 |
| `generatorCharacter`、`generatorCharacter_of_not`、`generatorCharacter_bot` | 允许生成元上的求值及非外部处的零延拓。 |
| `generatorCharacter_mul`、`generatorCharacter_top` | 在 `AllowedGeneratorInput` 和 `SixthPowerTrivial` 下证明乘法性及单位值。 |
| `generatorIdealHom`、`generatorIdealHom_apply` | 封装上述普通理想上的幺半群同态。 |
| `norm_mulChar_le_one`、`norm_generatorCharacter_le_one` | 实际特征范数界。 |
| `tsum_exterior_eq` | 外部理想和与普通理想上外部零延拓和的转换。 |

`generatorCharacter_mul` 的源码明确调用 `hD.multiplicative` 得到六次 S-unit 误差，再用 `SixthPowerTrivial` 消掉它；不能改写为未经证明的生成元严格乘法公式。把 `idealSymbol` 识别为这里的剩余特征求值仍属于实际符号字典。

### 4.3 两个筛

| 文件和可见名称 | 接线含义 |
|---|---|
| `project/HeckeAxiom/QuadraticSieve.lean`：`HeckeAxiom.quadratic_sieve_bound` | 对一个 `ArithmeticChoice` 的实际符号三次幂给出二次筛。 |
| 同文件：`thetaData_generator_eq_representative`、`exterior_cop`、`exterior_ne_bot`、`exists_quadraticFamily_eq_symbol` | 实际允许代表元与二次 Kummer 家族的对照证明。 |
| `project/CubicSieve/ExteriorSieve.lean`：`CubicSieve.ExteriorSieve.TargetAt`、`TargetBound` | 任意系数、平方自由支撑、范数截断和整数指数 `±2` 的三次筛接口。 |
| 同文件：`underlyingIdeal`、`underlyingIdeal_injective`、`finite_cutoff`、`cutoff`、`mem_cutoff`、`cutoff_mono`、`cutoff_card_le_ideal_count` | 外部理想到普通理想的单射及真实有限范数截断。 |
| `project/CubicSieve/Complete.lean`：`CubicSieve.Complete.targetBound` | 三次筛的已有提供者，带实际算术数据和 `AllowedGeneratorInput`。 |
| `project/HeckeSkeleton/Moments.lean`：`QuadraticSieveBound`、`CubicSieveBound`、`moment_quadratic_sieve`、`moment_cubic_sieve` | 面向 `TargetContext` 的接口和实例；可作为最终薄特化层的调用示例，通用主定理不依赖该上下文。 |

### 4.4 素支持、Möbius 与线性计数

| 文件及命名空间 | 已核对的实际名称 |
|---|---|
| `HeckePort/CenteredMoment/IdealMobius.lean`；`HeckePort.IdealMobiusDivisorSum` | `primeSupport`、`support_prime`、`support_product_ne_zero`、`factors_support_product`、`squarefree_support_product`、`support_product_dvd`、`moebius_support_product`、`support_product_injective`、`squarefree_divisor_support`、`squarefree_support_product_self`、`squarefree_divisors_eq_image`、`sum_moebius_divisors`、`norm_ideal_moebius_le_one`。 |
| `HeckePort/CenteredMoment/Mask.lean`；`HeckePort.CenteredMomentMask` | `ideal_coprime_mobius`、`tsum_ideal_divisible`、`masked_ideal_sum_eq`、`annular_ideal_sum_summable`、`masked_plain_ideal_sum`、`polynomial_mask_divisor_bound`。 |
| `HeckePort/CenteredMoment/Counting.lean`；`HeckePort.CenteredMomentCounting` | `idealCountConstant`、`one_le_idealCountConstant`、`card_le_idealCountConstant`、`norm_tsum_ideal_ball`。 |

本轮总定理直接从素坐标和线性计数重新构造所需有限 Möbius 展开、平方自由除数界和调和界。上述包内 Möbius、除数入口可用于验证实际字典或选择另一条项目接线，但已经不是总定理要求额外传入的未证损失字段。

## 5. 调用点可见、完整定义未随包提供：逐项需核对

以下只列本次实际接线有关的上游名字。全限定名未由包内信息确认时保留原简名；本轮自包含源码没有引用这些未见定义的名字。

| 名称 | 可见依据 | 仍需在完整项目核对的内容 |
|---|---|---|
| `ExteriorIdeal`、`ExteriorPrime` | `GlobalThetaData.lean` 等使用。 | **需核对**完整定义、幺半群实例、外部性及非零证明接口。 |
| `ThetaArithmeticData`；字段 `generator`、`generator_ne_zero`、`root6`、`primitive6`、`embedding`、`away_six` | `GlobalThetaData.lean` 的实际调用。 | **需核对**字段完整类型与符号定义的一致性。 |
| `AllowedGeneratorInput` | `Generator.lean`、筛文件使用。 | **需核对**完整结构、命名空间和实例提供者。 |
| `AllowedGeneratorInput.multiplicative` | `Generator.lean` 的 `hD.multiplicative` 调用。 | **需核对**六次 S-unit 误差的确切等式；不替换成严格生成元乘法。 |
| `AllowedGeneratorInput.generator_eq_sixth_power_of_ideal_eq_one` | `generatorCharacter_top` 的调用。 | **需核对**单位理想表示和参数。 |
| `AllowedGeneratorInput.reciprocity` | `TASK.md` 明确列为互反入口。 | **需核对**完整六次符号互反及共同素位零值；包内没有该定义。 |
| `sIntegerSexticIdealEvaluation` | `GlobalThetaData.idealSymbol` 的定义。 | **需核对**两变量乘法、六次 S-unit 不变性、六次幂掩码及共同素位零值的实际已证接口。这里不猜对应定理名。 |
| `ArithmeticChoice`；`.thetaData`、`.idealSymbol_eq`、`.idealSymbol_reciprocity` | `HeckeAxiom/QuadraticSieve.lean`。 | **需核对**缺失的 `HeckeAxiom.SexticSymbolDictionary` 中的完整结构和定理。 |
| `exteriorEquiv`、`recipeGenerator_spec`、`recipeOfContext` | 同文件的允许代表元对照证明。 | **需核对**定义、类型及所选算术数据。 |
| `KummerSquarefreeMembers.chooseRepresentative` | 同文件实际调用。 | **需核对**代表元构造和 `.integral`、`.radical_eq` 的类型。 |
| `RMKummerFamily.exists_actualKummerFamily`、`rm_hgl_oriented_masked` | 二次筛提供者的实际调用。 | **需核对**未提供的上游依赖及最终公理依赖；若复用既有筛，不需在本任务重证其内部分析。 |
| `CubicSieve.ExteriorKernel.kernel_reciprocity` | `ExteriorSieve.lean` 的调用。 | **需核对**整数指数范围；二次幂核互反不能直接充当全六次符号互反。 |
| `idealDivisors`、`mem_idealDivisors` | `IdealMobius.lean`、`Mask.lean`。 | **需核对**`DivisorFinsets` 的实际完整命名空间、零理想约定和成员条件。 |
| `ideal_divisor_count_le_rpow` | `Mask.lean` 调用 `DivisorEpsilonBounds`。 | **需核对**参数、常数先于尺度的量词顺序；本轮新总定理不依赖此名字。 |
| `exists_ideal_count_bound`、`boundedNormIdeals`、`mem_boundedNormIdeals` | `Counting.lean` 实际使用；`ExteriorSieve.lean` 也使用带 `DedekindZetaZeroFree.LargeSieve` 前缀的入口。 | **需核对**计数的零理想约定、范围与常数。外部理想有正范数，调和和不包含零范数项。 |
| `DedekindZetaZeroFree.LargeSieve.finite_ideals_absNorm_le` | `ExteriorSieve.finite_cutoff`。 | **需核对**完整截断有限性声明及参数。 |

直接缺失的依赖文件也已核对：

| 包内文件 | 未随包提供的直接项目依赖 |
|---|---|
| `GlobalThetaData.lean` | `HeckeGeneral.Analysis.LocalThetaInput`、`HeckeGeneral.Analysis.LogGaussianMellin`、`HeckeGeneral.Arithmetic.SIntegerLocalDiagonal`、`HeckeGeneral.Arithmetic.SUnitFiniteGeneration`。 |
| `Generator.lean` | `HeckeGeneral.Analysis.PrincipalGeneratorCalibration`、`HeckeGeneral.Arithmetic.SIntegerModulus`。 |
| `HeckeAxiom/QuadraticSieve.lean` | `HeckeAxiom.SexticSymbolDictionary`、`DedekindZetaZeroFree.Arithmetic.Kummer.QuadraticCharacterFamilyAndConductorShape`、`DedekindZetaZeroFree.LargeSieve.CharacterBounds.OrientedHeckeRows`。 |
| `CubicSieve/ExteriorSieve.lean` | `CubicSieve.ExteriorKernel`、`CubicSieve.FiniteDuality`、`CubicSieve.Bootstrap`、`DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound`。 |
| `CubicSieve/Complete.lean` | `CubicSieve.GcdPoissonAssembly`、`CubicSieve.GaussianColumnBlocks`、`CubicSieve.Initial`、`CubicSieve.Endpoint`。 |
| `HeckeSkeleton/Moments.lean` | `HeckeSkeleton.Theta`、`HeckeGeneral.Analysis.TInputParameterUniformMoments`、`HeckeSkeleton.HighArithmeticInputs`。其另两条直接筛依赖的文件在包内可见，但它们仍有上述缺失传递依赖。 |
| `IdealMobius.lean`、`Mask.lean`、`Counting.lean` | 分别涉及 `DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets`、`DivisorEpsilonBounds`、`LinearCountingBound`。 |

本轮使用的 Mathlib 名称以精确版本最终编译为核查依据；不把这些名字与未提供的项目名字合并标成一个模糊的“可能能编译”状态。若最终某个 Mathlib 名称仍未通过核对，应按实际失败日志逐项列出。

## 6. 实际项目中的调用顺序

1. 在新增项目接线文件中提供外部理想的乘法与素坐标等价，证明范数、平方自由和互素字典。
2. 对 `idealSymbol J (D.generator I)` 证明真正的生成元误差消除、两变量乘法和精确六次幂掩码律。
3. 把实际普通理想计数沿单射传到外部理想，把已证两条筛按字典转换成新接口。
4. 直接应用 `hybrid_energy`、`hybrid_energy_with_beta_mass` 或 `hybrid_energy_bounded`。不再重新编写正常形、18 项有限支撑证明、产品纤维估计或小幂账本。
5. 对实际冻结反射系数，识别它们与本轮规范局部表、支持拆分和相位系数的定义，再使用冻结出口及上述混合界。

使用普通理想上的外部零延拓时，非外部位置的零值也须进入全域符号律；不能在所有普通理想上无条件把六次幂写成纯 `IsCoprime` 指示函数。直接在非零外部理想子幺半群上建立字典通常更直接。

包内 `wholeIndexMask` 是关于完整指数 `completedIdeal c n` 的掩码。其标记重叠识别必须检查整个 `c*n³`；允许 `c,n` 共有素因子和标记槽重复，不能只检查平方自由变量 `c`。

### 6.1 本轮冻结出口已经构造的内容

下列原始有限和出口、统一源能量、变化冻结支撑的聚合及全族标准 `ε` 终端入口均已通过指定版本编译和全包公理审计。它们不要求项目重新提供拆分函数、原行等式或最终能量界。完整证明路线另见 `FROZEN_PROOF.md`。

| 文件及实际入口 | 已在新代码中完成的内容 |
|---|---|
| `PrimeCoordinates.lean`、`PrimeProducts.lean`、`RowCoordinates.lean` | 从真实幺半群与自然数有限素指数向量的等价构造所有素因子、支持／补支持因子、最小指数和剩余立方。证明实际元素的乘积分解及范数乘积公式；自然构造 `k_pow,k_sup,d` 并证明重建、两两互素、剩余行平方自由及其范数上界。素位类型不要求有限。 |
| `LocalTable.lean`、`RawInput.lean` | 使用显式三余数 Whittaker 表和普通局部系数表；证明 `e≡2 (mod 3)` 的系数为零，非零项的指数合法，并在原始 `(a′,n′)` 集合内部删去零项。固定最小因子的纤维上构造 `x`，证明 `a′=a_min*x³` 和重索引单射。 |
| `FrozenReduction.lean`、`RawSource.lean`、`Overlap.lean` | 源项保留未冻结的 `π,ρ,λ` 三类相位及原始混合相位。证明它们的精确冻结等式、完整立方 `b=x*n′` 的唯一性和原始源行的严格等式。完整指标标记的重叠零值由实际符号六次幂律推出，允许标记槽重复；不把零值规则或原行等式另列为假设。 |
| `ColumnNormalization.lean`：`FrozenReduction.Data.weighted_raw_frozen_row_block_exit` | 从原始行块和原始最低指数块出发，明确保留 `lam(c)/sqrt(N(c))`。构造单位模界的最终 `a,β`，并证明精确外部平方标量为 `(tableMajorant/Bmin)²/Nmin`；`N(P)^(-1/2)` 仍在混合行内部。 |
| `WeightedHybridBound.lean`：`FrozenReduction.Data.weighted_raw_hybrid_bound` | 将实际加权原系数能量接到已证明的 LOW-HYBRID 界，使用实际剩余行 annulus 的 `K₀`，不把它替换成较粗的总行球半径。 |
| `LocalBudget.lean`、`SourceLedger.lean` | 从逐素 Gauss 平方界构造实际 `chargeIdeal` 并证明 `tableMajorant²≤N(chargeIdeal)⁻¹`，得到准确的 `−v−2ℓ−S−B` 系数指数。`source_energy_ledger` 的左侧包含真实源能量，随后才乘强幂行和共同核标量。 |
| `PowerfulCounting.lean`、`FrozenCounts.lean`、`FrozenPartition.lean` | 对实际有限强幂理想集合、支撑平方自由集合及原始行的规范两因子有限像证明计数；`sum_rows_eq_frozen_blocks` 给原行有限和的精确正项分块。无需上游提供冻结块个数结论。 |
| `UniformWeightedHybridBound.lean`：`FrozenReduction.Data.uniform_weighted_raw_hybrid_bound` | 固定全局素坐标、符号、自然范数、线性计数和两筛后，先取得 `C₀`，再量化全部冻结 `Data`，包括 `support,ordinary,digit,minimum`。仅要求这些数据使用同一坐标和符号。 |
| `UniformSourceLedger.lean`、`UniformTerminalSource.lean` | `uniform_source_energy_ledger`、`uniform_source_energy_terminal`、`uniform_source_energy_power_saving` 将同一个先选的常数传到实际源能量、反射账本和终端幂节省。常数不依赖之后选择的冻结数据。 |
| `FrozenSupportExtension.lean`、`UniformAggregateSource.lean` | 证明固定 `pow` 后，`base` 扩成 `base∪support(pow)` 不改变该块的支撑部分、剩余行或原始行块。`FrozenFamilyAlignment` 允许每个实际冻结因子对使用自己的 `Data`，其反射支撑就是上述扩充集合。`varyingFamilySourceEnergy_eq_blocks` 给真实全行能量的严格正项分块。 |
| `UniformAggregateSource.lean`：`uniform_family_source_energy_ledger` | 对变化的普通素集、digit 和 minimum 使用同一个源能量常数，并消费实际冻结因子对计数。所得全行界为 `C*Z^(Eref + eps*(H+v+ell+z) + eta*(O+Rrad))`。强幂成本 `O/2` 只付一次；没有再次 Cauchy 的损失。 |
| `UniformAggregateTerminal.lean`：`uniform_family_source_energy_subpower`、`uniform_family_source_energy_terminal`、`uniform_family_source_energy_power_saving` | 已验证的全族出口：固定 `W>0` 与目标 `ε>0` 后先选常数，用长度预算 `(H+v+ell+z)+(O+Rrad)≤W` 和内部小幂 `ε/W` 得到 `Eref+ε`，再转为 `terminalBound+ε`，最后在明确裕度下得到 `F-c/4`。三个入口的公理依赖均只有标准三条。 |

因此，`split`、实际冻结支持分解、局部禁用余数类为零、非零项的合法指数、`π/ρ/λ` 冻结、原行严格等式和整体局部 majorant 的构造，都不再是留给项目的抽象结论输入。

**三个支撑范围须准确区分。** 初始行分解使用 `base`，对应固定 label/puncture。固定强幂部分后，反射集 `Data.support` 可以取 `base∪support(k_pow)`；扩充不改变该块剩余行，因为新增素位在原行上的赋值已至少为二。`Data.ordinary` 则是活动普通素位集 `f₀`，只要求包含于反射支撑。完整立方的自然拆分只按 `ordinary` 进行，对偶变量 `c′,n′` 也只避开 `ordinary`，允许含有 `support \ ordinary` 中的不活动素位。最低指数数据的 `minimum_ordinary` 是原始支持条件；对较大集合的 `minimum_supported` 由包含关系推出。

**局部输入仍是原始 Gauss 界。** `PrimitiveLocalBounds` 只要求逐素 `‖first‖²≤1/q`、`‖prefactor‖²≤q`，以及零指数表在 digit `0,4` 时的平方范数不超过 `1/q`、其余不超过一。整体 `C/N(x)`、`C²≤N(chargeIdeal)⁻¹`、单位化后的系数界及源能量界都在新模块内部证明。项目接线应从原始 Gauss／Weyl 表导出这些局部标量事实，不能直接把一个反射能量估计放进结构。

冻结侧仍需识别的实际项目数据是：原反射定理与新模块 `rawSourceTerm` 的逐项对应、原 Gauss 标量的上述局部平方界、允许生成元六次符号的精确乘法及互反，以及反射层共同 profile／核界和实际导子、不变量数据。核的共同标量在有限代数层按给定数值乘入；把它识别为具体反射变换的界，仍须调用原工程的核提供者。包内 `GlobalThetaData.lean` 的义务结构本身不能替代这些实例。

**强幂计数的准确强度。** 实现先给出 `sqrt(K)·H(K)`，再使用已证明的调和界，得到带 `1+log K` 的中间估计并吸收为任意 `K^(1/2+ε)`。这符合目标允许的任意小幂，但不应改写成已经证明无对数的精确 `O(sqrt(K))`。受支撑平方自由选择和任意固定局部切片成本 `c^ω` 分别由 `FrozenCounts` 与 `SupportPower.prime_support_power_subpower_of_counting` 从同一计数数据推出。

### 6.2 与任务字面要求的语义核对

`hybridRow` 的二次符号是 `symbol k (n*b)^3`，三次符号是 `symbol P n^(-2)`，并保留 `P,k` 与 `P,b` 两个原始碰撞掩码。输入二次筛的原符号方向通过有限复矩阵转置转换，未增加主 LOW-HYBRID 的互反假设。列权重严格为 `1/sqrt(N(P))`，质量严格为 `sum |a(P)|²/N(P)`；任意 `beta` 的最大平方质量只出现一次。

Cauchy 在完成变量的联合 `(t,c)` 指标上进行。二次筛作用于 `mh` 后，实际立方支撑预算仍保留在正项系数和内；随后三次筛作用于联合 `(m,c)` 对应的 `cm`。没有对每个原始 `b` 单独做 Cauchy，也没有假设 `g,t` 互素或收紧任意立方变量的支撑。

引理 4.6 的独立入口 `completed_quadratic_energy_bounded` 写在 `CompletedQuadraticBound.lean`，只接受二次筛。它先按 `y=n*b` 聚合，再规范写成 `y=s*t²`；原始列平方自由保证每个产品纤维被实际平方自由除数数控制。`CompletedQuadratic.completed_quadratic_positive` 给任意聚合系数的正性形式，原 `k,t` 零值在固定 `t` 后才从正项能量中删除。独立单位系数结论的主因子为 `(K+NB)NB`，损失 `Delta(NB)² H(NB)² (KNB)^eta` 取 `eta=eps/5` 吸收。这里没有逐字另行封装论文的 dyadic `(T,G,C,r)` 展示式；混合主证明实际需要的完整双掩码正性化已在前述正常形与加权组合中完成。

这个独立入口的左侧是原始双和，而不是已经分解的块：

\[
\sum_k\left|\sum_{n,b}\beta(n,b)\chi_k(nb)^3\right|^2
\le C_\varepsilon(KNB)^\varepsilon(K+NB)NB.
\]

其常数在 K,N,B≥1、全部原始有限支撑与系数之前选择；只要求 k,n 平方自由、原范数上界及 |β|≤1，b 不要求平方自由。符号方面只用第二变量乘法及六次幂掩码律，没有额外输入三次筛或全符号互反。

旧的固定 `D` 冻结入口本身只能陈述“对每个 `D` 存在常数”。新增统一入口将常数选择前移，明确得到“固定算术字典后存在常数，对所有冻结数据成立”，因此不能再把冻结字段变化的统一性留给文字解释。

## 7. 最后应审计什么

最终自包含文件已经按指定版本完整构建；`LowAudit` 对两个新命名空间的 955 个定理（包括内部辅助定理）检查了全部公理依赖，全部通过。依赖集合均包含于 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或新增算术公理。

在用户完整项目中完成字典后，应另对实际特化后的主定理运行同样的 `#print axioms`。包内 `Moments.lean` 含有其他占位声明；只有实际依赖链审计才能确认新入口没有使用那些声明。自包含模块通过核查不能替代完整项目实例的依赖审计。

本轮最应继续检查的边界已转移到**真实允许生成元和实际六次符号的字典**，以及外部理想与素指数坐标的识别。原行到加权块的完整有限重索引、两种平方自由产品支撑、除数和调和损失，已经在新代码内部构造，不再列为上游需要补证的分析步骤。
