# GR-12：Gram 装配（加性 Gram 界，论文命题 3.8）

`HeckeSkeleton/Gram.lean` 的 `gram_assembly` 要证明 `GramBound K S P`。
其余叶子 GR-01 至 GR-10 已关闭，GR-11 由子代理在做（`HeckeSkeleton/SmallRadius/`、`HeckeSkeleton/GramSmallRadius.lean`）。

## 已有的部分

- **零频率与行球 Poisson。** `GramCoreInputs/ActualGramRowBallPoissonReduction.lean` 的 `exists_actualGram_rowBall_reduction` 给出：对每个范数 ≤ Q 的轨道有限集 F，
  ∑_{q∈F} ‖振幅‖² ≤ covol⁻¹ · ‖rowBallDualSeriesTerm(Q⁻¹)‖ + C·Q/Y。
  剩下的是**非零对偶频率**的界：‖rowBallDualSeriesTerm‖ ≪ (1+|ν|)^J (Q/Y)(P_a^{1/6} + P_a²/Y) Z^ε。
- **旧仓库的分解。** `C:\Users\Boyang\Desktop\Math\Hecke L\.cache\hard-splits-20261029\gram-gr12-splits.md` 列了八个中间目标及各自在缓存中的提供者。
- **依赖闭包。** 那些提供者的闭包共 193 个模块、约 27,000 行，全部能在缓存里找到，分三部分：
  1. **无见证部分**：113 个模块。其中一个与 HeckeGeneral 逐字相同，已去掉，其余 112 个复制到新库 `GramAssemblyInputs/`（扁平模块名，清单在 `GramAssemblyInputs/PORT_MANIFEST.json`），正在逐个编译。
  2. **旧见证 `ActualAdjustedGeneratorWitness` 本身**：30 个模块，不移植。它是旧仓库自己的生成元构造，我们改用 Axiom 的。
  3. **依赖旧见证的消费者**：22 个模块，见下面阶段 2。
  另外有 27 个模块属于小半径链，其中 19 个已由 GR-11 的子代理移植到 `HeckeSkeleton/SmallRadius/`。只有 `ActualFixedBoxTotalNormSeminormBound` 和 `ActualWholeAnnularSmallRadiusPoisson` 依赖这条链。

## 阶段 2：把见证换成抽象接口

依赖见证的 22 个模块对 `w` 的用法统计：`w.D` 187 次、`w.S` 184 次、`w.C6` 16 次、`w.generator_class_mem` 4 次、`w.allowed` 3 次、`w.compl6` 1 次（只用 `.disjoint`）、`w.localization_injective` 1 次。

所以定义一个小结构体代替它：

```lean
structure GeneratorMaskWitness (K : Type) [Field K] [NumberField K] where
  S : Finset (HeightOneSpectrum (𝓞 K))
  D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K)))
  C6 : Subgroup (sameSLocalPowerQuotients K S 6)
  generator_class_mem : ∀ I, generatorSameSClass K S D I ∈ C6
  disjoint6 : Disjoint (sUnitPowerLocalization K S 6).range C6
  localization_injective : Function.Injective (sUnitPowerLocalization K S 6)
  allowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D
```

字段名、类型以旧见证中的定义为准，必要时补字段。

接口里的类型定义在旧见证闭包中，需要先移植：
- `sameSLocalPowerQuotients`、`sUnitPowerLocalization` 在 `FiniteSUnitPowerLocalization`（335 行，只依赖 `FiniteSUnitPowerDetectors` 和 HeckeGeneral），整个模块移植。
- `fieldLocalPowerClassHom`、`generatorFieldUnit`、`generatorSameSClass` 在 `ActualAllowedGeneratorAdjustment`。该模块还依赖 Hilbert 迷向性（`SameSLocalHilbertIsotropy`），所以只把这三个定义和它们的 simp 引理抽成一个新模块，不移植其余部分。`AllowedGeneratorNorm` 先与 `HeckeSkeleton/AllowedGeneratorNorm.lean` 比较，相同则直接引用。

然后把 22 个模块里的 `ActualAdjustedGeneratorWitness K Sinitial zeta hzeta embedding` 换成 `GeneratorMaskWitness K`，`w.compl6.disjoint` 换成 `w.disjoint6`，再逐个编译。这 22 个模块和 `ActualWholeAnnularSmallRadiusPoisson` 的来源路径与编译顺序见 `GramAssemblyInputs/PHASE2_SOURCES.json`。

## 阶段 3：用 Axiom 的选取实例化接口

`HeckeAxiom/ArithmeticChoice.lean` 中，`thetaData` 的生成元来自 `recipeOfContext`，也就是 `DedekindZetaZeroFree/Theta/Whittaker/ExteriorFrequencyBranchCoordinates.lean` 的 `AllowedRecipe`。它包含：
- `B : Subgroup A.V`；
- `complement : IsCompl A.E B`；
- `unit_kernel`；
- `allowed : rationalClass A (generator I) ∈ B`。

这与旧见证的结构相同：都是 S 局部六次方类群里单位像的补群。

**要做的事**
- 构造投影 π : A.V → `sameSLocalPowerQuotients K S 6`，即丢掉无穷位分量。K ⊇ μ₁₂ 所以全复，无穷位的六次方类平凡，因此 π 是单射。证明 π 与 `fieldLocalPowerClassHom`、`rationalClass` 相容。
- 取 C6 := B 在 π 下的像，验证接口的各字段：
  - `generator_class_mem` 来自 `allowed`；
  - `disjoint6` 来自 `complement` 加 π 的单射性；
  - `localization_injective` 来自 `A.local_power_injection`，用法见 `unit_kernel_of_classGroup`；
  - `allowed` 来自骨架的 `allowedGenerators K c`。
- 产出 `HeckeSkeleton.Base` 层面的 `generatorMaskWitness K c : GeneratorMaskWitness K`，满足 `(w.S : Set _) = places K c` 和 `w.D = arithmeticData K c`。

**接口改动**：`Gram.gram_assembly` 和 `gramBound_of_calibrated` 加一个参数，即一个 S、D 与 `P` 一致的 `GeneratorMaskWitness`。Principal.lean 中由 `generatorMaskWitness K c` 提供。用户同意为闭合目标调整骨架接口。

## 阶段 4：最终装配（旧仓库没有完成）

把以下各项连起来：
1. 核心库：行能量 ≤ covol⁻¹‖对偶级数项‖ + C·Q/Y。
2. 对偶级数项 = ∑ 轨道 q 上的 `rowBallDualIntegrand`，再由 `norm_rowBallDualIntegrand_le_residuals` 展开成 C 与 Möbius 余项之和。
3. 对非例外频率用 `exists_rowBallResidual_goodPrime_bound`：
   B·q_C·(联合半范数和)·N²·min(1,(q_C q_k/N)^A)，N = Y/(q_C q_D)。
   对例外频率用 `ActualRowBallResidualTrivialBound`，再加上 `exists_exceptional_weighted_shell_bound`。
4. 联合半范数和对半径 R 的衰减：目标 7，`ActualFixedBoxTotalNormDecay`。小 R 端要用 GR-11。
5. 二进壳求和：GR-08、GR-09；计数：GR-06、GR-07。

**参数**：GramBound 量化在所有 W 上。LOW-CAUCHY 只用 W = P.denominator，而缓存的消费者也正是对 P.denominator 陈述的。所以可以把 GramBound 收窄为 `W := P.denominator.toSmoothAnnularTest`，需同步改 Principal.lean 的用法。也可以按旧笔记写"四个正测试函数"的约化（见 gram-gr12-splits.md 最后一节）来覆盖一般的复值 W。

## 约束

- 只做单模块构建，一次一个。
- 不改 `GramCoreInputs/`、`HeckeGeneral/`。
- 不跑全量构建，不提交。
- 只用 `propext, Classical.choice, Quot.sound`。
