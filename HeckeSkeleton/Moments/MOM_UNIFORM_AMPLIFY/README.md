# MOM_UNIFORM_AMPLIFY

本目录对应论文 §4.9、第 5 章和 §7.1，负责六个原始骨架目标。
所有源适配器使用同一个 `expansionRecipeRaw K c`，同一个物理源和同一个
`recipeMomentModels`；没有另选满足所需结论的模型。编译及公理验证的实际状态
记录在 PR #10 和专用 Actions artifacts 中。

## 六个原始入口

| 原目标 | 证明入口 | 保留的输入 |
| --- | --- | --- |
| `moment_profile_control` | `actual_source_profile_control` | 原校准参数仍保留；剖面界直接来自实际配方 |
| `moment_row_eligibility` | EXPANSION 的 `actualRecipeRowEligibility` | 同一实际字符、掩码、严格 dyadic shell 和全部源索引 |
| `moment_finite_sector_reindex` | `source_moment_finite_sector_reindex` | 原逐行多项式校准及原行资格 |
| `inverse_sixth_power_masks` | `recipeMomentModels_sixthPowerMasks` | 实际 unmarked 模型的三个算术字段 |
| `inverse_independent_amplification` | `recipe_inverse_independent_amplification` | 规范逆归纳的完整行严格尺度 seed |
| `inverse_amplified_witness_models` | `actual_inverse_amplified_witness_models` | 已证明的统一独立尺度界；实际源给出参数与长度几何 |

`Moments.lean` 中其他任务负责的逆归纳、配对矩和素数消去证明不在本任务的
完成范围内。它们的显式结论参数仍保留在这里；本任务不把放大终点估计
改写为自身的输入。一般数域 Hecke L 函数的最终 7/8 无零点定理陈述不变。

## 实际剖面与有限阶一致性

`ModelProfileIndex` 同时枚举 inverse、两份 plain 和全部 prime windows。
统一源控制包括原 marked 参数族、独立的 `U,D≥1` unmarked 参数族，以及实际
选取的 `heights`、`realShifts`、`imagShifts` 的 admissibility，以及先于所有源索引的
统一 plain 长度上界（实际源可取 22）。原 marked 调用
`h J A hA` 通过兼容的函数 coercion 保留。

实际公式是固定 dyadic annular window、原 one-sided cutoff 和归一化 norm power。
逆窗口的 cutoff ratio 为 `D / U^(2ξ₃)`，可为任意非负数；没有额外上下界。
plain 使用同一 annular window，prime 使用固定有限槽系统的原窗口。
所有共同常数先于行、扇区、源索引、独立尺度和高度选定。

| 模块 | 内容 |
| --- | --- |
| `ProfileControl` | 仓库原 `testSeminorm`、共同支持及全类型 profile 索引 |
| `ProfileEuler` | 真实 Euler 连续线性算子、迭代及有限 Schwartz 阶控制 |
| `ProfileLogCoordinates` | 原正半轴 Euler 积分与对数坐标的精确换元 |
| `ProfileCommonFourier` | 对全部 rowwise twists 和 cutoff ratios 的同一个点态 Fourier majorant；其 weighted L1 界及无行数损失的 Minkowski 传播 |
| `ProfileFourier` | 原 Schwartz Fourier 变换的 weighted L1 界；实/虚 norm-power 混合导数；独立 cutoff ratio |
| `ProfileNormTwists` | 实际 annular norm power、原 cutoff 的无损扩展，以及原 `testSeminorm` 的多项式高度界 |
| `ProfileScaleJets` | 字面混合导数，包括 ξ₃ 导数的 `(-2 log U)^n E^n V` 公式及有限对数损失 |
| `CanonicalProfileControl` | 从固定配方的原始公式证明全部模型 profile bounds |
| `SourceProfileControl` | 接到实际源的 marked/unmarked 全族和实际 admissibility |
| `SourceProfileJets` | 同一个实际 inverse/prime 窗口的混合参数导数与支持控制 |
| `SourceFourierControl` | 原始 inverse 剖面与 log Schwartz 函数的精确等式、同一共同核及 rowwise Fourier 传播 |
| `SharedFourierPropagation`、`FourierApplication` | 对共同 Fourier 核应用有限 Hilbert 空间 Minkowski，并把 child frequency envelope 纳入一次 weighted L1 费用 |
| `FinitePropagation` | 有限树中的尺度、对数和高度次数传播，以及任意预留正损失对有限对数次数的吸收 |

这里不把任意 Fourier-frozen child profile 假定为由原外部 T 一致控制。
频率可以无界；`weightedProfileFourierKernel` 把其固定多项式 envelope
乘入所有行和 live labels 共用的同一个核。行掩码保持在向量被积函数中。
父 Fourier 阶由 child 所需权重选择，有限深度的反向选阶随后只产生有限阶。
这些是规范归纳中解析边的输入工具；实际两次 Poisson 变换和完整归纳属于对应任务。

## 真实有限和与六次方放大

`SourceReindex` 保留原两个 plain factors、选中素数乘积、全部有限扇区和原行零掩码。
实际物理行处于 `U < N(u) ≤ 2U`。模型行指数使用
`m(U)=1+log(2)/log(U)`，因此 `U^m(U)=2U`，没有把这个行窗简化成 U。
物理行的非单位 sixth-free 底理想在一个外部素理想处有 1 至 5 的赋值；
实际局部 ramification 排除有限 theta 族与主字符。该原行资格由 #5 的同源构造提供。

`SixthPowerRecipe` 将实际 unmarked 模型的 `allowedRow`、`rowCharacter`、
`commonMask` 逐字段识别为 complete-ideal 算术构造，得到

```text
rowCharacter(u*a^6) = rowCharacter(u)
mask(u*a^6, I) = mask(u, I) * 1_{IsCoprime(I,a)}.
```

`SixthPowerDivisorIdentity` 在原有限 support 上构造 prime envelope，把 squarefree
列唯一拆成支持于 a 和与 a 互素的两部分，得到原 `inversePolynomial` 的精确除数
恒等式，包括 `N(d)^(-1/2)` 归一化、背景字符、Möbius 系数和全部零延拓。

`SixthPowerEnergy` 对真实理想乘子平均该恒等式，应用 divisor bound 和加权 Cauchy，
再以素理想赋值模 6 证明 `(u,a) ↦ u*a^6` 注入。完整行求和只支付一次。
`AmplificationSource` 保留有限扇区和 dyadic 2U 常数，推出

\[
 E(U,D) \le C\max\{U,U^{1/6}D^{5(1+a)/6}\}(UD)^\varepsilon
 (1+\|\xi\|)^A.
\]

量词顺序是 `∀a>0, ∀ε>0, ∃C,A,h, ∀U,D,ξ,σ,τ`，并保留原参数盒
`‖ξ‖≤(UD)^h`、`‖σ(u)‖≤8`、`‖τ(u)‖≤1+‖ξ‖`。

`WitnessSource` 使用实际高 bin 下的 `0≤r≤3/2+lamA`、`U≥Z^(1/16)` 和原高度
admissibility，在整个有界 r 区间上选择放大参数和初步损失。代入 `D=U^r`
得到 `max(1,(1+5r)/6)`，并保留原
`∃A ceiling, ∀τ, ∃Z₀ k, ∀Z i` 顺序。高 bin 条件与原目标相同；早期 active
scales 的 default witness 也由实际构造覆盖。

## 共享陈述的修正与论文依据

| 旧陈述/缺陷 | 修正版 | 论文依据 |
| --- | --- | --- |
| 全 profile 控制只覆盖 ideal tests，缺少 prime windows | `ModelProfileIndex` 覆盖 inverse、两份 plain、prime | 第 1550–1559、1655–1679 行：全部 tests、有限槽系统和统一有限阶控制 |
| 源控制未覆盖独立 unmarked 族，也未提供实际参数 admissibility | `WholeMomentProfileControlFor` 的 `marked`、`unmarked`、`parameters`、`lengths` 四字段；实际公式生产实例 | 第 1554–1559、3159–3174、3212–3224 行 |
| strict seed 只求和 sixth-free rows，无法包含非平凡的 `u*a^6` | `StrictUnmarkedMomentBoundFor = CompleteUnmarkedScaleSupBound M.unmarked`；同一 profile 的完整行共同 scale majorant | 第 1589–1604、3237–3257 行 |
| 仅有 frozen compact 谱集的常数，无法推出固定 polynomial height degree | 新 seed 的 `C,A,h,H₀` 先于全部 profile 索引和完整行尺度 H；放大保留该固定 A | 第 3164–3190、3223–3224 行 |
| 原物理行上界为 2U，而旧模型参数给 U | 采用 #5 的 `m(U)` 和精确 `U^m(U)=2U`；重排与最终常数桥均保持这个等式 | 第 1521–1526、3194–3202 行及 §7.1 的有限扇区重排 |

完整行 seed 的精确含义如下：先固定原始 profile 索引
`i=(U,D,sector,ξ,σ,τ)`，然后另取完整行尺度 H。对每个严格 gap 和正 ε，
共同常数先选；当 `H≥H₀`、`‖ξ‖≤H^h` 时，存在同一个非负 B，满足

```text
∀v∈rows(H), ∀0<Dchild≤H^(1-gap),
  ‖inversePolynomial (sixthRootInverseData (family i)) v Dchild 0‖² ≤ B(v)
∑v∈rows(H) B(v) ≤ C H^(1+ε) (1+‖ξ‖)^A.
```

`sixthRootInverseData` 仅把测试的行参数沿 `sixthPowerFreePart` 拉回；原背景、
方向、行字符和 commonMask 不变。在 sixth-free 底行上测试等于原测试，在
`u*a^6` 上仍取同一个原 profile。该 seed 是规范逆归纳应生产的严格短尺度结论，
不是放大后的独立尺度估计。共享定义变更已在 MOM_INV_INDUCTION 的 PR #8 协调。

为编译实际源，还修复了来自 #5 的四个依赖模块的 proof/elaboration 问题：
`PhysicalCompletedPoisson`、`ActualRowKernelHolomorphy`、`PhysicalRecipeAssembly`、
`HighBinSupport.ActualNormFormFullCorrection`。其中联合解析性由原核的真实解析
因子复合得到；这些依赖的定理陈述、数学对象和共享定义均保留。

## 编译及严格公理检查

固定环境：Lean `4.35.0-rc3`，Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`。
专用 workflow 使用仓库指定的 `restore-lake-cache@ci/lake-cache-test`，随后正常
执行 `lake --rehash build`；不合成 traces，也不使用自定义 foundation 缓存。

```sh
lake --rehash build +HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.PureAudit:olean
lake --rehash build +HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.AnalysisAudit:olean
lake --rehash build +HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ArithmeticAudit:olean
lake --rehash build +HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceAudit:olean
lake --rehash build +HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.Audit:olean
lake --rehash build +HeckeSkeleton.Moments:olean
lake env lean HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/Audit.lean
```

各组件和总 `Audit` 递归审计本任务命名空间中的所有声明，包括定义、私有辅助和
结构生成声明。原六个名字另以 `#print axioms` 检查。所有关卡只接受
`{propext, Classical.choice, Quot.sound}` 的子集；缺失目标、编译错误或
任何额外公理均使检查失败。完整日志、源码提交及编译器元数据只保存在
Actions artifacts，不提交进仓库。PR 的最终状态以这些真实验证结果为准。

AI-assisted implementation and verification: ChatGPT (GPT-6 Astra Pro).
