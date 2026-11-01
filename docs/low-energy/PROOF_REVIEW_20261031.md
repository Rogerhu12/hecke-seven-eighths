# LOW-REFLECTED-ENERGY 源码审查（2026-10-31）

历史范围：本记录审查一般化之前的物理 Gaussian 证明链。下文使用的
`HeckeSkeleton.completedMarkedEnergy` 旧名称，现对应
`HeckeSkeleton.physicalCompletedMarkedEnergy`。最新一般接口、任意次幂
尾界和统一高度见 [GENERAL_STATEMENT.md](GENERAL_STATEMENT.md)；
当前验收结果见 [PR #3](https://github.com/Rogerhu12/hecke-seven-eighths/pull/3)。

本记录汇总本轮**源码与数学结构审查，不是 Lean PASS 声明**。实际编译及公理依赖以对应源码哈希的 [source_manifest.json](source_manifest.json)、CI 日志和公开定理的 `#print axioms` 为准；状态另见 [STATUS.md](STATUS.md)。在以下范围内，未发现确定的目标替换、循环能量假设或指数遗漏。

检查覆盖真实反射项、分离块、环带与双列聚合、冻结态、元组重构和最终轨道能量，并对照 paper 的混合筛法及低能量指数。以下结论只评价已读源码的结构；声明存在、证明策略合理与内核接受是不同层次，不能用本记录替代完整依赖闭包的验证。

## 条件端点与数据边界

[ActualCompletedMarkedEnergy.completedMarkedEnergy](../../HeckeSkeleton/LowEnergy/ActualCompletedMarkedEnergy.lean) 接受固定 `F : FiniteMellinData`、原 `MarkedCoefficientReflectionInput`、`QuadraticSieveBound` 和 `CubicSieveBound`，推出原 `LowCauchy.CompletedMarkedEnergy`。[反射输入](../../HeckeGeneral/Analysis/MarkedThetaReflection.lean) 保留生成元、外部非分歧、角权非零、核、两侧绝对收敛及反射等式等条件；本次不证明该输入的存在。[TargetSieveDictionary.quadratic_bound_iff、cubic_bound_iff](../../HeckeSkeleton/LowEnergy/TargetSieveDictionary.lean) 均为 `Iff.rfl`，没有强化两条允许的筛法假设。

[HeckeSkeleton.completedMarkedEnergy](../../HeckeSkeleton/Principal.lean) 泛化为固定的隐式参数 `F`，从而条件能量定理无需实例化尚未实现的 `finiteMellinData`。`principalSource` 仍显式使用该原始数据提供者；上游 admitted 构造及反射实现的缺口没有因此消失。常数可依赖固定的 `K,S,F,θ` 及核/反射资料，不宣称对所有 `F` 或变化的 `θ` 导子一致。

最终签名未增加 completed-energy、分离块能量或行主项估计。局部范数、窗口与导子比较是实际适配层证明的几何条件。目标字典只导入原行定义所在模块，未反向使用待证的主端点来证明自身。

固定 Lean 版本的[公理收集器](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Util/CollectAxioms.lean) 同时遍历声明类型和证明项。因此本轮还检查了条件端点类型中的直接构造路径，而不假设结构体投影会自动排除其他字段：

- [Base.probeData](../../HeckeSkeleton/Base.lean) 的五个字段来自 `arithmeticData`、两个 `signalCharacters` 投影和两个 `probeTests` 投影。算术路径为 `axiomChoice.thetaData → thetaArithmeticData`，使用已证明的存在性与生成元性质；信号字符和测试函数的直接构造中也没有 admitted 字段。
- `thetaPeriod` 是 `conjugate P.Lambda * conjugate P.G * targetCharacter`；代表字符的直接构造使用已证明的零点集恒等式。原行继续使用 `completedThetaSum → completedTerm` 的显式求和。
- [Gram.Orbit](../../HeckeSkeleton/Gram.lean) 只是 `SIntegerOrbits K S (sixthPowerUnits K S)`，没有捆绑 Gram 估计。轨道范数使用带有已证不变性的商提升。
- `Base.targetData` 确实捆绑尚未证明的 `highExpansion` 和 `rows_in_norm_envelope`，但上述条件端点及其直接构造路径没有引用它。

这项检查止于直接构造及其存在性证明，未发现需要改动的源码问题；它不是传递公理闭包的编译证明。最终端点的实际 `#print axioms` 仍是必需验收。

## 原始行、掩码和完整单位扇区

[TargetDictionary.completedMarkedRow_eq、completedMarkedRow_energy_eq](../../HeckeSkeleton/LowEnergy/TargetDictionary.lean) 连接原始行、截断和理想—扇区索引。[ActualTupleReconstruction.completedMarkedRow_reflection_identity](../../HeckeSkeleton/LowEnergy/ActualTupleReconstruction.lean) 还原同一行；活动标记（active）之和始终留在每行绝对值平方内部，完整立方变量也留在双列和内。活动标记与行、与立方列的两道移动互素掩码没有被删去；非活动碰撞通过明确的零项处理。

[ActualCompletedMarkedEnergy.idealSector_tsum_eq_finite](../../HeckeSkeleton/LowEnergy/ActualCompletedMarkedEnergy.lean) 对有限范数球与**全部** `SixthUnitClasses` 求和，扇区数仅进入固定常数，未选取单一主扇区。空选集与单位理想包含在原定义内。冻结态及类切片的平方计数由 [squared_frozenState_count_small_power](../../HeckeSkeleton/LowEnergy/ActualFrozenStateCount.lean) 支付；非活动元组使用倒范数权的总绝对质量。

[ActualFrozenAggregation.actual_frozen_row_energy](../../HeckeSkeleton/LowEnergy/ActualFrozenAggregation.lean) 抽出非活动倒范数标量后，非活动范数仍留在物理核尺度和窗口约束中。[ActualFrozenReconstruction.actual_frozen_row_reconstruction](../../HeckeSkeleton/LowEnergy/ActualFrozenReconstruction.lean) 的交换先取得环带与双 dyad 联合可求和性，再取各纤维并交换有限标记和；没有以不收敛级数的默认零值充当重构。该恒等式中为收敛选择的资料相关常数，不会替代最终能量所需的一致常数。

## 公共 Mellin 核与无界双 dyad

[ActualSeparatedBlock.slicedPhysicalBlock_eq_integral](../../HeckeSkeleton/LowEnergy/ActualSeparatedBlock.lean) 在平方前提取同一个核。公共密度只依赖冻结资料、固定四类和 dyad 端点；行、标记、双列系数分别仅依赖 `k`、`P`、`(c,b)`。其范数界 `16`、`4A`、`4Cf/(√Nc·Nb)` 给出精确平方因子 `65536 A² Cf²/(Clo Blo²)`；[actual_block_energy](../../HeckeSkeleton/LowEnergy/ActualBlockEnergy.lean) 保留完整四尺度筛法多项式。

[ActualCommonMellinTail.profile_uniform_weighted_L1_of_finite](../../HeckeSkeleton/LowEnergy/ActualCommonMellinTail.lean) 使用实际乘子界，在带状区域 `[-1/4,2]` 上取导数阶 `p+⌈8 ncx(K)⌉+2`，得一致加权积分界。小核因子为 `min(Y^(1/4),Y^(-2))`，在整个行向量外提取。

[Numerics.low_full_ramified_exponent_with_sieve_loss](../../HeckeSkeleton/LowEnergy/ExponentTail.lean) 保留原始损失 `δ(H+v+b+z)`；由 `hybrid_small_power_width` 和 `δ≤1`，无界列长度的小幂消耗一单位尾部衰减，最后仍余能量指数 `−2 max(v+3b−T,0)`。平方根后由 [DyadicTail.summable_weight_and_tsum_le](../../HeckeSkeleton/LowEnergy/DyadicTail.lean) 支付完整无限格点，质量至多 `(M+2)²`。[actual_all_annuli_dual_energy](../../HeckeSkeleton/LowEnergy/ActualAnnularBlockEnergy.lean) 再以实际高斯 seminorm 求和全部环带；积分及级数 Minkowski 均在原始行 Hilbert 空间进行，并先建立可积性/可求和性。固定正线 `2` 证明本目标所需尾部，不等于已形式化 paper 更强的任意幂尾部断言。

## ε 预算与精确 q⁻²

[ActualCompleteIdealEnergy.actual_finite_complete_ideal_energy](../../HeckeSkeleton/LowEnergy/ActualCompleteIdealEnergy.lean) 取

$$
\delta=\min(1,\varepsilon/100),\qquad
\varepsilon_{\rm inner}=\varepsilon/100,\qquad
\varepsilon_{\rm outer}=\varepsilon/2,\qquad
\rho=\varepsilon/24.
$$

于是 `23δ+2εinner+εouter ≤ 3ε/4 < ε`；`ρ` 与 powerful 理想聚合所用参数一致，半范数质量只支付一次。所选理想范数满足 `Z^d ≤ q ≤ 2^slots Z^d`：下界用于原行截断的 `−2d`，上界经 [LogGeometry.restore_selected_norm](../../HeckeSkeleton/LowEnergy/LogGeometry.lean) 恢复原 `q⁻²`，仅付固定因子 `2^(2 slots)`。最终两处 `q⁻²`（行截断与能量右端）均保持原定义。

## 本轮依赖修正

[TargetGaussian.annularMarkedRow_summable、completedMarkedRow_gaussian_annuli](../../HeckeSkeleton/LowEnergy/TargetGaussian.lean) 改为直接调用 `ActualThetaAbsoluteDraft.actual_probeTheta_absolute`，并收窄导入至 `ActualProbeThetaAbsolute`。此前通过不透明复合 `actual_probeIntegralInput` 投影 `theta_absolute`，可能把无关积分字段的 admitted 依赖带入证明项；直接调用保留所需结论并缩小依赖。高斯重构只移动 completed theta 尺度，原素数窗口与权重始终使用原 `Z`。该修正的最终公理闭包仍须以本次源码的实际验证输出确认。
