# 素数槽消去接线报告

## 主定理与假设

新增模块 `HeckeSkeleton/PrimeCancellationWiring.lean` 给出：

```lean
theorem paired_primes_below_one_of_models
    (M : SourceMomentModels K c) (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) M)
    (hrows : SourceRowEligibility M) (control : PrimeSlotModelControl M) :
    PairedPrimeProductBound K c M (2 * c.family.B - 1)
```

结论使用原有 `PairedPrimeProductBound`，未重新定义或弱化它；模型 `M` 是任意参数，
证明不调用 `momentModels` 或原先尚未完成的 `paired_primes_below_one`。
所有修改均为新文件，原有证明、定义及任务说明保持原样。

`PrimeSlotModelControl` 只增加模型结构、窗口和导子的条件：

1. 槽数不超过固定的 `c.geometry.slots`。
2. 每个槽系数的逆元属于模型的有限例外角色集 `theta`。
3. 每个实际素数窗口都是一个支撑在 `[1,2]` 的 Schwartz 函数，并与该槽的
   `profile 0` 完全相等。
4. 每个有限组 Schwartz 半范数都有统一的 `C * (1 + T)^A` 界；常数在外部尺度
   `Z`、高度 `T`、行和槽之前选定。
5. **每个实际求和行**的槽角色导子满足
   `log Q ≤ D * (1 + log X) * (1 + T)^q`，其中 `X = momentBase i`，
   `D ≥ 1`、`q ≥ 0` 在所有这些参数之前选定。

其中没有把素数和估计、配对矩估计、Euler 恒等式、无零性或解析增长界作为模型条件。
现有校准和行资格记录仍为单独的假设，不改变它们的含义。

## 旧陈述的缺口及修正

### 素数窗口

`WholeMomentProfileControl` 没有提供实际 `primePolynomial` 所用窗口的控制，
因而不能独自供给消去核心所需的半范数。新记录明确识别实际窗口，并对实际选定
的高度参数给出半范数界。它不假定尚未证明的高度参数范围。
新增 `PrimeCancellationWindows.lean` 为已有的 `PrimeWindowGeometry` 给出正面构造：
把每个实际 `g.weight j` 转成 Schwartz 函数，证明它与
`analyticMomentPrimeWindow K g j` 的 `profile 0` 完全相等，支撑包含于 `[1,2]`，
且整个固定有限窗口族在任何指定有限组半范数下都有共同常数界（高度指数可取 `0`）。
这验证了原有预先选定的窗口满足所需的解析性质。把这些窗口识别到完整参数化模型
的每个槽，以及参数依赖情况下的统一控制，仍属于具体模型的校准工作。

### 非主性与有限例外角色

`rowCharacter u ∉ theta` 与 `slotCoefficient j ∈ theta` 本身不能推出
`rowCharacter u * slotCoefficient j ≠ 1`。恰当的条件是槽系数的**逆元**属于
`theta`。新引理 `slot_character_ne_one_of_exclusion` 证明这一点。

已有的完整理想构造给出具体实例：`decomposedZeroSlotMomentData` 取
`theta = {1}`，`decomposedMomentDataWithSlots` 保留它并令每个 `slotCoefficient = 1`。
新引理 `decomposedMomentDataWithSlots_inverse_mem` 直接证明这个实际构造满足取逆条件，
`inverse_mem_restrictSlots` 证明原有选槽操作保留该条件。
`decomposedWitnessMomentData` 仅替换两个 plain tests，也保留同一例外集和槽系数。
项目当前的 `rayFilter` 是空集，故默认构造沿用这组系数。对包含额外有限 ray twist
的其他模型，可以选择取逆封闭的有限例外族，并验证其原有行资格；这里不替代完整
`SourceMomentModels` 的构造与校准。

若存在槽，槽长严格为正，`totalLength > 0`，配对行定义中的例外角色排除条件
确实生效。零总长度时不存在槽，空乘积等于 `1`，无需非主性假设。

### 所有求和行与导子控制

物理行到模型行的单向校准不能覆盖模型中可能额外出现的行。新记录直接对
`pairedRows` 中的每一行要求导子界，避免把物理行的结果无依据地推广到整个和。

这是一条可由通常算术导子估计推出的条件：
`source_conductor_control_of_polynomial` 证明，只要所有求和行满足
`0 < Q` 和 `Q ≤ C₀ * (idealNorm u)^r`，其中 `C₀ ≥ 1`、`r ≥ 0` 固定，
便可取 `q = 0`、`D = 1 + log C₀ + r`。证明使用模型自身已有的
`idealNorm u ≤ X`；不需要额外的物理行满射假设。
`source_paired_slotCount_le_of_selected_equiv` 同样把实际槽索引与选中槽的对应
转为固定槽数上界。这些条件是实际模型构造要验证的结构和算术事实。

## 实际 Hecke 解析输入

`PrimeCancellationCounting.lean` 从 Mathlib 的理想计数渐近式证明域依赖的统一
线性理想计数和素理想计数界，并使用实际的 `HeightOneSpectrum (𝓞 K)` 与绝对范数。

`PrimeCancellationHecke.lean` 构造消去核心的实际 `SlotData`：

- `deletedSlotData` 的函数是项目的 `heckeDeletedContinuation K χ S`，
  系数是 `primeCoefficient K χ` 删除有限集 `S` 后的系数。
- 原 Dirichlet 级数、导数和素数幂 Euler 级数之间的恒等式来自项目已有的 Euler
  理论；包含两种素数幂索引顺序的重排以及绝对收敛证明。
- 中心线上的对数界来自实际 Euler 对数的统一可和主项，对角色和有限删除集统一。
- 非范数角色的全纯性来自实际 Hecke 延拓。`Re s > B` 的无零性在
  `Re s > 1` 使用 Euler 理论，在剩余区域直接使用传入的角色包边界。
  最终接线传入的是 **`c.family.boundary`**。
- 有限阶非主角色不能是范数扭转；其无限型在全复域上为零。
  实际固定无限型增长定理由此给出统一的
  `C * Q^(5/8) * (2 + |Im s|)^(2 * card (InfinitePlace K))` 界。

最终配对和使用 `emptySlotData`，即删除集为空的实际
`heckeDeletedContinuation`。模型的完整公共掩码仍留在素数和内，由核心的
有限掩码估计处理。这避免给随行变化的删除集加入多余的增长假设。
任意有限删除集的解析适配器也单独保留。

## 完整掩码与指数预算

实际掩码还要求素理想与整行理想互素，不能只删除固定坏素数。
`originalMomentMask_prime` 给出它在素理想上的精确公式。
用固定非零理想 `D` 支撑排除素数（包括六的素因子），所有删除素数都整除 `D*u`，
因此任意有限素数池中的删除个数不超过

```text
(log (idealNorm D) + log X) / log 2.
```

这里使用每个模型求和行已经具备的范数上界。另有一个单独引理说明：只有在额外
证明坏行素因子上的系数为零之后，才可以把行依赖掩码替换为固定掩码；主证明
没有假定这一消零事实。

设固定槽数上界为 `J`，总选中长度为 `z`。证明先固定轮廓宽度 `δ > 0`，使
`2 * δ * z ≤ lamA/2`。所需的长度上界仅由 `pairedCapacity` 的第一部分得出：
`z ≤ J * mesh`；不使用裸细分数据没有保证的 `plainLength ≥ 0`。

每个槽的归一化平方界具有指数 `(2B - 1) * length + 2δ * length`。
相乘、使用线性行数界和有限扇区数后，剩余对数损失最多为
`(1 + log X)^(2J)`。用另外的 `X^(lamA/2)` 吸收它，得到精确的目标指数

```text
X^(1 + (2B - 1) * z + lamA) * (1 + T)^A.
```

证明首先给出 `Z ≥ 1`、`T ≥ 1` 相互独立时的统一常数，最后代入 `T = Z^τ`。
因此常数选择满足原 `UniformMomentBound` 的量词顺序。对 `X < 1`，由非零理想
范数至少为 `1` 直接证明求和行集为空，不需要额外的壳层尺度比较条件。

## 还差什么

原仓库的 MI-M-MODELS 仍需构造具体的 `momentModels`，并验证其原有校准、行资格
与本报告列出的修正结构条件。这是任务说明允许保留的模型构造工作。
本次结果覆盖任意满足这些明确条件的模型，不声称完成整个七八定理。

## 编译与公理核查

固定环境为 Lean `4.35.0-rc3`、Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`，与任务指定环境一致。
新增工作流使用仓库原始 Lake 配置构建实际完整依赖链：

```sh
lake build +HeckeSkeleton.PrimeCancellationWiring:olean
lake env lean HeckeSkeleton/PrimeCancellationAudit.lean
```

`PrimeCancellationAudit.lean` 分别打印实际解析输入、行能量转移和最终两个定理
的公理依赖。编译结果和完整公理清单将在完成核验后记录于本节。
