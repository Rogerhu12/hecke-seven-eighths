# 素数槽消去接线报告

## 主定理与假设

主结果位于 `HeckeSkeleton/PrimeCancellationExplicit.lean`：

```lean
theorem paired_primes_below_one_of_explicit_models
    (F : ExplicitModelFamily c ι) (hB : c.family.B < 1)
    (control : ExplicitModelControl F) :
    ExplicitPairedPrimeProductBound F (2 * c.family.B - 1)
```

上下文是数域 `K`、仓库现有的 `c : TargetContext K`，以及独立的索引族
`ι : ℝ → ℝ → Type u`。`ExplicitModelFamily` 的每个元素仍是原有的实际
`MomentData`，使用原 `pairedRows`、`slotProduct`、`primePolynomial` 和完整
`originalMomentMask`。索引不经 `SourceMomentIndex`、`targetData` 或
`highExpansion` 定义。这个分离使新增主定理可以独立审计，同时保留到旧模型接口
的明确适配。

模型族记录模型底数 `X > 0`、配对参数满足 `m + q = 1`、参数长度与几何总长度
同为 `z`、原公共掩码的精确等式，以及槽系数的有限阶性。这些都是结构条件；
所有求和行的 `idealNorm u ≤ X` 从原 `rows_spec` 推出，线性行数界则从实际
数域理想计数定理证明，没有把两条估计增加为模型假设。

`ExplicitModelControl` 要求：

1. 槽数不超过固定的 `c.geometry.slots`。
2. 每个槽系数的逆元属于模型的有限例外角色集 `theta`。
3. 每个实际素数窗口是支撑在 `[1,2]` 的 Schwartz 函数，并与该槽的
   `profile 0` 完全相等。
4. 每个有限组 Schwartz 半范数都有统一的 `C * (1 + T)^A` 界；常数在尺度
   `Z`、高度 `T`、模型索引、扇区和槽之前选定。
5. **每个实际求和行**的槽角色导子满足
   `log Q ≤ D * (1 + log X) * (1 + T)^q`，其中 `D ≥ 1`、`q ≥ 0` 统一。

结论在 `ExplicitPairedCapacity F i`，即 `z ≤ J * mesh` 下成立。这里
`J = c.geometry.slots`；原 `pairedCapacity` 已蕴含这个长度上界。
主证明先给出独立的 `Z ≥ 1`、`T ≥ 1` 下的统一界：

```text
∑ sector ∑ u ∈ pairedRows, ‖slotProduct u X 0‖²
  ≤ C * X^(1 + (2B - 1) * z + lamA) * (1 + T)^A.
```

`A,C` 先于所有 `Z,T` 和索引选取。最终定理代入 `T = Z^τ`，保持原来的
`∃ A, ∃ ceiling > 0, ∀ τ, ∃ Z₀, ∃ C, ∀ Z, ∀ i` 量词顺序；
可以取 `ceiling = 1`、`Z₀ = 1`。原结论中的 bin 限制不为证明所需。

控制记录没有把素数和、配对矩、Euler 恒等式、无零性、解析增长或理想计数界
作为假设。后文说明窗口、取逆条件与全行导子控制在实际构造中的来源。

### 原接口的兼容定理

`HeckeSkeleton/PrimeCancellationWiring.lean` 仍给出精确的原有结论：

```lean
theorem paired_primes_below_one_of_models
    (M : SourceMomentModels K c) (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) M)
    (hrows : SourceRowEligibility M) (control : PrimeSlotModelControl M) :
    PairedPrimeProductBound K c M (2 * c.family.B - 1)
```

`explicitModelFamilyOfSource` 与 `explicitModelControlOfSource` 逐字段适配原模型
及修正条件，然后直接调用上述独立主定理。`PairedPrimeProductBound` 没有重定义，
证明不调用 `momentModels` 或尚未完成的原 `paired_primes_below_one`。
旧接口类型自身经 `SourceMomentIndex` 继承的公理依赖，单独列在审计表中；
不会将该包装接口误报为独立主定理的公理清单。所有 PR 差异均为新增文件，
原有证明、定义及任务说明保留目标分支原样。

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
`2 * δ * z ≤ lamA/2`。显式模型接口以 `z ≤ J * mesh` 为容量条件；在旧接口中，
这条长度上界仅由 `pairedCapacity` 的第一部分得出，
不使用裸细分数据没有保证的 `plainLength ≥ 0`。

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

原仓库的 MI-M-MODELS 仍需构造具体 `momentModels`，并验证其原有校准、行资格
与本报告列出的修正结构条件，尤其是随参数变化时覆盖全部模型行的导子界。
这是任务说明允许保留的具体模型构造工作。本次主结果覆盖任意满足这些明确条件
的实际模型族，不声称完成整个七八定理。

原骨架的 D-EXPANSION（`highExpansion`）与 D-SUPPORT
（`rows_in_norm_envelope`）也仍是既有未完成项。旧 `SourceMomentIndex`
经 `targetData` 引用它们，因而旧接口的兼容定理仍继承 `sorryAx`。
新增独立索引主定理不使用该索引类型，其依赖由严格递归白名单独立核查。
本 PR 没有改写这些既有上游定义或证明。

## 编译与公理核查

### 本轮实际验证

2026-10-31 UTC，提交
[`1998acb78ba9bf0a82114aa6fb4d8fa01ee2b35e`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/1998acb78ba9bf0a82114aa6fb4d8fa01ee2b35e)
的[主运行 41172711766](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41172711766)
已整体 `success`。[proofs job 124453912879](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41172711766/job/124453912879)
在 05:36:02 完成实际 Lake 构建，在 05:36:09 完成独立公理审计。
[解析输入运行 41172711746](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41172711746)
也已成功，5 个输入 job 全部通过。

环境为 Lean `4.35.0-rc3`，编译器 commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`，Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`。实际日志同时记录了编译器版本与
Mathlib revision 的检出。

| 模块 | 本轮真实结果 |
| --- | --- |
| `HeckeSkeleton.PrimeCancellationCounting` | Lake 日志为 `Replayed`；源码与此前成功构建相同 |
| `HeckeSkeleton.PrimeCancellationBounds` | Lake 日志为 `Replayed`；源码与此前成功构建相同 |
| `HeckeSkeleton.PrimeCancellationHecke` | Lake 日志为 `Replayed`；源码与此前成功构建相同 |
| `HeckeSkeleton.PrimeCancellationPolynomials` | Lake 日志为 `Replayed`；源码与此前成功构建相同 |
| `HeckeSkeleton.PrimeCancellationWindows` | Lake 日志为 `Replayed`；源码与此前成功构建相同 |
| `HeckeSkeleton.PrimeCancellationMoment` | Lake 日志为 `Replayed`；源码与此前成功构建相同 |
| `HeckeSkeleton.PrimeCancellationExplicit` | 实际 `Built`，41 秒 |
| `HeckeSkeleton.PrimeCancellationWiring` | 实际 `Built`，4.5 秒 |
| `HeckeSkeleton.PrimeCancellationAudit` | 独立 Lean 命令成功，严格守卫与全部 24 项输出完成 |

实际执行命令：

```sh
lake --fail-fast build +HeckeSkeleton.PrimeCancellationWiring:olean
lake env lean HeckeSkeleton/PrimeCancellationAudit.lean
```

构建日志为 `Build completed successfully (12345 jobs).`；
12345 统计全部构建任务，本轮两份修改的证明模块都被实际重新编译。
命令使用 `set -euo pipefail`，保留真实退出结果。
完整日志已保存为
[`prime-cancellation-verification` 产物](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41172711766/artifacts/13032012116)，
大小 156699 bytes，SHA-256 为
`a9cc050509e647342f0a63b0da277f9fd1873d00b0d739547ea73ef6fb9dc7e8`。

工作分支已合并目标分支 `182769d49e5c184547c0949ddc328b9e7a87e6f7`。
本轮 9 个 Lean 文件的 Git blob 均与验证提交逐一核对一致。
最终报告提交仅补齐本说明，不改变已验证的 Lean 源码。

### 严格主定理守卫与全部 24 项实际输出

`PrimeCancellationAudit.lean` 使用 `Lean.collectAxioms` 递归检查以下两个独立主定理；
只要出现白名单以外的依赖，CI 就失败。声明缺失也会失败。

- `PrimeCancellationExplicit.exists_uniform_paired_prime_bound`
- `PrimeCancellationExplicit.paired_primes_below_one_of_explicit_models`

本轮日志明确输出两条 `PRIME_CANCELLATION_CLEAN_AXIOMS`，其公理均为
`[propext, Classical.choice, Quot.sound]`，随后输出
`PRIME_CANCELLATION_CLEAN_AUDIT_CHECKED|2`。这与下表两项对应的实际
`#print axioms` 完全一致。

下表是独立 Audit 的全部 24 项，顺序与源码逐一核对。16 项仅含标准三公理，
4 项旧源模型适配声明和 4 项既有骨架声明仍含 `sorryAx`。

| 声明（省略共同前缀 `HeckeSkeleton.`） | 实际公理清单 |
| --- | --- |
| `PrimeCancellationExplicit.exists_uniform_paired_prime_bound` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationExplicit.paired_primes_below_one_of_explicit_models` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationExplicit.ExplicitModelFamily` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationExplicit.exists_paired_linear_count` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationMoment.canonicalFixedBadPrimeSupport` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationHecke.exists_ideal_count_bound` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationHecke.actualPrimeArithmetic` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationHecke.deletedSlotData` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationHecke.emptySlotData` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationHecke.exists_uniform_finiteOrder_polynomial` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationWindows.actualPrimeWindowSchwartz_uniform_seminorm` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationBounds.absorb_slot_logarithms` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationMoment.logQ_le_of_norm_polynomial` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationMoment.source_paired_energy_le_of_slot_bounds` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `PrimeCancellationMoment.source_conductor_control_of_polynomial` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `PrimeCancellationMoment.decomposedMomentDataWithSlots_inverse_mem` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationMoment.inverse_mem_restrictSlots` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationWiring.primePolynomial_bound_of_analytic_data` | `[propext, Classical.choice, Quot.sound]` |
| `PrimeCancellationWiring.exists_uniform_paired_prime_bound` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `PrimeCancellationWiring.paired_primes_below_one_of_models` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `highExpansion` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `rows_in_norm_envelope` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `targetData` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `SourceMomentIndex` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

新增独立模型族类型、真实全行计数、固定坏素数支持及两条主定理均通过三公理检查。
这项检查针对在明确模型条件和现有 `c.family.boundary` 前提下的证明依赖；
具体模型和零点边界仍是定理陈述中的前提。

旧 `SourceMomentIndex` 经 `targetData` 引用原 `highExpansion` 与
`rows_in_norm_envelope`，因此旧 Source 包装定理保留同一项 `sorryAx` 依赖。
独立主定理的类型和证明不引用该索引；兼容包装的公理清单单独保留。
全部新增 Lean 文件未引入 `sorry`、`axiom`、`native_decide` 或 `admit`，
原有定义与证明保持目标分支原样。

### 构建调度与并发取消

基础依赖按真实深度上界 `40`、`100`、`180` 分为三个阶段，每阶段四片。
完整包只在真实 Lake 构建成功后生成，恢复时检查源码／配置指纹及归档 SHA-256；
最终仍由 Lake 检查构建记录。本轮命中完整依赖前缀缓存，prepare 与 proofs 成功，
三个 foundation 阶段按设计跳过。此前成功生成的原生产物得到复用。

远端全部五个 workflow 均已核对为 `concurrency.cancel-in-progress: true`：

- `prime-cancellation-verify.yml`
- `prime-cancellation-inputs.yml`
- `prime-cancellation-foundation.yml`
- `theta-local-wiring.yml`
- `low-hybrid-exterior.yml`

主验证和解析输入按分支分组；基础编译 job 的分组另含调用工作流、阶段上下界和
分片编号，保留当前分片的并行并取消对应分组的过时编译。
[旧运行 41158923531](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41158923531)
已实测以 `cancelled` 结束。取消后的进度缓存仅对实际开始编译的任务保存，
并先停止该独占 runner 内的编译进程。
