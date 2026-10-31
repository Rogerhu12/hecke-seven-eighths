# HIGHBIN 原始接口接线（2026-11-01）

本轮从 PR #7 的 `d88663c8e2c9461cdd942267631e829d72d1f9b3` 继续，
合入 PR #5 的实际共享源 `0263481ab8c8f2ef30d909f6a665ed22d64e5b8c`。
源码状态与原生验证状态分开记录；以下接线仍须通过本轮固定工具链的完整编译和严格公理门。

## 同一实际源

`Base.expansionRecipeRaw`、`targetData`、`SourceData`、原 `ModerateBlock`、
`actualHighPresentation` 使用同一个参数对象、原 arithmetic Euler provider、
原始行掩码、有限分箱、扇区、末壳剪裁和物理高度。共享 `SourceMomentIndexFor`、
`SourceMomentModelsFor` 以及全部校准/资格/能量对象继续引用同一份完整的 E。

`Base` 与 `Theta` 保留 PR #5 的已校准选择、径向规范化及 THETA_GLOBAL 接线。
旧的 `BaseContext` 与 `TargetArithmeticData` 模块保留为兼容导入，避免另造一份
上下文或算术选择。`ActualHighPresentation.euler` 继续使用 #7 的固定 accessor，
其值按定义为 `arithmeticHighEulerData`。

## PR #1 成果吸收核对

精确核对 PR #1 head `250644c7a5b6e09aca9e7a28747eceb160b2395a` 的完整 Git 树：
143 个 HIGHBIN 相关文件在 #7 起点全部存在，其中 114 个逐字相同、29 个已有后续修改。
涉及证明源码的差异为十一份支持模块及 `HighBin.lean`；其余为报告和检查脚本。

公开 Euler/calibration 结果迁移到 `ActualTargetEuler` 等模块，未丢弃；
prime-power additive character 的私有引理已统一为公开的
`principalPowerAddCharacter_mk`。Fourier/CRT 差异保留 #7 后来的原生修复。
固定 Euler provider 后原 provider transport 退化为 `rfl`。
本轮保留这些后续成果，并采用 #5 对相同实际算术文件的原生 elaboration 修复。

## 原 HB 接口的构造

- `actualHighPresentation`：读取原物理配方的 fixedRows、标签、移位核及 movingPiece 积分。
- `highInitialEulerControl`：消费实际初始四理想级数/Euler 乘积校准。
- `highExceptionalEulerControl`：消费原有限有理表，常数 9、cutoff 2。
- `highLabelUniformity`：原固定标签类型的基数上界；高度次数为零。
- `highShiftedNormForm`：实际主素数多项式幅度、完整 correction、导子 radical 联合分配、
  原积分搬运与固定高度盒给出 `lamB/4` 损失。
- `highBoundaryControl`：同一原行集上的初始减最终轮廓，经原壳层/分箱重索引，
  给出 `C Z^14 T^(-N)`，高度次数零。
- `highBin`：原逐标签范数界、输入行数界及原计数恒等式的有限求和。

完整 correction 保留 main、regular、valuation-one、repeated 四项。每个重复素数子集
先与行导子 radical 一并估计，再对全部子集求和。物理标签始终是原 main prime polynomial
的幅度，没有替换为另一套 full-correction 标签。

movingPiece 把当前物理样点的行单射搬运到同标签的最大基数样点。单个 receiving row
至多承接一个原核，因此逐点范数上界在搬运中保留；积分仅付固定高度盒的体积因子。

## 必要的数值选择与中间量词修正

### 幅度网格预算

| 原共享参数 | 本轮保留的更强构造信息 |
|---|---|
| `width_pos : 0 < width` | 另有 `width_buffer : 2 * e < width` |
| `e_cap : e ≤ eCap`，width 与 cap 无关系 | 另有 `width_cap : width ≤ 4 * eCap` |
| 从检测定理的 ε 取 width | 从同一已证 source 的 `∀ width > 0` 选择 `width = 4 * eCap` |

原 `exists_physical_recipe_parameters` 公开陈述保持不变；它由新增的
`exists_bounded_physical_recipe_parameters` 推出。`PhysicalRecipeParameters` 保存两个
额外的已证数值约束，仍保留原全尺度 source 与全部标签 provenance。
实际 `eCap = min(lamA,lamB)/1000`，故 `width ≤ lamB/100`。
此项已在 PR #5 评论 6545961849 与 6546037523 中提前协调，变更单独提交以便共享源吸收。

论文对应：`weil_seven_eighths_revised.tex` 的幅度分箱（约3880–3905行）要求网格、
检测和局部损失共同选小；4349–4357行明确把幅度网格及 correction 损失放入剩余预算。

### 范数形的 power-height 顺序

旧 `HighShiftedNormForm` 要求

```
∃ A C ceiling Z₀, ∀ Z ≥ Z₀, ∀ 1 ≤ T ≤ Z^ceiling, ...
```

其中包含固定 `T = 1`。实际有限零点高度的素数消去定理在固定正 `τ`、
`T = Z^τ` 后选择阈值。本轮接口据此为

```
∃ A ceiling, ∀ 0 < τ ≤ ceiling, ∃ C Z₀, ∀ Z ≥ Z₀, ... at T = Z^τ.
```

高度次数 A 与 ceiling 仍在 τ 之前固定；当前物理 producer 还把 C 固定在 τ 之前。
旧的全高度上界通过 `HighShiftedNormForm.of_uniform` 接入，两个原支持消费者一起适配。
原 `HighBinInput` 的量词本来允许 τ 后选择 `k'`、`Z₀`，因此其陈述完全不变；
`highBin_of_piece_controls` 同步执行新的选择顺序。最终一般数域 `Re(s)>7/8`
无零点定理的陈述未改。
论文对应：3659–3667行的原物理行指数、3669–3670行的固定高度次数、
4314–4367行的实参数/内部分析阶/随后高度选择顺序。

### 同一 Poisson 标量

#5 校准的固定 `physicalPoissonScalar` 保留在真实核中。旧 HIGHBIN 的两个内部 tuple
恒等式右端与 profile 因子显式同步这一标量；边界常数与范数常数吸收其范数。
对应论文3529–3532行的固定 Haar 归一化。原 contour、原 probe 和原边界方向保持一致。

### 旧范数形支持接口的实际归一化

`exists_actual_primeNormalizer_inverse_subpower` 保留原来的结论，新增显式条件
`hcomplex : ∀ v : InfinitePlace K, v.IsComplex`。它现在由 PR #5 的
`exists_actual_primeNormalizer_inverse_bound` 推出，可取系数一，替代旧的
`PrimeNormalizer.normalizer_smallPower` 未完成输入。唯一已有消费者从
`P.arithmetic.primitive12` 构造此条件；原目标定理不增加假设。
对应论文4340–4347行固定非负、非零、互不相交的实际素数窗，以及原共同归一化。

## 边界常数的选择顺序

设 `q = boundaryHeightDegree K`。阈值 `Z₀ = max(Z₁,2)` 先于任意外部阶 `N`
固定。支持定理给出的常数为

```
C_N = (2 + 1 / log 2) * physicalRecipeMultiplicity(K,S,B,e)
      * C_(N+q) * 5^q.
```

对原配方允许的全部壳参数、`Z ≥ Z₀` 和 `T ≥ 1`，原整箱边界满足
`‖boundary‖ ≤ C_N * Z^14 * T^(-N)`。因此原 `PowerHeightTailBound` 直接取
`A = 0`、`R = 14`、`ceiling = 1`。证明仅把零点检测的上界缩到 `T+3/2`；
实际行选择、原配方、初始和最终积分的物理高度 `T` 保持不变。

## 本轮验证门

固定环境：Lean 4.35.0-rc3，compiler `470d5ce1400764999581fd26d5d72b00d990b0f4`；
Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。

CI 使用仓库统一 `restore-lake-cache@ci/lake-cache-test`，普通 Lake 编译，
`cancel-in-progress: true`。完整日志、当前源码清单、提交号与公理输出保存在 Actions artifacts。
全部九个 scope 保留；全部 scope 统一拒绝标准三公理以外的传递依赖。

允许的公理仅 `propext`、`Classical.choice`、`Quot.sound`。actual/presentation 另检查
十二个原名目标的完整类型及公理闭包，包括 `actualHighPresentation`、两 Euler consumer、
`fullHighEulerControl`、pole、conductor、labels、normform、boundary、wholeBoundaryTail、
计数 assembly 和 `highBin`。原码已填不等于此门通过。

当前第一轮整合提交：`465122674ac926868d42be3874de3065fd5da0e5`，
run `41219280369`。该轮不包含后续原名接线，不能作为最终完成证据。
本轮全部原始证明体已填，正在原生编译和修复；最终验证结果另在完成时更新。

AI-assisted：ChatGPT / GPT-6 Astra Pro，2026-11-01。
