# HIGHBIN 构造与验证历史记录

> 本文记录 PR #7 在 `d88663c8` 的历史阶段。当前共享源、原名接线、量词修正与验证门见 [本轮整合报告](INTEGRATION_20261101.md)。

本分支承接 HIGHBIN 的实际 Euler 校准、例外表、移位范数形和边界移动。
这里严格区分源码中已写出的证明、通过原生 Lean 检查的证明，以及与旧的
`Base.highExpansion` / `actualHighPresentation` 之间尚未完成的共同数据构造。
具体编译状态以本报告末尾及 `verified_*.json` 的精确源码记录为准。

## 1. 使用同一份实际数据

令 `K` 为数域，`c : TargetContext K` 为项目原有目标上下文。其族参数满足
`7/8 < B ≤ 1`、`0 < lamA ≤ 1/1000`、`0 < lamB`，并提供原有字符包共同零点边界。
所有实际算术、测试函数、Haar 测度和目标字符均取自该上下文的原有构造。

本轮固定

```
lambda = min lamA lamB
e = lambda / 100
zeta = min (1/96) (lambda/100)
upper = 13/16 + zeta
Theta = {1}
```

其中 `0 < e ≤ 1/10000`、`0 < zeta < 1/48`。`targetEuler` 按定义就是
`arithmeticHighEulerData`，没有以一条待证相等式连接到任意 Euler 提供者。
原来的 `rayFilter` 定义为 `∅`，所以目标边界与实际分片积分使用同一个 prime window。

为消除数据与证明的循环导入，原 `Base` 的上下文及原始数据声明逐字移到
`BaseContext`，原 `Theta` 的算术校准声明逐字移到 `TargetArithmeticData`。
旧模块导入并重新导出这些声明。`ActualTargetEuler` 将目标专用校准与一般算术
Euler 构造分开；`ActualCanonicalData` 再将共同目标数据与较深的范数证明分开。
这没有改变原 `highExpansion`、`rows_in_norm_envelope` 或其未完成状态。

## 2. 行分配、壳与高度由构造给出

取 `M = ceil(1/e)`。`BufferedDetectorGeometry` 的有限离散论证给每行选择
一个索引 `(i,j) ∈ Fin(M+1) × Fin(M+1)`，得到
`a = 51/100 + j*e`、`51/100 ≤ a ≤ B`。非底层 bin 有实际选中的零点；
上检测高度处所有相关零点的实部不超过 `a+2e`。输入只有原共同零点边界，
没有输入待证明的 bin 数目或边界估计。

对任意实际有限行源集，`assignedRows` 是这一选择函数的纤维。因此这些集合
两两不交、覆盖源集，并严格保持有限求和。只保留非空纤维，块数不超过
`(M+1)^2`。

内部高度统一取 `H = max(T, Z^kappa)`，检测尺度取 `2H`。对应轮廓高度恰为 `H`，
上检测高度至少 `2H+2`。范数形与边界移动使用这一份几何数据。

dyadic 壳采用原行范数 `Nu`，区间是

```
Z^d < Nu ≤ 2 Z^d.
```

有限壳数为 `ceil(((upper-1/16)/log 2)*log Z)`；壳指数
`d_j = 1/16 + j*log 2/log Z`。严格下端点与闭合上端点给出唯一壳分配。
最终壳仍与原有限源集相交，保留原上界 `Nu ≤ Z^upper`，不会多算末壳超过截断的行。
目标源集是 `Z^(1/16) < Nu ≤ Z^upper` 的实际非主频行。

`ActualCanonicalFamily` 用依赖有限类型同时记录壳与非空检测纤维。
对每个 `eta>0`，它的实际基数满足

```
card(family) ≤ (M+1)^2 * (2 + ((upper-1/16)/log 2)/eta) * Z^eta
```

（`Z≥1`）。这是实际索引类型的基数定理，不是一个单独假定的 block-count 字段。

## 3. Euler 初始校准和例外因子

`targetEuler_input` 的结论是原项目的

```
TRowEulerInput K S (probeData K c) (targetCharacter K c) (targetEuler K c).
```

其算术路径使用实际有限商环 Fourier 和、素数幂 Gauss 计算、含交叉相位的 CRT、
四理想级数的绝对收敛与初始 Euler 乘积。CRT 保留各交叉符号，最终在实际归一化
系数中证明相消；不将单独的原始有限 Poisson 因子错误地宣称为无相位乘法函数。

`targetEuler_exceptional_control` 对所有 `51/100 ≤ a ≤ B`、实际行 `u`、标记集合
`Q` 及例外素理想 `p∉Q`，在

```
Re(s)=a+16e,   Re(w)=1-a-6e,   Re(z)=17/50
```

上给出常数 `9`、截断 `2`。这样的例外素理想确实整除行理想，因而实际有限有理表满足
`|H_p-1| ≤ 9 q^(-10e)`。全部虚部均不受限制。

正则分支满足 `|H_p-1| ≤ (11/negativeStripEulerMargin) q^(-1-10e)`。
`targetEuler_full_control` 将初始输入和两分支的统一界连接到同一个 `targetEuler`，
可取统一常数 `max(9,11/negativeStripEulerMargin)`。范围允许 `B=1` 以及负的 `Re(w)`。

这里继续使用已修正的 `rowEulerRegion`：必须包含 `Re(w+6z)>1` 与 `Re(s+6z)>1`。
缺失这两个条件的旧区域不能支持其声称的正则 Euler 收敛。

## 4. 原式 (6.24) 的实际计算分片

`ActualNormFormComputedPacket` 用实际完整修正振幅定义有限标签、标签行集、
均值和每一个受限高度积分。标签类型固定为 `Fin slots → Fin(N+1)`，数量恰为
`(N+1)^slots`。没有从总和恒等式推测单个分片，也没有把分片上界存为输入数据。

`targetCanonicalNormForm` 首先选取 `kappa, theta, N, C, Z0`，满足
`kappa>0, theta>0, C>0, Z0≥1`；之后才量化 `Z,T,d`、有限源掩码、非空检测纤维、
标签及显式 witness subdivision 配方。对

```
Z≥Z0,  1≤T≤Z^kappa,  1/16≤d≤1
```

它证明实际槽上下界、分块的最终轮廓恒等式及

```
sum_(u in A_label) norm(actualRegionPiece u)
  ≤ C * card(A_label.rows)
      * Z^(3/16 + moderateExponent d (2a-1) A_label.mean 0 + lambda/4).
```

`targetCanonicalParameters` 从这个已证明的存在命题中选择一组纯数值，随后
`targetCanonicalParameters_spec` 证明这组数值的性质。该记录只含数值，不含调用者
必须提供的分析估计。

`chosenTargetFamily_normForm` 将这一结论用于同一份有限 dyadic 家族，并利用
`lambda≤lamB` 得到原 HB-NORMFORM 的准确 `lamB/4` 损失。其规模范围是
`Z≥max(Z0,2)`，高度范围仍为 `1≤T≤Z^kappa`。

### 全尺度积分恒等式

一般计算包先保留真正可积的行，使有限积分分割在 totalized Bochner 积分下有合法依据。
`ActualFinalContourIntegrability` 进一步证明：在上述目标几何范围内，对每个 `Z>0`、
`T≥1`，所有分配行的最终核都在整个紧高度盒上可积。分母字符有 norm pole 时，
其倒数通过 pole-cleared 函数解析延拓；分子线严格避开极点。

因此 `canonicalRows_integrableRows_eq` 在这些尺度上证明过滤器等于原分配行集，
`canonicalBlock_value_eq_final` 与 `chosenTargetFamily_value_eq_final` 识别完整的原行
最终积分。这个步骤不是把可积性当作假设，也不借助尚未证明的范数估计。

## 5. 同一行集上的边界移动与尾项

每块边界按定义为同一份分配行上的

```
initial(s=B+20e, w=1-a-6e, z=17/50)
  - final(s=a+16e, w=1-a-6e, z=17/50).
```

`maskedBoundaryPiece_eq_initial_sub_block` 将最终积分替换为上节实际计算块值。
整个移动没有在两条轮廓之间改变行集。

对一般数域、原测试函数、Borel 结构和 Haar 测度、有限伴随字符包（含 `1`）、
`0<e≤1/10000`、`51/100≤B≤1` 以及原共同零点边界，
`exists_maskedShellBoundary_external_tail` 的量词顺序是

```
exists Z0≥1, forall N:Nat, exists C>0,
  forall ray source Z T kappa d,
  Z≥Z0 -> T≥1 -> 1/16≤d -> d≤1 ->
  norm(shellBoundary) ≤ C Z^13 T^(-N).
```

`ActualDyadicBoundary` 再对实际壳求和，得到 `C Z^14 T^(-N)`，阈值仍先于 `N`。
常数统一于源掩码、ray filter、内部高度指数与合法上截断；源集可以依赖 `Z,T`。
`dyadicBoundary_powerHeightTailBound` 与目标专化 `chosenTargetFamily_boundary`
给出原 `PowerHeightTailBound`，可取尺度指数 `R=14`、高度次数 `A=0`、ceiling `1`。
这些是实际积分移动、水平面与尾积分估计的后果，没有输入另一条边界控制假设。

## 6. 旧命名接口仍须协调的部分

本轮将 `ActualHighPresentation.euler` 改为固定算术数据的派生 accessor，原结构中
其余数据及身份字段保留。`euler_eq_arithmetic` 是 `rfl`；不再假设一条待证明的
provider 相等式。原 `highInitialEulerControl` 直接调用 `targetTRowEulerInput`，
`highExceptionalEulerControl` 调用实际有限表估计，常数为 `9`、cutoff 为 `2`。
这两处源码中的 `sorry` 已替换，命名模块的完整原生复验仍待完成。
命名例外定理仍使用 `HB-PRESENT` 提供的正 buffer 与 bin 范围，必须披露这项
继承依赖；对任意 presentation 参数的对应定理不自行调用 admitted 构造。

旧 `ActualHighPresentation` 的两条精确身份只约束聚合和。
`FinitePieceGauge` / `ActualPresentationGauge` 证明：若某标签含两个不同的行，可以对
两个贡献加上互相抵消的量，保留每个标签的和、总块值及其他已有字段，同时令分片范数和
任意大。因此聚合身份不足以证明单个分片的 HB-NORMFORM。这一结果针对任意满足旧接口
的 presentation；它不是对尚未定义的具体 `actualHighPresentation` 的反例。

另一个必须修正的身份是旧 `shifted_identification`：它积分的是整个原始 buffered bin。
实际选择纤维只包含在该 bin 内；不同原始 bin 可有重叠。子集不能直接替换为相等，
更不能在最终壳丢弃原上截断。修正后的接口应将 `fixedRows` 定义为实际分配纤维，
并在初始与最终轮廓中都使用它。

本轮没有以额外估计假设或空 witness cover 来填掉旧 `HB-PRESENT`。要将新构造接入旧
`D-EXPANSION`，还需由共同展开任务实现同一份真实 witness 选择、覆盖和饱和配方，并使
`Base.highExpansion` 的块、标签、实际槽值和分片就是这里的构造。
完整槽有 `-M + E_regular + E_valuation1 + E_repeated` 四项；不能仅用主项 prime polynomial
的身份替代完整槽与 moment 数据之间的校准。

因此旧文件中的其余命名 admitted obligations 没有因为这些新端点而自动消失。
剩余接口是具体数据构造及其身份，不允许把范数形、例外 Euler 界或边界衰减改为输入字段。

## 7. 验证记录（持续更新）

- `4f733f5f9a616332feffeed212aed57972daf012` 的 GitHub 原生 core job 已通过：
  66 个模块、533 个公开声明，仅允许 `propext`、`Classical.choice`、`Quot.sound`。
  新 detector、有限分片 gauge 和三个 dyadic 模块均在内。
- 三个 dyadic 模块、有限 gauge 和 detector geometry 另有本地原生、源码未变的成功记录。
- `011125ed` 的 Mellin 分组完整通过：6 个实际模块、67 个公开声明的类型及公理
  全部检查完成，额外公理集合为空。精确源哈希与下载证据见
  `verified_mellin_axioms.json`；这一结果不替代后续 Euler、范数形与边界模块的验证。
- `357effad` 的 Fourier 分组完整通过：8 个实际模块、162 个公开声明的类型及
  公理检查，额外公理集合为空。实际 Gauss/Fourier/Poisson、CRT、初始绝对收敛
  的精确源绑定见 `verified_fourier_axioms.json`。后续 Euler 乘积校准仍单独验证。
- `f1dd2fc` 的 CI 已实际编译 `ActualGeneratorPowers`、`ActualPrimePowerSymbols`、
  `ActualGaussData`、`ActualInitialAbsolute` 四个模块；这次输出中的 12 项公理检查
  仅含三项标准公理。该 Fourier job 整体仍失败，不能把它记作完整 Fourier 审计通过。
  精确源码绑定见 `verified_arithmetic_foundation_ci.json`。
- 固定 Lean 为 `4.35.0-rc3`，Mathlib 为 `0493595ecd5da8ef14742febab99728f98e948e8`。
  完整 Mathlib 入口已原生编译成功；复用的依赖按源码、编译器及所需 sidecars 核验。
- 实际算术、积分及本轮新目标端点仍在原生验证和修复中。失败编译的 recovery `sorryAx`
  不作为通过记录；源码清单、静态依赖检查也不作为 Lean 编译通过。
- 对实际模块必须记录传递公理依赖，尤其项目现存的上游输入。原有上游 admission 与
  本轮新声明自身是否包含 admission 分开报告。
- 新增独立的 `euler`、`normform`、`boundary`、`canonical`、`presentation` CI 分组，各自编译实际
  模块并检查整个 HIGHBIN 支持依赖闭包的公开类型与公理，不取消原四项检查。
  `euler` 与 `boundary` 拒绝标准三公理以外的依赖。范数链已知使用原
  `PrimeNormalizer.normalizer_smallPower`，它继承 `window_prime_lower` 的
  `PR-WINDOW-PIT` admission；`normform` 与 `canonical` 完整披露这项 `sorryAx`
  传递依赖，并拒绝其他新增公理。通过这两个分组不代表该上游素数分布输入已证明。
  `presentation` 同时检查固定 Euler 数据后的旧命名消费者，披露现存骨架的
  `sorryAx` 依赖。独立分组合并覆盖全部 79 个实际支持模块，完整 `actual` 检查保留。

旧 HIGHBIN 原有六处 `sorry`，目前源码剩四处：`HB-PRESENT`、`HB-LABELS`、
`HB-NORMFORM`、`HB-MOVE-BOUNDARY`。两条 Euler 命名证明及其他待编译源码，
均须在完整原生复验后才能列为验证成功。
