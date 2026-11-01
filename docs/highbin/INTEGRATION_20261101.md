# HIGHBIN 原始接口接线（2026-11-01）

本轮从 PR #7 的 `d88663c8e2c9461cdd942267631e829d72d1f9b3` 继续，
合入 PR #5 的实际共享源 `0263481ab8c8f2ef30d909f6a665ed22d64e5b8c`。
随后核对 #5 的 `77dbe777f479823d0bc830f82a15e594a17191b7` 与 #10 的
`5adae18b0928aa7b33afc1472b61ffc7408805d8`，采用 #5 最新的八个相关 Lean
文件，统一共享参数与原核解析性、Poisson、floor-bin 和完整 correction 的原生修复。
再按 owner 的 `2a8298882530d5c4c3212cda05db8c92017b915a` 恢复原参数存在接口的
兼容签名，采用独立 bounded constructor，并同步初始行和的函数等式修复。
再核对 owner 的 `0460b9c217f4a272d6cad6158ffc321d0a596bf8`，精确同步标签积分
构造、初始 Mellin 恒等式、中等行核衰减与初始行截断四份文件。共享数据、标签和
SourceData 保持一致；已在本分支原生通过的其他共享证明保留其已验证的等价写法。
继续对齐 `1ff1c2bcfb21c49c484c08db91d137064d306f58` 的主行核、z 方向移线、
初始补偿和标签积分四份证明修复，并沿 owner 的小行和写法处理其最新原生诊断。
该次 owner 差异仅涉及证明体，不改变共享接口或实际数据。
再核对 `6709923e324f5ee3e4d529dc46a505b6b47de49b`：当前依赖链的三个既有
共享证明修复均已由本分支覆盖。按其 run `41265148631` 的同源原生日志，
继续修复主行余项的函数别名、大行 subtype 求和、外部尾项的负实指数换算及
配方行和的 `filter` 表示。这些修复已在 #5 评论6552483360、6552529938提前协调，
仍仅改变证明体。
继续核对 owner 的 `6d256b9d63f71bd900c09247a42ee4798d5731cb` 与
`3c0f712627c8cc195c814cceec56de4a24d0862d`：共享定义、SourceData 与公开声明
均未改变。其同源主留数、初始搬运和配方余项诊断已在本分支修复；最新初始搬运及
配方余项两份源码与 owner 逐字相同。大行求和保留本分支已在 run `41267214644`
fresh Built 且三条打印均仅标准公理的显式 `tsum_subtype` 证明，不以尚未验证的
等价写法替换它。证明修复与直接消费者的定点消歧已在 #5 评论6552808905、
6552858619、6552917415中协调；仍须经过本分支完整原生验收。
源码构造与原生验收分开记录：完成声明以固定工具链的完整编译和严格公理门为准。
最新提交、验收运行、剩余工作及最终状态统一记录在
[PR #7](https://github.com/Rogerhu12/hecke-seven-eighths/pull/7) 的说明中。

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

`PhysicalRecipeParameters` 保存两个额外的已证数值约束，仍保留原全尺度 source
与全部标签 provenance。先前本方独立提交 `a9d412d` 用额外的 bounded constructor
保留旧存在定理类型。共享源 owner 在 `7d598d9` 一度直接加强两个原存在结论，
随后于 `2a829888` 恢复 `exists_physical_recipe_parameters` 和
`exists_physical_recipe_expansion` 的原公开类型，另由
`exists_bounded_physical_recipe_parameters` 提供两个预算证明给参数构造消费者。
本轮统一采用 owner 的最新兼容接口、cap transport 和参数构造，不保留第二份共享定义。
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
4364–4386行的内部分析阶、随后高度及常数/阈值选择顺序。

### 同一 Poisson 标量

#5 校准的固定 `physicalPoissonScalar` 保留在真实核中。旧 HIGHBIN 的两个内部 tuple
恒等式右端与 profile 因子显式同步这一标量；边界常数与范数常数吸收其范数。
对应论文3529–3532行的固定 Haar 归一化。原 contour、原 probe 和原边界方向保持一致。

### 旧范数形支持接口的实际归一化

原 `exists_actual_primeNormalizer_inverse_subpower` 的类型保持不变。合入的当前
基线已经用 `WindowPIT.window_prime_lower` 与
`TauCeti.primeCount_univ_isEquivalent_div_log` 证明了实际素数窗下界；
第一轮 run 41219280369 的 normform 日志实际编译该支持引理，并打印仅三标准公理。
历史报告所称未完成 PIT 已不适用于当前基线。

完整接线提交曾暂时切到 #5 的另一个实际 normalizer producer 并增加全复无限位参数；
核对上述原生证据后，恢复原公开接口，新物理核也直接消费已证的同一个空 ray
`primeNormalizer K S g ∅ Z` 上界。其固定常数吸入核常数，指数 `nu` 仅计算一次。
对应论文4339–4347行固定非负、非零、互不相交的实际素数窗，以及原共同归一化。

### 全复性辅助引理的实际 probe 输入

`ActualPhysicalPrimeSlotBound.all_complex_of_original_probe` 的旧源码只在证明中引用
节变量 `P`，结论本身只出现 K。Lean 因此未保留 S/P，既无法绑定证明中的 `P`，
也无法接受其消费者已有的 `K S P` 调用。修正版用 `include P in` 明确保留
同一份 `ProbeData K S`，从其中的 `primitive12` 调用已证的全复性引理。
这是局部工具引理由错误的 `K → ∀v, v.IsComplex` 恢复为原意的
`K S (P : ProbeData K S) → ∀v, v.IsComplex`，不增加主 prime-slot、HIGHBIN
或最终一般数域定理的假设。此项已在 #5 评论6546921509提前协调。
论文377–378行先取 `K = F(ζ₁₂)`；420–424行的物理分析固定该含十二次单位根的域，
因此全复性正应从已有实际 probe 的算术数据读取。

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
该轮 core、mellin、fourier 通过；normform 实际失败日志已下载并核对 artifact
SHA256，原 tuple 重排超时、continuity composition、SharpFactors 和 scalar
未解目标分别修复，共享四处错误按上述 #5 最新修复对齐。
完整原名接线已发布为 `a63e791f87d5a3ddadfce2cc3f2fef3146d2e59f`。
该轮 run `41220839679` 的 core、mellin、fourier 通过，六个主体组由后续修复取代。
随后 `525f1c4fc34271043a27bcf4f5c23990e0bd9e7c` 的 run `41222277026`
再次通过这三个 scope；80 个 module 源与该提交逐文件匹配，完整声明审计仅三标准公理。

从 #5 run `41221403216` 的 artifacts 取得与 `525f1c4` 同源的进一步原生诊断，
下一批只修 `SmallRowCorrection` 的常数化简/非负性、moderate joint analytic
helper 的命名空间、floor provenance 的 cap 重写以及 `ActualCompensationSlotIdentity`
的名称和索引透明性。另采用 #10 `fc87b44` 的 `PhysicalInitialMellinTerm` 三处
证明修复。共享定义与声明不变，已在 #5 评论 6546575780、6546605675 提前协调。
同一 #5 日志实际编译了与当前源码匹配的 `PhysicalCompletedPoisson`、
`ActualRowKernelHolomorphy`、`JointAnalyticLimit` 和 `ActualNormFormFullCorrection`，
其打印的22项声明仅三标准公理；这不替代本分支原名目标的最终审计。

run `41222277026` 的 normform 随后自然结束：51模块源清单全部对上 `525f1c4`，
其中29模块本轮 fresh Built。旧 tuple、L-ratio、SharpFactors、完整 correction 与
`PhysicalNormScalar` 的首因已经消失；这些模块打印的相关声明均仅三标准公理。
本轮新诊断推进到 `ActualKernelEnvelope`、boundary integrability、旧 slot cap、
新 conductor product，以及前述共享 slot identity / floor assembly。下一批同时修正
这些具体行范数透明性、实/复常数、连续函数参数推断和根命名空间问题，并修复其
直接消费者的同型问题。失败声明的 Lean 错误恢复输出不作为公理审计通过的证据。

修复提交 `b517766e0c724b17deccf6d196c423e3e2cf648b` 的 run `41224364578`
再次通过 core/mellin/fourier。normform 与 boundary 的源码清单和 artifacts 已核验；
该轮实际编译了 `ActualKernelEnvelope`、`ActualBoundaryIntegrability`、
`ActualNormFormSlotCap`、`ActualPhysicalConductorProduct` 和共享 slot identity，
相关已打印声明仅三标准公理。`ActualContourTransport` 也 fresh Built，五条
实际 Fubini/矩形身份/外部 tail 声明打印仅三标准公理。
下一层失败推进到 `ActualBoundaryEstimate`、旧 amplitude 连续性、物理 prime-slot
消费者，以及共享 outer kernel、Mellin absolute 与 large-row all-scales 证明。
本轮按实际诊断补齐显式范数基底、常数非负性、函数等式/连续性组合及上述局部 probe
输入，并采用 owner 的 cap transport。尚未到达的高层仍须完整原生验证。

上述每一批源码修复均须经普通 Lake 和完整严格公理门验证。这里的历史失败日志
用于说明修复依据，不代表最终验收；最终运行与逐 scope 结果集中记录在 PR #7 说明中。

AI-assisted：ChatGPT / GPT-6 Astra Pro，2026-11-01。
