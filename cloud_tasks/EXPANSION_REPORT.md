# EXPANSION：真实检测源、同源见证配方与验证报告

分支：`codex/expansion-detector-20261030`；基线：`dtests-handoff`；交付：PR #5。

**整个 EXPANSION 任务尚未闭合。** 本报告严格区分已经由 Lean 检查的定理、已经写完但尚待核验的实际项目接线，以及仍然开放的顶层数据构造。保留 Draft 状态，不把接口校准或部分编译成功当成全项目完成。

主定理的逐字源码陈述另列于 [EXPANSION_CONTRACTS.md](EXPANSION_CONTRACTS.md)，包含全部定理假设；完整 section 上下文和证明在链接的 `.lean` 文件中。

## 1. 已核验的真实终端源与 Fourier 尾项

`Expansion/TerminalFourierTail.lean` 的核心结论直接作用于真实非零整理想有限和。它保留原始 Möbius 系数和所有 Euler 删除零掩码，先作有限 dyadic 分解，再在一个共同的有界 Fourier 频率上提取 inverse/plain 乘积。

这里的三个截断必须区分：终端卷积截断是 `H = U^21`；dyadic 上限是 `dyadicCap (3H)`；用于 Fourier 与完整 annular profile 接合的理想环境集是 `nonzeroTerminalSet (6H)`。源码证明扩大环境集后原始终端源不变。旧的 `nonzeroTerminalSet H` 不足以容纳所有保留 dyadic 尺度的完整 annular 支持。

在扩大后的环境集上，每个系数质量至多为 `(18H)^2 * CZ`。两因子合计保留 `U^84` 的幂次，粗 dyadic 双计数损失至多 `U^2`。对于任何固定 `τ > 0`，取自然数阶数 `N` 满足 `τ*N ≥ 87`，使用半径

```text
R = U^τ / (8π + 8)
```

便得到至多 `K/U` 的尾项，显式阈值 `U ≥ max 2 (8K)` 令它不超过 `1/8`。常数、导数阶数与共同 Fourier 质量都在逐行、逐零点、逐 dyadic 选择之前确定。

GitHub Actions run `41156938468`、pure job `124406070209` 在提交 `8912a81da02c0a9f1c138f23f5a7d3378b4b9e51` 实际完成了这条链的 Lake 编译。日志明确列出 `actual_terminal_product_eventually`、`actual_zero_product_eventually` 及其支持、尾项和频率连接定理，公理均只有 `propext`、`Classical.choice`、`Quot.sound`。该 pure **job 整体仍失败**，原因是另一个 `AnnularCutoffFamily` 模块的证明错误；不能把此部分验证称作整个 job 成功。

## 2. 实际 Hecke 零点到两个饱和因子

下列实际项目端点已写入真实仓库定义，正在逐层核验：

| 端点 | 供应的连接 | 仍作为输入的真实数学条件 |
|---|---|---|
| `exists_original_masked_product` | 普通 Hecke 零点 → 原始终端源 → 同频率乘积 | 固定无穷型、非范数角色、导子与行范数界、零点条带和幂次高度、平滑 cutoff |
| `exists_original_masked_saturation` | 再使用真实有限 Mellin 上界，推出两个单独下界及长度饱和 | 同一角色的缓冲上零点界及明确数值预算；不假设终端源或多项式上、下界 |
| `exists_canonical_row_saturation` | 从原始物理行自动提供无穷型、导子、非范数角色，并统一两个背景的阈值 | 真实 `rowZeroAbove` / `rowZeroBelow`、物理壳层范数和高度几何 |
| `exists_physical_row_detection` | 固定真实 cutoff 和显式损失预算，代入 `U=Z^d`、`T=Z^τ`、相邻物理高度 | `d∈[1/16,1]`、`t∈[1,3/2]`、真实物理零点 bin；无逐行算术或检测结论假设 |
| `exists_physical_witness_cover` | 构造真实 `RecipeAmplitudeData`，证明原有 `WitnessCover` 与六维矩参数盒 | 同一 sector 的有限真实行、上述物理 bin、同一物理点及原始 slot/amplitude 数据 |

完整删除集始终包含固定异常集 `S`、六以上的素理想，以及完整原始行理想的全部素因子。没有将它替换为角色导子支持。

### 实际字符与范数角色的处理

固定背景乘上非主行字符仍可能成为范数角色；因此“行自身非范数角色”不足以处理全部背景。`PhysicalRowPoleExclusion` 使用实际算术角色有限纤维定理构造有限例外行集，再取一个共同范数阈值。它不假设角色映射单射，也不要求背景在原始 `S` 外不分歧。

现有 `MomentData` 的 plain 背景只允许 `1, ψ, ψ⁻¹`。因此不任意扩大背景集合，而取 identity companions `{1}`，仍保留物理族的四个实际字符。对逆向字符先反射零点，再运行检测，得到两个规范方向：背景 `1` 或 `ψ⁻¹` 乘同一个正向算术行字符。inverse 与 plain 由此使用完全同一个角色和频率。

`CanonicalDetectorBounds` 由有限阶行的实际无穷型和原始理想导子定理给出统一参数。导子常数显式包含固定 `S` 的导子预算、域判别式以及两个固定背景的有限导子。

### 预算与选择顺序

令 `A` 为固定 Hecke 高度次数、`η>0`。`DetectorHeightGeometry` 使用

```text
e = ε = min (η/4096) (1/2000)
ceiling = min (1/(64*(A+1))) (η/(2048*(A+1)))
```

该模块当前源码已通过严格选项的本机 Lean 编译，打印公理仅有标准三项。它证明对于所有 `0<τ≤ceiling`，零点高度预算和正、反射两种 Mellin 损失同时成立。Fourier 半径使用 `τ`，零点/上矩形的幂次包络使用 `32τ`，二者不混用。

最终端点先选 `e, ε, ceiling`（覆盖定理还先选计数常数），再允许选择有限高度数 `N`，再选 `τ` 和共同 `Z₀`，最后才选择壳层、bin、行、源指数、零点及频率。因此以后按 `N=ceil(C/e)` 选择缓冲层数不会循环。

覆盖端点还显式输出 `e ≤ lam/1000`。`witnessCover_weaken_loss` 证明在同一 `RecipeAmplitudeData` 上放宽损失参数会保留计数、长度、覆盖与两个 spike 下界，因此可先以 `lam = min lamA lamB` 选检测预算，再接入原有 `lamA` 的见证接口；原始 bin 宽度要求不会被遗漏。

## 3. 同一个实际配方生成见证与矩模型

`ActualCanonicalRecipe` 的两个 presentation 直接使用既有 `PolynomialPresentation`。两个 annular test 都是实际 dyadic profile；cutoff 是同一显式 `cutoffProfile`；源截断保持字面上的 `D=U^t`。归一化后的 inverse/plain 值与原始检测有限和逐项相等，所有原始掩码保持不变。

频率 `ν=2πξ−Im ρ` 可能达到固定倍数的 `T`。配方存储 `ν/C`，在 profile 中恢复 `C*(ν/C)=ν`，其中 `C=3(N+1)`。全局六维参数向量仍以原始 `T` 为锚，没有改成新的物理高度。实际模型满足实部参数范数至多 `8`，虚部参数范数至多 `1+‖heights‖`，并有 `‖heights‖=T`。

`FiniteTerminalLabels` 的离散标签是两个 presentation 与两份真实 dyadic 指数。标签数为

```text
2 * (dyadicCap (3*U^21) + 1)^2 ≤ k * U^lam.
```

连续零点/频率信息由固定 sector 的实际理想嵌入组装成一对理想索引参数映射。无效离散标签使用长度 `(t,0)`，其选中行纤维为空；它们不会被赋予虚假的 spike。

`PhysicalWitnessCover` 构造同一 `RecipeAmplitudeData`，保留输入的候选行、sector、物理点与 amplitude 数据。对每个 `t∈[1,3/2]` 证明原有 `WitnessCover`：有限覆盖、subpower 计数、所有标签的长度条件，以及两种实际模型多项式的下界。其最终陈述没有把这些下界作为假设。

通用配方归一化已经从依赖 named `Moments` 的文件中拆出为 `RecipeDetectorNormalization`。原 `SourceRecipeNormalization` 是兼容包装并保留 named 投影定理；具体检测配方不再通过该包装导入 admitted 的全局数据。

## 4. 与原任务之间仍缺的内容

| 原始目标 | 本次状态和剩余边界 |
|---|---|
| D-EXPANSION / `expansionRecipeRaw` | 仍开放。需将实际全局 buffered row selector、完整物理积分和 amplitude 采样/输运填入一个全局配方。当前实际检测覆盖提供了 witness 子构造，但尚不是该全局配方。 |
| D-SUPPORT | 现有高层支持结论由配方的实际行枚举推出；named 结论仍继承未构造 `expansionRecipeRaw` 的依赖。 |
| EX-HEIGHT-BUDGET / EX-CUTOFFS | 检测子链已有显式共同预算与阈值；五个实际展开估计的联合预算和 `expansionCutoffsRaw` 仍开放。不能用任意正数替代应有的解析预算。 |
| EX-BLOCK-COUNT | 通用实际 shell schedule 的计数已写出，公共 envelope 覆盖 `2^16` guard 与计数常数；named 版本仍依赖 raw recipe。 |
| EX-DETECTOR-WITNESSES | 已构造真实物理零点 bin → 同源 `WitnessCover` 的端点，待最终 native 核验和全局 recipe 接入。完整 `BlockSource` 还需实际 amplitude 与 prime-slot 下界连接。 |
| HB-PRESENT | `actualHighPresentation` 仍开放。必须识别完整 shifted `rowContourBox` 与保留零掩码的实际 label pieces，不能仅挑选任意可加分块。 |
| HB-LABEL-HEIGHT | 高度/label 范围由同一 schedule 与 finite data 推出；named 对象仍依赖前述数据构造。 |
| MI-M-MODELS / calibration | inverse、paired、unmarked 模型现由同一 raw family 定义，具体检测配方也给出真实值等式。generic 等式不等于 raw recipe 已构造；named 校准的 inherited admission 会单独报告。 |

原有 expansion identity、principal/small/large 界及最终 moving-tail 义务仍保留其原始开放状态。没有用空展开、零 amplitude、预设 spike 或新增公理来宣称完成。

还有一个具体的同源等式尚未构造：`PhysicalProbeContours.compensatedRowMellinKernel` 使用原始 marked corrections 与物理权重，而 `RecipeFamily.slotCoefficient` 是配方中的独立字段；`MomentInputs.primePolynomial` 则使用 row character 乘该字段。目前缺少把物理 kernel 的每个素数槽逐项识别成这一配方系数的定理。现有 L-ratio/detector 的分子、分母角色已由 identity companions `{1}` 覆盖，不能把这项系数校准缺口误写成必须扩大 companion 集合。

素数槽估计还存在一个具体接口差异：`PrimeCancellation.Analytic.ZeroFreeData.zeroFree` 要求整个右半平面的无零点结论，而实际 `rowZeroBelow` 只有给定缓冲高度内的控制。因此 `PrimeCancellation.exists_uniform_fixed_window_prime_bound` 不能直接用来完成此处的 bin 振幅上界。新增 `PhysicalLogDerivative` 已写出实际有限高度的对数导数界：由原 Hecke strip growth、右半平面 Euler 上界和中心 Euler 对数界，在半径 `2−β−δ/2` 的圆盘上使用 `|t|+3/2≤Hupper` 证明局部非零，给出 `48*(1+log C+(5/8)log U+heightDegree(K)*log(4+|t|)+A)/δ²` 的界。它还证明同一有限高度的 `ZeroUpperBound H a` 可收紧到 `min a 1`，没有增加全高度控制。`ActualPrimeLogSeries` 进一步使用真实 prime-power ideal 定义 `(n,p)` 索引、`log(Np)*χ(p)^(n+1)` 系数及其范数，并由原导数 Euler 级数证明初始直线校准和绝对收敛；统一质量由只依赖数域与初始横坐标的理想对数 majorant 给出，有限支持由实际理想范数窗口拉回。`ActualPrimeContour` 将这套数据接入已有有限矩形 Mellin 定理，在 `|ν|+H+3/2≤Hupper` 下保留左边主项、两条横边和右线补尾三项，所有 Dirichlet/解析假设都由实际 Hecke 定义供应。这条新增链尚待编译核验。

去对数权也已有实际源码端点。`LogDividedAnnularProfile` 从已证明的紧参数 profile 家族推导任意阶点界、全直线积分和有限高度尾项，常数在素数尺度 `P` 之前选择，阈值为 `exp(4)`。`ActualLogDividedContour` 因而使用同一常数控制所有足够大的 `W(y)/log(P*y)` 窗口，而不为每个 `P` 重新选择一个无法控制的 profile 常数。`ActualPrimeArithmetic` 用真实素理想到真实理想窗口的单射证明线性计数，保留角色的分歧零系数，再由逐项去对数权恒等式拆成真实素数和与高次素数幂尾项。

`ActualPrimeCancellation.exists_actual_finite_height_prime_bound` 将二者接合，给出原始平滑窗口的实际素数和上界：左线主项为 `M*P^(β+δ)*CW`，两条横边合计为 `2*CW*M*P²*(2−β−δ)/(1+H)^order`，右线补尾为 `mass(K,2)*P²*CW/H^order`，三者乘 `1/(2π)`，再加一个统一的 `B*sqrt(P)` 高次幂尾项。`M` 是实际有限零点缓冲推导的对数导数 envelope；全部常数先于角色、尺度和高度。该新端点仍待编译，且尚未把完整原始删除掩码误差、归一化后的统一幂次预算与物理 slot/kernel 校准接入全局 `BlockSource`。

## 5. 已识别并修正的定义/陈述问题

1. 原 Fourier 环境集没有覆盖全部 annular 支持；扩大到 `6H` 并证明源不变。
2. `2π` 的真实 Fourier 频率会消耗高度缓冲；半径改为 `U^τ/(8π+8)`，并保留 `3/2` 余量。
3. 一般固定背景与行的乘积可能有范数角色极点；必须使用实际有限纤维阈值。
4. 任意 companion 不能直接当成 permitted plain background；采用实际允许的两个规范 presentation 并先反射零点。
5. 物理壳层为 `U<N(u)≤2U`，不能送入模型的原 `rows U`。named 模型的 row-enumeration exponent 已使用 `1+log 2/log U`；多项式长度尺度仍为 `U`。
6. wide zero-control bins 重叠，不可视作互不相交。实际 row selector 必须先于 Mellin 积分固定；移动 amplitude 标签与其零掩码保留在积分内部。
7. 小行边界修正为 `1/16`，小行 saving 为 `1/50`；大行自身的 `63/800` saving 没有误改。全局族上界保留真实 `B≤1`。

## 6. 验证与交付状态

固定环境：Lean `4.35.0-rc3`，提交 `470d5ce1400764999581fd26d5d72b00d990b0f4`；Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。原项目选项为 `autoImplicit=false`、`relaxedAutoImplicit=false`。

逐模块源哈希、编译证据、已完成模块的打印公理和取消记录列于 [EXPANSION_VALIDATION.json](EXPANSION_VALIDATION.json)。这份清单记录各版本的具体证据，并单独标出与当前源码是否一致；它不是最新整棵依赖图已经成功构建的证书。仅出现 `Ran` 的日志不计入成功。

`scripts/expansion_verify.py` 记录实际源 SHA-256，在原模块路径构建，再递归检查选中模块中每个声明的公理。构建会继续收集其他独立模块的诊断；任一必需模块失败仍返回失败，并阻止最终公理审计。pure 和 actual 组仅允许 `propext`、`Classical.choice`、`Quot.sound`；skeleton 组单独保留、报告 inherited admissions。审计驱动本身已有 36 声明的 native smoke 检查，未发现非标准依赖。

- 首个 run `41155570075` 在执行 job steps 前失败；它不是 Lean 结果。
- run `41156938468` 的 pure job 实际编译了 68 个任务模块；当时独立复核其中 66 个与当前源码一致。实际终端 Fourier 端点和 57 份有效打印公理记录只包含标准三项。三个来自失败 annular 模块的记录明确排除。
- run `41158889277` 的 pure job `124411822493` 又验证了固定 sector 组装、更新后的 log-profile 层与 `CanonicalCutoff`；它因新 `FiniteTerminalLabels` 的三类 Lean 接口错误失败，修复已在当前源码中。
- run `41158889277` 的 actual job `124411822152` 因 `ExpansionDetectorInitial` 的五处 Lean 化简错误失败；已补删除系数同态的应用引理、用 `map_zero` 处理零理想并移去冗余 tactic，原定理陈述未改，当前修复尚待 CI 重验。
- 本机已验证当前源码的 `DetectorHeightGeometry`、`WitnessHeightNormalization` 和 `FixedSectorParameters`；对应打印公理只有标准三项，固定 sector 的理想嵌入本身不依赖公理。
- run `41161175643` 的 pure job `124418947565` 明确重新编译通过当前 `AnnularCutoffFamily`，三项打印公理都为标准依赖；该组仍因 `FiniteTerminalLabels` 一处 guard 化简和 `RecipeSchedule` 两处依赖索引化简失败；当前源码已修复，等待重新核验。
- 实际 Hecke/Mellin/最终 recipe 接线仍以完成的当前-source native/CI 记录为准，不预先宣称通过。
- 本地大型 legacy Hecke 导入曾发生持续换页：一次导入约 12 分钟、物理读取超过 200GB 而无 proof 诊断，已停止该重复检查并记录为资源取消。它既不是定理失败，也不是编译通过。实际项目链继续由真实 GitHub runner 检查。

按照用户本轮指示，已核对分支全部两个 workflow 的 `concurrency.cancel-in-progress` 均为 `true`，并保留各自的同分支分组键。旧运行已经取消。核验工作流增加了只读恢复后备项，允许尚无自己缓存的组复用本分支已有、同一 toolchain/manifest 的 actual 组依赖缓存；Lake 仍按源及依赖 trace 判定是否重编译。既有保存与上传步骤未变，没有添加额外 native 编译产物上传。

新增 `scripts/expansion_native_verify.py` 为 actual/skeleton 组只读恢复同仓库既有成功 foundation run `41126752041` 的 12 个固定原生产物。它重新下载固定提交 `984b0de3…` 的源码，复算 6,028 模块及配置 fingerprint，检查原 job 成功、外层 ZIP 与内层归档哈希、原编译器签名和模块伴随文件，并仅复用当前源码与所有传递项目依赖均完全相同的模块。其余模块在隔离路径按原 package 选项重新编译；不生成或修改 Lake trace，不将新 native 输出放入既有 cache-save 或日志上传路径。根仓库证明继续使用两项 implicit=false；vendor 依赖保持原 package 的真实选项。完成全部必需编译后，仍执行同一个逐声明递归公理审计，任一失败会阻止该审计。离线源码/配置 plan 与一个真实 ZIP 恢复烟测已经通过；这只验证恢复机制，不表示目标 Lean 证明已经编译成功。

本报告在最终交付前还会用最新完成的源匹配记录更新。只有明确完成的编译和对应公理结果才计为验证成功。
