# LOW-FROZEN-CUBE：从原始有限行到统一终端界

## 1. 交付范围与验证状态

本说明对应任务中的引理 4.8 行分解部分，并说明其如何消费已经证明的 LOW-HYBRID，得到论文的 can-Eref 与 can-terminal-ledger。证明在自包含素理想坐标模型中完成：底层对象是交换幺半群，其素指数给出到有限支撑自然数向量的乘法等价。没有假设最终行正常形、完整立方拆分函数、原行等式、组装后的局部系数界或目标能量估计。

目标环境是 Lean 4.35.0-rc3、Mathlib 0493595ecd5da8ef14742febab99728f98e948e8。原始加权行出口、LOW-HYBRID 应用、局部预算、源能量账本、单块终端界、所有冻结数据的统一常数、实际变化支撑下的全行聚合，以及全族标准 ε 终端界，均已在该环境编译通过。两个新命名空间的全包公理审计通过，共检查 955 个定理，包括内部辅助定理；每个定理的全部公理依赖均属于 propext、Classical.choice、Quot.sound。

任务允许在项目传递依赖缺失时先交付 Mathlib 自包含模块。本轮没有修改输入材料，也没有把缺失的项目名字伪装为已验证接口。外部理想、实际允许生成元和反射公式的字典见第 10 节及 [WIRING_NOTES.md](WIRING_NOTES.md)。

## 2. 公开入口与常数量词

最底层精确出口是 [ColumnNormalization.lean](HeckeSkeleton/LowFrozenCube/ColumnNormalization.lean) 中的 **FrozenReduction.Data.weighted_raw_frozen_row_block_exit**。它的左侧是原始行块上、原始局部指标有限和的平方范数；结论同时构造单位模界的最终系数，并给出与 LOW-HYBRID 能量的严格等式。

完整上界入口如下。表中 FrozenReduction 表示命名空间 HeckeSkeleton.LowFrozenCube.FrozenReduction，Data 子命名空间另行写出。

| 入口 | 结论与使用范围 |
|---|---|
| Data.uniform_weighted_raw_hybrid_bound | 固定全局算术数据与 ε 后先选 C₀，再对全部冻结 Data、尺度、有限行集和系数给原始加权源能量的混合界。 |
| uniform_source_energy_ledger | 使用同一个 C₀，接上局部最低指数预算、范数归一化和共同核标量，得到实际单块源能量的反射指数界。 |
| uniform_source_energy_terminal | 将上述实际能量接入 can-terminal-ledger 的三个指数分支。 |
| uniform_source_energy_power_saving | 在明确的步长和保留块容差下，给单块实际能量的 F−c/4 界。 |
| uniform_family_source_energy_ledger | 对原始行按实际强幂／受支撑因子对精确分块；允许每一对使用不同的有效冻结数据和不同的反射支撑，再合成全行能量界。 |
| uniform_family_source_energy_subpower | 事先固定长度预算 W>0 和目标 ε>0，内部选择小幂参数，将混合界及块数损失合为一个 ε。 |
| uniform_family_source_energy_terminal | 上述全行能量满足 terminalBound+ε 的界。 |
| uniform_family_source_energy_power_saving | 上述全行能量满足 F−c/4 的界。 |

这些统一入口的关键量词是：

\[
\begin{gathered}
\text{固定 }(A,\mathrm{coords},\chi,\mathcal N,q,
  \text{线性计数},\text{二次筛},\text{三次筛},W,\varepsilon),\\
\exists C>0,\quad
\forall\text{ 尺度、有限原行集、冻结数据族及原始系数族},\quad
\text{原始支撑和局部条件}\Longrightarrow\text{实际源能量上界}.
\end{gathered}
\]

其中 W 仅在将所有小幂合成一个给定 ε 的最后三个入口中需要。常数在 ordinary、digit、minimum 和每个块的反射支撑之前选择。早期固定 Data 的同名短入口仍保留，但最终统一性由 UniformWeightedHybridBound、UniformSourceLedger、UniformAggregateSource 里的量词顺序明确证明。

全族能量的定义是：每个实际强幂／受支撑因子对选择一个有效的原始源块，再对原行的平方范数求和。该定义允许该块内任意有限局部输入；它不把不同最低指数纤维的复数和暗中换成其能量和。需要组合额外局部切片时，应按真实外层公式使用有限和不等式和已证明的小幂切片计数。

## 3. 素坐标、三种支撑与自然行分解

基础输入是

\[
\mathrm{coords}:A\simeq_\times
  \operatorname{Multiplicative}(\iota\to_0\mathbb N).
\]

素位类型 ι 可以无限。每个元素自身的赋值向量有限支撑，因此素乘积、支撑裁剪、商以及最小指数构造都是有限的。[PrimeCoordinates.lean](HeckeSkeleton/LowFrozenCube/PrimeCoordinates.lean) 证明赋值的单射性、乘法与幂公式；[PrimeProducts.lean](HeckeSkeleton/LowFrozenCube/PrimeProducts.lean) 由逆等价构造 primeElement 并证明

\[
a=\prod_{\mathfrak p\in\operatorname{supp}(a)}
\mathfrak p^{v_{\mathfrak p}(a)},\qquad
\mathcal N(a)=\prod_{\mathfrak p\in\operatorname{supp}(a)}
\mathcal N(\mathfrak p)^{v_{\mathfrak p}(a)}.
\]

三个有限素集承担不同作用：

| 集合 | 含义及约束 |
|---|---|
| base | 原始行分解中固定的 label／puncture 素位。 |
| Data.support | 固定强幂部分后反射行与活动标记须避开的集合。全族聚合中实际取 base∪supp(k_pow)。 |
| Data.ordinary | 活动普通素位集 f₀，包含于 Data.support。a′ 与 a_min 支撑于此；对偶平方自由列 c′ 和补立方 n′ 只避开此集合。 |

因此 c′、n′ 允许含有 Data.support 中不活动的普通素位。完整立方拆分按 ordinary 进行，不能按较大的 support 裁剪。剩余行 d 和标记 P 则仍避开整个 support。

[RowCoordinates.lean](HeckeSkeleton/LowFrozenCube/RowCoordinates.lean) 在每个素位按原行赋值直接定义：

- 赋值至少二的整段指数放入 k_pow；
- 赋值恰为一且素位属于 base 的部分放入 k_sup；
- 其余赋值恰为一的部分放入 d。

由此证明真实等式 k=k_pow·k_sup·d、三个因子两两互素、后两个因子平方自由，以及 d 避开 base。固定前两个因子的原行有限纤维称为 rowBlock，剩余行映射在该纤维上单射；能量重索引为精确等式。

[FrozenSupportExtension.lean](HeckeSkeleton/LowFrozenCube/FrozenSupportExtension.lean) 进一步证明：固定 k_pow 后，将 base 扩成 base∪supp(k_pow)，不改变该块的 k_sup、d 和 rowBlock。新增素位在原行上的赋值已至少二，不会被重新划入任何赋值一的部分。这一步使变化的反射支撑与原始行分块真正相容。

## 4. 从局部表得到合法指数和实际最低指数纤维

[LocalTable.lean](HeckeSkeleton/LowFrozenCube/LocalTable.lean) 定义显式三余数表。记 q 为素范数，first 为第一 Whittaker 标量：

\[
W_q(e)=
\begin{cases}
q^{-e/3},&e\equiv0\pmod3,\\
q^{-\lfloor e/3\rfloor}\,\mathrm{first},&e\equiv1\pmod3,\\
0,&e\equiv2\pmod3.
\end{cases}
\]

普通局部系数在 e=0 时为 atZero(j)；e>0 时仅 digit j=4 可以非零，此时为 prefactor·W_q(e)。这些是定义中的实际表项。禁用余数类为零、正指数只允许 digit 4、非零项指数合法均由该定义证明。

合法指数的规范分解保留零指数的特殊性：

\[
e=e_{\min}+3x,\qquad
(e_{\min},x)=
\begin{cases}
(0,0),&e=0,\\
(1,(e-1)/3),&e\equiv1\pmod3,\\
(3,e/3-1),&e>0,\ e\equiv0\pmod3.
\end{cases}
\]

因此 e_min=0 时不能夹带一个任意正立方指数。Valuations 中的 CanonicalFrozenPair 正是包含这个限制的唯一性条件。

[RawInput.lean](HeckeSkeleton/LowFrozenCube/RawInput.lean) 从原始有限输入 (a′,n′) 出发，先取实际 minimumFactor(a′)=a_min 的纤维，再保留显式局部乘积非零的项。它证明这些项逐素合法，且实际构造的 residualCubeFactor 满足

\[
a'=a_{\min}x^3.
\]

原指标到 (x,n′) 的映射在固定 minimum 的纤维上单射。随后 [RawSource.lean](HeckeSkeleton/LowFrozenCube/RawSource.lean) 在有限和内部删除零项并重索引。因而最终出口没有额外要求调用者证明 admissibility、CanonicalCube 或某个给定的源行等式。

## 5. 三类系数、混合相位与完整立方

[CoefficientSeparation.lean](HeckeSkeleton/LowFrozenCube/CoefficientSeparation.lean) 明确定义未冻结的三类系数，而不是从一个已分离的行开始。记普通素位相位乘积为 I₋、I₊，则其形状为

\[
\begin{aligned}
\pi(P;a')&=a_0(P)\chi_P(a')^2 I_-(P),\\
\rho(d;a')&=\rho_0(d)\chi_d(a')I_-(d),\\
\lambda(c';a')&=\lambda_0(c')\chi_{c'}(a')^2 I_+(c').
\end{aligned}
\]

I₋、I₊ 使用真实局部 phase digit。该 digit 在合法的 e=e_min+3x 下不变。在 a′=a_min x³ 后，支撑给出 (P,x)=1 和 (c′,x)=1，六次幂律给出

\[
\pi(P;a_{\min}x^3)=\pi(P;a_{\min}),\qquad
\lambda(c';a_{\min}x^3)=\lambda(c';a_{\min}),
\]

\[
\rho(d;a_{\min}x^3)=\rho(d;a_{\min})\chi_d(x)^3.
\]

剩余行相位在平方范数中模为一；χ_d(x)³ 留在混合行内部。

[FrozenReduction.lean](HeckeSkeleton/LowFrozenCube/FrozenReduction.lean) 的 mixedPhase 保留冻结前的全部三类混合相位。由互反与精确六次幂掩码律

\[
\chi_a(b)^6=\mathbf1_{(a,b)=1}
\]

证明

\[
\begin{aligned}
\chi_d(P)^4\chi_P(d)^2&=\mathbf1_{(P,d)=1},\\
\chi_d(c')\chi_{c'}(d)^2&=\chi_d(c')^3,\\
\chi_P(c')^2\chi_{c'}(P)^2&=\chi_P(c')^4.
\end{aligned}
\]

最后一个幂等于 LOW-HYBRID 使用的整数幂 χ_P(c′)^(−2)：非互素处符号为零，互素处六次幂为一，两种情况都由代码处理。

完整立方 b=xn′ 使用唯一的 ordinary／补 ordinary 坐标拆分。在 x 支撑于 ordinary、n′ 避开 ordinary 时，cubeSplit(b)=(x,n′)，乘积映射因此单射。P 避开较大反射支撑，而 x 支撑于 ordinary⊆support，所以 (P,x)=1 是支持条件的结论。于是

\[
\mathbf1_{(P,n')=1}=\mathbf1_{(P,b)=1}.
\]

两个曾经可能被当作占位桥的 hsplit 与 hPx 均在 sourceRow_eq_hybridRow 的证明中构造。

取 a(P)=π(P;a_min)，β(c′,b) 用上述唯一拆分读取剩余列系数后，源行严格变成一个模一行相位乘以下式：

\[
\sum_P\frac{a(P)}{\sqrt{\mathcal N(P)}}\,
\mathbf1_{(P,d)=1}
\sum_{c',b}\beta(c',b)\,
\chi_d(c'b)^3\chi_P(c')^{-2}
\mathbf1_{(P,b)=1}.
\]

a 仅依赖 P，β 仅依赖 c′、b；二者均不依赖剩余行 d。完整立方 b 不要求平方自由，c′ 与 b 也不被额外要求互素。

[Overlap.lean](HeckeSkeleton/LowFrozenCube/Overlap.lean) 对完整原指标建立标记重叠零值。它允许标记槽重复，并从共同素位上的实际符号六次幂律推出零；没有将“重叠项为零”设为独立输入，也没有只检查平方自由列而遗漏其立方部分。

## 6. 局部预算、两种范数分母与精确能量等式

局部表首先给出复数层面的立方递推，再给范数层面的严格乘积公式。令 C_tab 为所有普通素位最低指数系数范数的乘积，则

\[
\|\text{localProduct}(a_{\min}x^3)\|
  =\frac{C_{\rm tab}}{\mathcal N(x)}.
\]

逐素范数乘积等于真实理想范数，由 PrimeProducts 证明。其余 phase 在原始输入上的模不超过一，因此组合后的 Ω 满足 C_tab/𝒩(x) 界；这不是入口的整体 majorant 假设。原项还带 1/𝒩(n′)，故完整立方系数有

\[
\|\beta_{\rm raw}(c',b)\|\le
\frac{C_{\rm tab}}{\mathcal N(x)\mathcal N(n')}
=\frac{C_{\rm tab}}{\mathcal N(b)}.
\]

原反射列系数还含 1/√𝒩(c′)。ColumnNormalization 明确保留这个分母，而不把它吞入无尺度说明的单位系数。若

\[
\mathcal N(c')\ge N_{\min}>0,\qquad
\mathcal N(b)\ge B_{\min}>0,
\]

则构造的单位系数满足 |a(P)|≤1、|β_unit(c′,b)|≤1，且实际原始行块能量满足

\[
\boxed{\quad
E_{\rm raw}
=\frac{(C_{\rm tab}/B_{\min})^2}{N_{\min}}\,
E_{\rm hybrid}(a,\beta_{\rm unit}).
\quad}
\]

标记分母 1/√𝒩(P) 始终留在 hybridRow 中。C_tab=0 或活动局部输入为空的情况由零能量分支处理，不需要非法除以零。

[LocalBudget.lean](HeckeSkeleton/LowFrozenCube/LocalBudget.lean) 只要求以下原始逐素平方界：

\[
|\mathrm{first}|^2\le q^{-1},\qquad
|\mathrm{prefactor}|^2\le q,\qquad
|\mathrm{atZero}(j)|^2\le
\begin{cases}q^{-1},&j=0\text{ 或 }4,\\1,&\text{其余 }j.\end{cases}
\]

它按最低指数构造实际 chargeIdeal：最低指数三的素位收费一次；最低指数零且 digit 为零或四的素位收费一次；其余不收费。由实际素乘积证明

\[
C_{\rm tab}^2\le \mathcal N(\mathrm{chargeIdeal})^{-1}.
\]

最低指数的 0、1、3 分类从原始非零表项推出。最上层 PrimitiveLocalBounds 只含上述三类 Gauss 标量条件；AnnularSupport 只含原始支撑、范数上下界和模界。它们都不含能量估计。

## 7. LOW-HYBRID 的实际应用与参数账本

将实际剩余行范数截断取为 K₀=Zᴴ，平方自由列截断取为 N₀=Zᵛ，完整立方截断取为 B₀=Z^ℓ，标记截断取为 L₀=Zᶻ。这里 H 控制的是分解后真实 d 的范数，不是原 k 的较粗范数。

环带下端点为 N_min=Zᵛ/2、B_min=Z^ℓ/2。若

\[
\mathcal N(\mathrm{chargeIdeal})\ge Z^{S+B},
\]

则外部平方系数不超过

\[
8Z^{-v-2\ell-S-B}.
\]

此处大写 B 是局部账本指数，B₀ 是完整立方的范数尺度，两者不同。四尺度小幂为

\[
(K_0N_0B_0L_0)^\eta=Z^{\eta(H+v+\ell+z)}.
\]

LOW-HYBRID 的主尺度满足

\[
(K_0+N_0B_0)B_0
\{N_0+L_0+(N_0L_0)^{2/3}\}
\le
6Z^{\max(H,v+\ell)+\ell+
       \max\{v,z,2(v+z)/3\}}.
\]

[Scale.lean](HeckeSkeleton/LowFrozenCube/Scale.lean) 证明真实实数幂不等式，系数六来自二项和三项的乘积。环带下端点的八与它相乘，使 SourceLedger 的常数是 48C₀。

设

\[
u=\min\{v,z,(v+z)/3\},\qquad
\kappa=-\tfrac12(T-v-3\ell)_+.
\]

共同核的平方标量记为 Z^κ。精确指数恒等式为

\[
\begin{aligned}
E_{\rm ref}
&=\frac O2-v-2\ell-S-B
 +\max(H,v+\ell)+\ell+(v+z-u)+\kappa\\
&=\boxed{\frac O2+\max(H,v+\ell)-S-B+z-u-\ell
 -\frac12(T-v-3\ell)_+}.
\end{aligned}
\]

uniform_source_energy_ledger 的结论直接包含实际源能量：

\[
Z^{O/2}E_{\rm raw}Z^\kappa
\le C_s Z^{E_{\rm ref}+\eta(H+v+\ell+z)}.
\]

O 在这一单块定理中是账本标量；真实强幂块数在下一步才证明并消费。共同核标量本身在有限代数层按给定数值乘入，原工程的 profile／核分析仍负责将真实反射核识别为该界。

## 8. 实际块计数与 O/2 只出现一次

[PowerfulCounting.lean](HeckeSkeleton/LowFrozenCube/PowerfulCounting.lean) 对实际强幂元素证明规范表示 a=u²v³，其中 v 平方自由。结合线性范数计数及已经证明的有限调和估计，首先得到 √K·H(K) 型界，再得到带 1+log K 的中间界和任意 K^(1/2+η) 界。这里没有声称已证明无对数的精确 O(√K)。

[FrozenCounts.lean](HeckeSkeleton/LowFrozenCube/FrozenCounts.lean) 同时计算受支撑平方自由部分的选择数。对原行的实际有限像

\[
\mathrm{Pairs}=\{(k_{\rm pow},k_{\rm sup}):k\in\mathrm{rows}\},
\]

若 𝒩(k_pow)≤Zᴼ、𝒩(rad(base))≤Z^Rrad，则

\[
\#\mathrm{Pairs}\le
C_r Z^{O/2}Z^{\eta_r(O+R_{\rm rad})}.
\]

该结论从同一正自然范数、线性计数和素乘积数据推出，不要求额外传入一个冻结块数估计。任意固定的局部切片成本 c^ω 另由 SupportPower 的实际素支持小幂界控制。

FrozenPartition 给原行有限和的精确纤维分解；UniformAggregateSource 通过已证明的支撑扩充等式，得到

\[
E_{\rm family}=\sum_{\mathrm{pair}\in\mathrm{Pairs}}E_{\rm pair}.
\]

每对的 Data 可以有自己的 ordinary、digit、minimum 和 source 系数；其 support 必须与 base∪supp(pair.pow) 对齐，并共享固定坐标与符号。FrozenFamilyAlignment 只表达这些数据等式，不包含任何能量不等式。

求和时使用同一个 C_s。单块界左侧原有的 Z^(O/2) 与块数界中的 Z^(O/2) 相消，因此全行结论为

\[
E_{\rm family}Z^\kappa\le
C_sC_r\,Z^{E_{\rm ref}
  +\eta(H+v+\ell+z)+\eta_r(O+R_{\rm rad})}.
\]

E_ref 中已有且仅有一次 O/2；这里没有再付一个强幂成本，也没有对不同原行块再用 Cauchy。

最后预先固定 W>0、ε>0，并要求

\[
(H+v+\ell+z)+(O+R_{\rm rad})\le W.
\]

取内部 η=η_r=ε/W 后，uniform_family_source_energy_subpower 给出统一的

\[
E_{\rm family}Z^\kappa\le C Z^{E_{\rm ref}+\varepsilon}.
\]

C 先于所有尺度和冻结族选择。长度预算 W 的依赖是显式的，不靠“参数有界”一句话隐去。

## 9. can-terminal-ledger 与真实幂节省

[Ledger.lean](HeckeSkeleton/LowFrozenCube/Ledger.lean) 使用以下原始标量信息：

\[
\begin{gathered}
F=N+V,\qquad N^*=N-3b_h,\qquad
V,b_h\le\delta,\quad z\le z_0,\quad H\le M-O,\\
c\le F-M-Q-z_0,\qquad c\le4F-3M-6z_0,\\
T-S-B\le2M-O+Q+V-N^*+2z,\qquad
v+3\ell\le T+\tau.
\end{gathered}
\]

另保留 O、S、B、ℓ、v、z、Q 的非负性。没有把 conductor 比较替换成一个最终能量假设，也没有删除保留块容差 τ。

代码按行主项、列主项且 u=z、列主项且 v≤2u 三个分支证明

\[
E_{\rm ref}\le
\max\left\{
F-c,\quad
F-2c+5\delta+\tau,\quad
F-\frac M4-\frac{3c}4+\frac{5\delta}2+\frac\tau2
\right\}.
\]

后两个列分支的覆盖由 cubicSaving_dichotomy 证明。UniformTerminalSource 和 UniformAggregateTerminal 将此实变量结论直接接到实际源能量界，而不只是另给一个孤立的指数引理。

若 M,c≥0、δ≤c/100、τ≤c/8，则上面的最大值不超过 F−c/2；再取 ε≤c/4，最终得到

\[
\boxed{
E_{\rm family}Z^{-\frac12(T-v-3\ell)_+}
\le C Z^{F-c/4}.
}
\]

完整入口的常数也不依赖之后选择的 c；它适用于所有满足该余量条件的节点。

## 10. 实际项目接线与审计边界

以下是将本证明应用到完整项目所需的字典，不是新模块内部尚未证明的正常形或系数估计：

1. 将 ExteriorIdeal 的实际乘法与交换幺半群结构、有限素赋值等价识别，并证明坐标平方自由／互素与底层理想谓词一致。
2. 将 exteriorNorm 识别为乘法实范数及正自然范数，并沿实际理想单射提供线性范数计数。最终全族入口已从线性计数内部推出正性，不额外要求一条外部范数正性估计。
3. 将 χ_J(I) 识别为 idealSymbol J (D.generator I)，证明允许生成元的六次 S-unit 误差在符号中消失，再提供两变量乘法、所需互反和共同素位零值。不能直接假设允许生成元严格乘法。
4. 将已经证明的二次、三次筛按上述范数、符号和平方自由字典传入。LOW-HYBRID 已完成两筛的组合以及除数、调和损失的吸收。
5. 把实际反射公式的 π、ρ、λ、自相位和原始 Gauss 项逐项识别为 rawSourceTerm 的定义，从真实 Gauss 表导出 PrimitiveLocalBounds，并把真实支撑识别为 AnnularSupport。
6. 调用原工程的共同 profile／核提供者，以及真实导子和不变量比较，解释 Z^κ 与终端标量条件。有限代数证明不会从一个义务结构自动制造其分析实例。

其中第 3、5 项是最需要逐项复核的接口：实际生成元误差和局部反射标量的方向、符号、归一化都必须与定义一致。本文的源项已经保留原系数的变化部分，因而这些识别是可逐项检查的等式，不是一个待证的“最终混合行化”大假设。

最终验证已使用精确指定版本构建两个公共入口及其全部新数学依赖。[LowAudit.lean](HeckeSkeleton/LowAudit.lean) 遍历两个新命名空间的定理，包括内部辅助定理，确认 955 个定理的全部公理依赖均属于 propext、Classical.choice、Quot.sound，没有 sorryAx 或新增算术公理。源码也不使用 native_decide。每模块日志保留源码哈希、版本、构建命令、源码编译期间未变标记和退出码。完整项目特化后仍需对其真实依赖链另做一次公理审计；自包含证明的通过不代替缺失项目库的验证。
