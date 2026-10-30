# 原始 LOW-HYBRID 行到两条大筛的完整证明接口

本文说明新 `NormalForm*` 模块实际证明的行恒等式及其能量推论。完整 LOW-HYBRID 主链、独立引理 4.6 与跨全部冻结数据的统一入口现已通过 Lean 4.35.0-rc3 / Mathlib 0493595 的精确版本编译；`hybrid_energy`、`hybrid_energy_with_beta_mass`、`hybrid_energy_bounded` 的公理输出均只有 `propext`、`Classical.choice`、`Quot.sound`，详见对应构建日志。这里没有把最终行等式、块算子界或目标能量界作为算术结构的字段。

## 1. 原始行与两次除数展开

记

\[
Q_k(x)=\chi_k(x)^3,\qquad C_P(x)=\chi_P(x)^{-2},\qquad
M(x,y)=\mathbf 1_{(x,y)=1}.
\]

负二次幂按复数域的零延拓解释。原始行是 `Rows.lean` 的 `hybridRow` 中逐字定义的

\[
\sum_P\frac{a(P)}{\sqrt{N(P)}}M(P,k)
\sum_{n,b}\beta(n,b)Q_k(nb)C_P(n)M(P,b).
\]

`Arithmetic` 只要求范数乘法性及非负性、符号在两个变量中的乘法性、互素谓词的对称与乘法律、精确六次幂律，以及有限 Möbius 除数展开和可除时的商重建。它不包含任何能量估计。

第一次完整展开 `M(P,k)`，在每一个固定原行上写

\[
P=DQ,\qquad k=D\kappa.
\]

`markQuotients marks D` 是原标记集中所有可被 `D` 整除的标记，经商映射得到的有限集。商重建保证这个映射在相应支撑上单射；此处不需要另外假设最终有限和重索引式。

令

\[
\beta_D(n,b)=\beta(n,b)Q_D(nb)C_D(n)M(D,b).
\]

提取标记归一化后，原行中留下准确因子 `μ(D)/√N(D)`。完整 Möbius 展开后没有残余的 `M(Q,κ)` 掩码。

## 2. 完整立方的规范分解和第二次展开

规范完成平方分解为

\[
b=gt^2,\qquad n=cm,\qquad g=ch.
\]

`Completion` 的唯一输入是从原 `(n,b)` 到 `(t,c,m,h)` 的逐点重建。重建自动推出拆分映射单射，所以原双重有限和与拆分支撑上的和严格相等。`PrimeArithmetic.completion` 从素指数坐标实际构造这个拆分。

六次幂碰撞律给出

\[
Q_\kappa\bigl((cm)(cht^2)\bigr)
 =Q_\kappa(mh)M(\kappa,c)M(\kappa,t).
\]

完整展开第二个移动掩码 `M(κ,c)`，写

\[
\kappa=r\lambda,\qquad c=rc'.
\]

从此处起，代码中的 `c` 表示新的 `c'`。原始列和立方变量始终重建为

\[
n=rcm,\qquad b=rcht^2.
\]

两个除数的行局部有限集合是

\[
\operatorname{divisorPairs}(k)
=\{(D,r):D\mid k,\ r\mid k/D\}.
\]

`hybridRow_normal_form` 和 `hybridRow_eq_weightedBlocks` 证明原行恰为

\[
\sum_{(D,r)\in\operatorname{divisorPairs}(k)}
\mu(D)\mu(r)\frac{1}{\sqrt{N(D)}}\,
\operatorname{block}_{D,r}(k).
\]

这是逐行复数等式；其中所有支撑均由原始支撑和两次商映射定义。

## 3. 块内系数及严格零延拓

设 `κ=k/D`、`λ=κ/r`。块的三个关键系数是

\[
\begin{aligned}
a_{D,r,t,h}(Q)
 &=\frac{a(DQ)}{\sqrt{N(Q)}}C_Q(r)M(Q,ht),\\
\beta_{D,r,t,c,m,h}
 &=\mathbf 1_{(t,c,m,h)\in\mathcal S_r}
   \beta_D(rcm,rcht^2)Q_r(mh),\\
\operatorname{rowMask}(k,t)&=M(\kappa,t).
\end{aligned}
\]

`a` 的 Lean 函数签名只有 `(t,h,Q)`；它不能依赖移动行、`c` 或 `m`。`beta` 的签名只有 `(t,c,m,h)`；它不能依赖移动行或标记 `Q`。因此系数独立性由构造和类型保证，没有一个独立性假设需要用户证明。

二次核和三次核分别是

\[
q(k,m,h)=
\begin{cases}Q_\lambda(mh)&(m,h)\in\mathrm{goodPairs},\\0&\text{否则},\end{cases}
\]

\[
\chi(m,c,Q)=
\begin{cases}C_Q(cm)&(m,c)\in\mathrm{goodMC},\\0&\text{否则}.\end{cases}
\]

两种 good 集保留各自的平方自由产品和范数限制。乘积映射不同：二次是 `(m,h)↦mh`，三次是 `(m,c)↦cm`。零延拓由 `zeroExtendedQuadratic` 和 `zeroExtendedCubic` 的 `if` 定义实现。

## 4. 由原支撑推出权重预算

只要块 `beta` 非零，原立方支撑立即给出

\[
N(r)N(c)N(h)N(t)^2\le B.
\]

在 `|β|≤1` 时，六次根值符号与掩码都是模至多一的因子。因此

\[
N(t)N(c)|\beta_{D,r,t,c,m,h}|^2
\le\frac{B/N(r)}{N(t)N(h)}.
\]

`blockBeta_budget` 从实际非零支撑和原始系数模界推出这条预算。它没有先删除原立方支撑再应用预算。

## 5. 两条算子界由给定大筛推出

`weightedBlock_admissible_from_sieves` 在所有尺度、有限集合和系数之前选择二次、三次常数。二次方向先调用已证明的有限复矩阵转置，再经 `λ=k/(Dr)` 拉回原行。重建式

\[
(Dr)\lambda=k
\]

直接保证该行映射在固定块的原行支撑上单射。二次产品纤维与三次产品纤维分别付出它们自己的除数重数；两个核都在坏产品上严格为零。

`FiniteInputs` 的字段只包含有限支撑、平方自由性、范数截断、产品纤维计数、行局部除数计数与标量调和和。没有大筛算子界、块能量界或原行到块的等式字段。

## 6. 原始能量、列质量与统一小幂

`hybridEnergy_finite_bound` 将实际原行恒等式和实际块可容许性传给 `Global.lean` 中的 `hybrid_energy_of_weighted_blocks`，得到原始 `hybridEnergy` 的有限上界。

`ColumnMass.lean` 中的 `NormalForm.Arithmetic.columnMass_div_eq` 证明精确质量恒等式

\[
\frac{1}{N(D)}\sum_{Q:DQ\in\mathrm{marks}}
\frac{|a(DQ)|^2}{N(Q)}
=\sum_{P\in\mathrm{marks},\ D\mid P}\frac{|a(P)|^2}{N(P)}.
\]

交换两次有限和后，每个原标记仅按自己的除数个数收费。这个质量论证只使用商重建与范数乘法性，不需要取消律。

在自然截断 `D,r≤K` 下，所有剩余损失为

\[
\Delta(K)^2\Delta(NB)\Delta(N)\Delta(L)
(KNB)^\eta(NL)^\eta H(B)^3H(N)H(K).
\]

`NaturalLosses` 将五个除数因子、两个大筛小幂和五个调和因子同时吸收到 `(KNBL)^ε`；选择 `η=ε/12` 足够，全部常数都先于 `K,N,B,L` 选定。`hybrid_energy_of_finite_inputs` 因而给出

\[
E(a,\beta)\le C_\varepsilon(KNBL)^\varepsilon
(K+NB)B\{N+L+(NL)^{2/3}\}
\sum_P\frac{|a(P)|^2}{N(P)}
\]

对单位模界的 `β` 成立。

最后，`Homogeneity` 从字面原行证明对 `β` 的线性和能量二次齐次，并构造原有限支撑上的真实最大值

\[
\mathcal B(\beta)=\max_{n,b}|\beta(n,b)|^2,
\]

空支撑取零。`hybridEnergy_beta_mass_of_unit` 无需额外系数模界，就把右侧乘以这一个 `\mathcal B(β)`，得到任意复数 `β` 的质量版本。

## 7. 实际算术入口与无质量的任务公式

`HybridEnergy.lean` 中 `HeckeSkeleton.LowHybrid.hybrid_energy` 的入口不要求用户提供 `FiniteInputs`、除数界或调和界。它接受素指数坐标等价、自然数值的乘法范数、线性范数计数和两条大筛，并在内部构造规范完成平方、全部有限截断、两种产品好集合、除数包络与调和包络，再逐项兑现上述接口。

`Corollaries.lean` 中的 `hybrid_energy_with_beta_mass` 将这一完整算术入口与真实 `betaSquaredMass` 组合，给出任意 `a,β` 的质量公式。

当 `|a|,|β|≤1` 时，归一化标记质量满足

\[
\sum_{P}\frac{|a(P)|^2}{N(P)}\le H(L).
\]

同文件的 `hybrid_energy_bounded` 对质量版使用 `ε/2`，并由线性计数把 `H(L)` 界为常数乘 `L^{ε/2}≤(KNBL)^{ε/2}`。两个小幂合并为准确的 `ε`，得到

\[
E(a,\beta)\le C_\varepsilon(KNBL)^\varepsilon
(K+NB)B\{N+L+(NL)^{2/3}\},
\]

右端不再含系数质量。这个常数仍先于全部尺度、原始有限支撑和系数家族选定。


## 8. 只用二次筛的独立引理 4.6

`CompletedQuadratic.lean` 与 `CompletedQuadraticBound.lean` 还给出了独立的 `completed_quadratic_energy_bounded`。先按实际产品 `y=nb` 聚合：

\[
\gamma(y)=\sum_{nb=y}\beta(n,b).
\]

由于原列 `n` 平方自由，每个产品纤维通过第一投影单射进入 `y` 的平方自由除数集。因此单位系数时 `|gamma(y)|≤Delta(NB)`。再由素坐标唯一写成 `y=st²`，保留精确符号恒等式

\[
\chi_k(st^2)^3=\mathbf 1_{(k,t)=1}\chi_k(s)^3.
\]

`completed_quadratic_positive` 的任意系数正性版本在 `t` 上以 `N(t)` 为权做 Cauchy；固定 `t` 后才删除模至多一的行掩码，并将二次筛应用于平方自由 `s`。实际支撑给 `N(s)≤NB/N(t)²`，线性计数与剩余权重相抵后，得到

\[
E_{\rm quad}\le C_q C_{\rm count}
\Delta(NB)^2H(NB)^2(KNB)^\eta(K+NB)NB.
\]

五个小幂因子取 `eta=eps/5`，证明

\[
\sum_k\left|\sum_{n,b}\beta(n,b)\chi_k(nb)^3\right|^2
\le C_\varepsilon(KNB)^\varepsilon(K+NB)NB.
\]

此入口不要求三次筛、不要求全符号互反，也不在原始 `b` 上逐项做 Cauchy。常数仍先于尺度、支撑与系数选择。任意系数正性公式保留实际产品聚合和平方提取支撑；它不是论文 dyadic `(T,G,C,r)` 式的逐字封装。

## 9. 冻结字段变化时的常数一致性

实际加权冻结出口已经把原行等式和单位系数界接入 `hybrid_energy_bounded`。`UniformWeightedHybridBound.lean` 进一步把这一次混合常数选择放到所有冻结 `Data` 之前：固定 `coords`、`symbol`、自然范数和计数及两筛后，取得一个 `C`，再对所有使用这套坐标与符号的 `support`、`ordinary`、`digit`、`minimum` 应用同一界。

`UniformSourceLedger` 和 `UniformTerminalSource` 将该同一常数传到系数账本、实际源能量以及终端裕度结论。两个数据等式 `D.coords=coords`、`D.symbol=symbol` 只表达共用算术字典；没有加入待证能量或统一块界。原有固定 `D` 入口保留为便利接口，完整统一性由这些更强的公开入口明确陈述。

独立二次结论、统一加权冻结入口、统一源能量和终端／聚合模块均已通过 Lean 4.35.0-rc3 / Mathlib 0493595 的精确版本编译。最终环境的全量公理审计也已通过，允许依赖仅为 `propext`、`Classical.choice`、`Quot.sound`；具体源码哈希、完整类型与构建记录以交付包的核验证据为准。
