# LOW-HYBRID 第二轮只读数学边界审查

审查对象：`HybridEnergy.lean`、`CanonicalInputs.lean`、`Corollaries.lean`，并沿其证明读取 `NormalFormUniform`、`NormalFormBound`、`BlockAdmissible`、`CanonicalSupport`、`ColumnMass`、`Homogeneity`、`Transpose`、`NormalForm` 和计数／损失模块。

本审查针对源代码中的数学依赖和量词；最终构建、源码哈希及公理证书应以根代理的串行重建结果为准。

## 1. 审查结论

当前通用素坐标实例的 LOW-HYBRID 主链中，没有发现把目标混合能量、块能量、最终正规形等式、产品纤维上界或任意小幂除数界作为公开最终定理前提的情形。`hybrid_energy` 的公开前提是素坐标乘法等价、自然值乘法范数、线性范数计数、六次符号的基本乘法／零值规律以及两个原始大筛结论。所有 `FiniteInputs` 字段均在 `canonical_finite_inputs` 中从原始有限支撑构造。

主增长项恰为

\[
(K+NB)B\bigl(N+L+(NL)^{2/3}\bigr).
\]

没有产生额外的固定正幂 `N`、`B` 或 `L`。剩余除数、调和与筛中小幂因子统一吸收为 `(KNBL)^eps`。

实际 `ExteriorIdeal K S` 和允许生成元符号的实例字典仍是明确的项目接线边界。它不能在报告中写成“已经编译的实际数域实例”。这不是新的混合能量假设；字典内容见第 6 节。

## 2. 常数量词与系数质量

`hybrid_energy`、`hybrid_energy_with_beta_mass`、`hybrid_energy_bounded` 的次序均为：固定算术数据和 `eps > 0`，先取得 `C0 > 0`，再量化四个尺度、全部有限支撑以及两类原始系数。`NormalFormUniform.hybrid_energy_of_finite_inputs` 先取 `eta = eps/12` 和算术损失常数，然后取得两个大筛常数；没有在固定尺度后重新选常数。

实际范数 cutoff 是先定义的函数 `X ↦ normCutoff X`，实际除数包络也是先定义的函数 `Delta(X)`。由 `SubpowerBound` 得到的常数先于 `X`。因此这里没有利用“对每个尺度另选一个有限集合常数”混淆统一性。

`hybrid_energy` 保留原始标记质量

\[
\mathcal A=\sum_{P\in\mathrm{marks}}|a(P)|^2/N(P).
\]

任意复系数版本使用 `betaSquaredMass`，即原始有限 `columns × cubes` 上 `|beta|²` 的最大值；空支撑时定义为零。该质量在线性能量上界中只出现一次。`Homogeneity` 中的单位系数能量前提是一个可复用的齐次性引理接口；在公开推论中它由已经构造的 `hybrid_energy` 填入，不是新的最终假设。

双单位系数版本先以 `eps/2` 调用主界，再用同一个线性计数证明标记倒数范数和不超过 `C_H L^(eps/2)`，由 `L ≤ KNBL` 合并为目标 `eps`。因此消去标记质量没有额外 `L` 因子。

## 3. 从原始支撑得到的全部结构条件

| 所需条件 | 实际来源 |
|---|---|
| 完成平方及原始有限和重索引 | `PrimeArithmetic.completion` 使用规范素指数分解；重组恢复原始 `(n,b)` |
| 两个完整 Möbius 展开 | `PrimeArithmetic.mobius_expansion` 由素支撑幂集证明；`NormalForm.hybridRow_normal_form` 执行展开与商重索引 |
| `D,r` 的完整范围 | 两者均整除原始行，故均落在 `cutoff K`；未删去可能贡献的除数 |
| 双商行平方自由、范数不超过 `K` | 双商整除原始平方自由行；乘法范数各因子至少为一 |
| 商标记平方自由、范数不超过 `L` | 商标记整除原始平方自由标记 |
| 完成变量 `t,c,m,h` 的有限盒 | 原始 `n=rcm`、`b=rcht²` 的支撑恢复及乘法范数 |
| 二次产品 `mh` 平方自由、范数不超过 `NB` | 规范指数分解的剩余平方自由性，以及 `Nm≤N`、`Nh≤B` |
| 三次产品 `cm` 平方自由、范数不超过 `N` | `cm` 整除原始平方自由列 `n` |
| 两种产品纤维界 | 首因子映入实际平方自由除数集合；素坐标消去给出纤维内单射 |
| 变换后的 beta 单位界 | 原 beta 单位界乘以六次符号／掩码的模不超过一因子；支撑外定义为零 |
| 加权立方预算 | beta 非零时恢复原始立方指标，并使用 `Nr Nc Nh Nt²≤B` |
| 列质量 | `D` 的平方根权重与商标记平方根权重正好还原 `1/N(P)` |
| 调和边界 | 每个完成变量集合都是实际范数 cutoff；由线性范数计数的有限 Abel 求和统一控制 |

`canonical_finite_inputs` 使用较大的 `t≤B` 盒而非 `t≤sqrt B`，但它只引入 `H(B)`，没有按盒基数进行粗计数。因此这一放宽只影响已经计入的调和小幂因子。

`blockA(d,r,t,h,p)` 不含移动三次行变量 `c,m`，`blockBeta(d,r,t,c,m,h)` 不含移动行或移动标记。两个大筛所需的系数独立性由实际函数签名体现。固定 `d,r,t,h` 后的运用次序符合纸面论证。

## 4. 算术损失账本

自然完整公共除数 cutoff 使用 `r≤K`，所得损失为

\[
\Delta(K)^2\Delta(NB)\Delta(N)\Delta(L)
(KNB)^\eta(NL)^\eta H(B)^3H(N)H(K).
\]

其中除数项共五个、两个大筛小幂共两个、调和项共五个，总计 `12 eta`。把每个参数放大到 `M=KNBL≥1` 后，`NaturalLosses` 得到

\[
\mathrm{loss}\le C_D^5 C_H^5 M^{12\eta}.
\]

取 `eta=eps/12`。`r≤K` 相比更精细的 `r≤N` 不改变主增长项，也不需要额外行计数。二次筛的转置由 `Transpose.finite_operator_bound_transpose` 的复 Hilbert 空间有限对偶证明，保留同一算子常数；没有额外互反或多项式成本。

实际 `Delta` 是所有范数不超过 `X` 的元素的平方自由除数个数最大值。其小幂不是输入：线性计数先推出有界范数集合有限；真实素坐标给出除数个数 `2^|support|` 和素范数乘积不超过总范数；有限小素集合支付不能由 `N(p)^eta` 支付的有限因子。

当前 `HybridEnergy`／`Corollaries` 表述仍显式带 `hqpos` 和 `hCcount`。它们是冗余结构前提，可以分别由 `CountingPositivity.linear_norm_counting_norm_one_le` 与 `linear_norm_counting_constant_pos_of_element ... 1` 消去。消去后无需新增数学输入。

独立的引理 4.6 现在还有已通过目标版本编译的 `completed_quadratic_energy_bounded`：它只接收二次筛、符号第二参数乘法与六次幂掩码，以及相同素坐标／范数计数结构；没有三次筛或互反假设。原始 `(n,b)` 先按实际乘积 `y=nb` 分组，其纤维由平方自由列因子映入 `y` 的真实平方自由除数集合。再用 `y=s*t²` 的规范重构和带范数权的 Cauchy，把无限制立方指标保留在联合乘积里。最终上界是 `C (KNB)^eps (K+NB) NB`。该证明的中间损失是一个筛小幂、两个除数小幂和两个调和小幂，取 `eta=eps/5`；没有逐个 `b` 另做一次无权 Cauchy，也没有借更强的混合结论替代只二次筛命题。

## 5. 冻结行求和的新增真实计数出口

下列真实计数与分块接口已通过目标版本编译；完整交付的构建状态与源码哈希以根代理最终审计为准。

- `LowFrozenCube.powerful_count_le_sqrt_harmonic`：实际有限强力理想集合的基数不超过 `Ccount * sqrt K * H(K)`。
- `powerful_count_small_power`：统一 `C K^(1/2+eps)`，常数先于尺度和集合。其证明使用规范 `u²v³` 重构和 `Nu Nv≤sqrt K`，未假设强力理想计数结论。
- `supported_squarefree_count_le` 与 `supported_squarefree_count_small_power`：实际受限平方自由集合先受 `2^|support|` 控制，再由相应支撑根基的范数小幂控制。
- `frozen_row_pair_count_small_power`：直接对原始行的 `(powerfulRowFactor,supportedRowFactor)` 有限像给出 `C sqrt K (K N(radSupport))^eps`。`K` 只约束强力部分，故纸面的 `O/2` 只计一次。
- `sum_rows_eq_frozen_blocks`：原始行的和按上述实际有限像精确分块；正项求和没有额外 Cauchy 成本。
- `prime_support_power_subpower_of_counting`：任意固定非负局部切片基数 `c` 的 `c^omega(a)` 也从同一计数前提推出小幂。

用 `sqrt K * log K` 代替纸面精确 `O(sqrt K)` 是明确的实现选择。损失被任意小幂吸收，符合终端本就带 `eps` 的目标；不能把这个中间定理描述为已证明无对数的精确强力理想计数。

实际冻结块计数乘出的 `Z^(O/2)` 与单块账本左侧同一因子正好取消，因此汇总后的 `Eref` 没有重复支付强力部分。

### 5.1 变化冻结数据的统一常数与实际原始行

早期固定 `D` 的入口保留用于兼容。此前审查指出的“先固定 `D` 才选择常数”限制，已由新统一链真实消除：`uniform_weighted_raw_hybrid_bound`、`uniform_source_energy_ledger`、`uniform_aggregate_source_energy_ledger` 和 `uniform_family_source_energy_ledger` 均先固定全局 `coords`、`symbol`、范数与计数／筛输入及小幂参数，随后选择一个 `C>0`，最后才量化所有冻结数据。新的统一源账本与全族聚合已通过目标版本编译，公理只有标准三条。

具体而言，`D.support`、`D.ordinary`、`D.digit`、`D.minimum` 可以在各实际冻结对之间变化。普通集合与其局部数据仍须满足其结构定义和所写原始支撑／Gauss 界；这些不是能量估计。`uniform_aggregate_source_energy_ledger` 对实际冻结对索引的块能量之和直接成立，不要求各块有同一个排除支撑。

原始行版本使用 `FrozenFamilyAlignment`，逐块要求数据坐标等于公共坐标，且

\[
\operatorname{support}(D_{\mathrm{pair}})
 =\mathrm{base}\cup\operatorname{supp}(\mathrm{pair.pow}).
\]

`base` 可预先包含固定 label、puncture 和 inactive 排除集合。对强力部分已固定的块，强力素位的原始行赋值不等于一，所以加入这些素位既不改变 valuation-one supported factor，也不改变 residual factor。`FrozenSupportExtension` 已证明两个因子及实际 `rowBlock` 的相等，不能把这个等同作为一个隐藏接口假设。

`varyingFamilySourceEnergy` 的定义是按原始 `rows` 求和：每个原始行先提取它自己的实际冻结对，再调用该对的原始 `rawSourceRow`。`varyingFamilySourceEnergy_eq_blocks` 证明这个逐行定义等于对应块能量的正项和。它不是将块能量之和直接命名为原始行能量。`FrozenFamilyAlignment` 只包含坐标、排除支撑、原始行集合和两种因子的等式，没有能量界或正规形等式字段。

### 5.2 最终任意小幂与 terminal 预算

`UniformAggregateTerminal` 的三个公开入口都在 `LowFrozenCube.FrozenReduction` 中，已通过目标版本编译且各自只有标准三条公理：

| 定理 | 实际全原始行能量乘共同 kernel 平方因子的上界 |
|---|---|
| `uniform_family_source_energy_subpower` | `C Z^(reflectedExponent + eps)` |
| `uniform_family_source_energy_terminal` | `C Z^(terminalBound + eps)` |
| `uniform_family_source_energy_power_saving` | `C Z^(F-c/4)` |

这些入口固定 `W>0` 与任意 `eps>0` 后，先选择常数，再量化全部尺度、原始行、support 和变化的冻结数据。其明确的长度范围条件为

\[
(H+v+\ell+z)+(O+R_{\rm rad})\le W,
\qquad N(\operatorname{rad} \mathrm{base})\le Z^{R_{\rm rad}}.
\]

内部在所有尺度之前选择 `eta=eps/W`，同时用于混合筛损失和实际冻结对计数。因此全部这两类损失为

\[
\eta(H+v+\ell+z)+\eta(O+R_{\rm rad})\le\varepsilon.
\]

这不是让小幂参数事后依赖当前尺度。固定 `W` 的前提需要保留在使用说明中；不能宣称该具体推论对不受任何范围约束的 logarithmic lengths 仍给出同一个固定总 `eps`。

terminal 入口调用已经证明的三个实数分支。最终 saving 入口再使用 `M,c≥0`、`delta≤c/100`、`tau≤c/8` 以及 `eps≤c/4`，由 `terminalBound≤F-c/2` 得到 `F-c/4`。`F=N+V`、`Nstar=N-3bh`、两条 margin、导子比较和 retained-range 条件均为明确的标量前提，没有被重命名为能量前提。新的三个入口还在内部从线性计数推出自然范数至少为一和计数常数为正。

此处“全原始行族”准确指所给实际冻结对上的原始行正项求和，并允许每个冻结对选择不同的局部数据。它不应被扩张描述为已经证明 theta 反射、共同 Fourier profile、无限尾部，或任意未提供的外层 minimum／class／inactive Minkowski 合并。固定局部选择数的 `c^omega` 和有限倒数范数和已有真实小幂定理；具体外层系数分解与实际 theta 对象的识别仍属于下节第 6 项所述接线。

## 6. 真正需要实际项目字典提供的内容

1. **外部理想的乘法及素坐标。** 把实际非零、避开 `S` 的理想类型组织为交换幺半群，构造 `A ≃* Multiplicative (ExteriorPrime →₀ ℕ)`，并证明坐标平方自由／互素分别等价于实际理想的 `Squarefree`／`IsCoprime`。
2. **范数。** 构造实际 `exteriorNorm` 的乘法同态和自然值证书。包中 `GlobalThetaData.exteriorNorm` 明确等于底层 `Ideal.absNorm` 的实数强制转换；实际乘法与 `absNorm` 的兼容仍须接线。
3. **线性计数。** 用外部理想到所有非零理想的单射，将项目的理想计数上界转为 `LinearNormCounting`。自然 cutoff `N=0` 的情况要由非零理想范数正性处理，不能只接 `X≥1` 部分而忽略零 cutoff。包内 `HeckePort.CenteredMomentCounting.card_le_idealCountConstant` 和 `CubicSieve.ExteriorSieve.cutoff_card_le_ideal_count` 展示了相关有限集合转移；其上游导入 `DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound` 不在当前可独立编译的自包含层中。
4. **允许生成元符号。** 令 `symbol J I := idealSymbol ... J (D.generator I)`，证明两个参数的严格乘法性及 `symbol^6` 的互素指示值。这里要使用允许生成元的第六次幂单位修正，不能把生成元本身误称为严格乘法。包内 `HeckePort.CenteredMomentGenerator.generatorCharacter_mul` 通过 `AllowedGeneratorInput.multiplicative` 和第六次幂平凡性展示了正确处理方式。
5. **两个大筛。** 将提供的 `QuadraticSieveBound` 和 `CubicSieveBound` 重新定向、重命名为当前同一个实际 `symbol` 的输入；二次方向交换已在通用层证明，无需另加互反估计。平方自由谓词的等价与第 1 项保持一致。
6. **冻结局部数据的识别。** 将具体局部旋转表、Gauss 因子、剩余相位和有限类切片识别为冻结模块的显式数据；其独立性、重叠零值、范数预算和导子指数比较应由对应新模块调用，不能把最终行能量当作字典字段。

上述事项均是公开、具体的实例化义务。此前缺少的“完整正规形、支撑恢复、除数小幂、调和小幂、乘积纤维、系数质量或最终 epsilon 量词”已经不属于待提供的字典内容。
