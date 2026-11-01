# 一般 completed marked energy 的接口

本次推广对应 `weil_seven_eighths_revised.tex` 的
`lem:can-marked-energy`，并保留原物理能量定理的接口。
本文件说明公开源码接口；实际验收以 PR #3 当前 head 的完整原生构建
与四项公理报告为准。

公开名称现在为 `HeckeSkeleton.completedMarkedEnergy K S D hreflection hquadratic hcubic`，
结论 `CompletedCanonicalMarkedEnergy K S D F theta` 包含以下具体结论。
原物理结论 `HeckeSkeleton.CompletedMarkedEnergy K c` 未改，证明改名为
`HeckeSkeleton.physicalCompletedMarkedEnergy`，`principalSource` 已同步使用此名称。

| 字段 | 结论 |
| --- | --- |
| `product_block_energy` | 原 tuple/prime-choice 有限投影的统一行能量；具体 block family 和 source support 自动构造。 |
| `block_energy`、`uniform_block_energy` | 一般 source family 的能量，以及常数先于有限阶子背景和实范数扭曲的版本。 |
| `reconstruct`、`reconstruct_product` | 原 canonical completed sum 与完整反射级数相等，包含 product-form mark 的碰撞零项。 |
| `reconstruct_product_block` | 具体 product factory 的投影就是原 reflection sigma index 的有限投影及实际活动理想环带。 |
| `reconstruct_original_product` | 同一具体 source family 等于原行、标签和穿孔下非碰撞 tuples 的完整有限原索引投影；碰撞零项由实际掩码证明。 |
| `project_columns`、`discarded_columns` | 全列和等于有限保留块加真实补集；补集由其实际 sourceTailPiece 控制。 |
| `power_tails`、`uniform_power_tails` | 任意幂尾界及显式多项式高度版本。 |
| `uniform_discarded_tails` | 同一任意幂界直接作用于所保留完整环带的真实补集。 |
| `annular_conductors` | 原行、原 powerful part 和实际 residual annulus 的两个导子比较。 |

## 原陈述与一般陈述

原物理陈述固定 `TargetContext`、由其得到的 theta period、Gaussian
剖面、空 puncture 和原始 `5/6` 行截断，结论为
`C * Z^(5/6 + eps) / q^2`。常数先于 `Z`、窗口中的素理想 tuple 和
所选槽集合确定。全部活动标记的和保持在每一行的范数内部。

一般陈述使用任意未分歧 Hecke period、任意固定环带测试函数、任意
正 completed scale `X`、任意平方自由 puncture 和 label、真实 row
的 powerful/supported/residual 分解，以及原二次、三次筛。
数据结构只记录实际理想、系数、范数尺度及有限支持；它们不以能量
结论或等价分析估计作为字段。

任意完成尺度下，核参数为

\[
\frac{X\,N(a_{\min})\,N(c)\,N(b)^3}
     {N(d)^2 N(f_0)^2 N(P)^2}.
\]

一般块的活动标记分母保留 `N(P)^2`。物理完成尺度为
`X = Z * N(inactive) * N(P)`，在该逐项等式中恰好约去一个
`N(P)`；`GeneralReconstruction.generalAtom_eq_physicalAtom` 明确
证明这个专门化等式。

单独的固定 X 定理不能直接用于 X 随 P 变化的和。为此共同核估计
`GeneralSeparatedEnergy.general_separated_energy` 统一处理
`X(P)=X0` 与 `X(P)=X0*N(P)`，并在选择这两种尺度律之前选择常数。
一般块和原物理块都直接从这一共同定理实例化；物理端之后沿用原有的
全 Gaussian 环带求和和选定理想分母恢复。

## 真实系数与量词

论文中的 canonical 系数满足
`a0 = conjugate(Lambda) * gamma₂`。`MOM_BASE` 已实现此定义及其
calibration，且 `canonicalPeriod = Lambda⁻¹ * nu` 保留任意允许的
背景。推广使用这些真实定义，不把 `a0` 当成与 theta reflection
无关的任意函数。各活动槽的原系数通过任意有界 `markWeight`
保留在原行内；非活动槽使用原 reciprocal-prime 权重的 L1 质量。

统一能量常数先于 frozen datum、label、puncture、完成尺度、环带
剖面、四个理想支持和标记系数选定。剖面的有限 seminorm 及标记
系数的显式范数界单独显示。可变尺度处于给定有限长度范围时，筛的
小幂损失先统一分配到最终 `eps`。

`block_energy` 的界为
`C*A^2*(B^rmax)^2*testSeminorm(V, order(K,0), 2)^2*Z^(O/2+E+eps)`。
这里 A 是真实活动理想系数界，B 是原非活动槽系数界；活动 tuple 聚合
用实际 ideal fibre 求和，`GeneralInactiveMass` 给出仅依赖固定槽数的
fibre 常数。允许窗口重叠和 tuple 内素理想重复；重复素理想只能整体
进入 active 或 inactive，一次 reciprocal norm 只按 distinct support 计。
活动理想环带按实际 N(P) 分段，不假设重复 tuple 的范数等于各槽范数积。

基础背景 theta 与有限 Mellin 数据 F 固定在统一常数之前。
`uniform_block_energy` 进一步在选取常数之后允许任意有限阶字符 nu 和
任意实参数 t，应用于 `nu * theta * heckeNormTwist K t`，显式乘上
`(1 + |t|)^(18 * ncx K)`。子背景原有的 reflection/unramified 输入仍显式
给出，但该能量常数不能依赖子背景或 t。此结论固定基础角型；没有声称
任意无界角型都由同一常数控制。

若 consumer 为事先固定的有限背景清单逐个构造不同的 Mellin 数据
`F(theta)`，可对每个背景应用 fixed-F 结论，再取有限个常数的最大值。
同一个 F 下的有限阶字符和范数扭曲则直接使用上述统一字段。
这两种量词顺序均保留真实 finite Mellin table 与相应背景的校准关系。

任意幂尾项的统一版本同样先选取核移线阶数 J、常数 C 和阈值 Z0，再选
nu、t 和有限尾项族。大参数阶数为
`A = 1 + 2*(B_tail + L)/tau`，高度因子为
`(1 + |t|)^(8 * ncx K * A)`。`B_tail` 由真实有限项数、外部系数和理想
范数长度上界计算；没有把多项式核界作为新的假设。

## 与原 completed sum 的等式

`GeneralReconstruction` 从原 `MarkedCoefficientReflectionInput`
的绝对收敛反射出发，保持每一个 frozen state、每一个活动子集和
两个完整 dual columns。两个 zero extension 保留原来的
row/mark、column 和 mark/cube 互素条件。随后有限局部类分解把
这些真实反射项识别为 `GeneralReflectedBlock.slicedBlock`。

`canonicalCompletedSum_eq_general_atoms` 把 `MOM_BASE` 中的原
canonical completed sum 接到同一反射级数，采用原 whole-index
mark；不存在替换系数后再假定能量的步骤。

`GeneralProductReconstruction` 对论文 product-form mark 证明有限线性展开，
以原 canonicalTau（包含 label 的四次幂）处理全部 row、label、puncture
碰撞零项。`GeneralCanonicalBlock.sourceTerm` 直接使用原 `reflectedTerm`
及其真实 source index；source-family energy 与估计中的行和在取范数前
相等。`SourceSupported` 只有原理想支持与互素条件。

`GeneralTupleBlocks` 负责从原 tuple 和 prime MarkChoice 到饱和槽模式、
非活动 tuple 与真实活动理想 fibre 的有限重排。活动与非活动 distinct
support 必须不交，所以重复素理想不能被拆到两侧。这一步把原 product
mark 的反射展开接到能量定理使用的具体 source family。
`GeneralProductEnergy` 因而直接估计原有限投影的平方行范数，consumer
无需补一个 source identity、系数独立性或 source support 假设。

`GeneralColumnCutoff` 保留完整的实际 dyadic rectangles，并在取范数前
证明全列和等于有限保留和加真实补集。补集中的核参数由同一个实际
row/mark 比值盒推出下界，因而由 `GeneralKernelTail` 的任意幂尾项控制。
`GeneralSourceCutoff` 把这些列项重新乘上真实 inactive/row/mark 系数并
汇总有限局部类，得到未切类的原 `generalAtom` 与其实际补集。
新接线与高度传播均须由完整原生构建核验；此处是源码接口说明。

## 一般指数

`GeneralBlockPolynomial` 使用真实尺度的 `log_Z` 长度，证明

\[
T_d=2H+2A_0+2z_a-N_*-N_0-3B_0,
\qquad u_0=\min\{v,z_a,(v+z_a)/3\},
\]

\[
E_{\mathrm{ref}}=\frac O2+\max(H,v+\ell_b)-S_0-B_0+z_a-u_0-\ell_b
-\frac12\max(T_d-v-3\ell_b,0).
\]

`GeneralMarkedEnergy` 将实际两筛块界接到这个指数。
`GeneralAggregation` 汇总真实 frozen states、全部局部类和
powerful rows；`O/2` 只由 powerful ideal 的真实计数引入一次。
`GeneralRows` 与 `GeneralConductor` 负责真实行分解和导子比较。
`GeneralKernelTail` 从原 Mellin kernel 的任意阶大参数估计得到
完整双列的可求和主函数和任意幂尾界。

## 原生验证

最终验证由 `.github/workflows/low-energy-verify.yml` 执行。
它恢复官方固定 release 中的依赖产物，重新构建本任务的全部新
证明模块，并在新的 Lean 进程中打印所需最终声明的公理。
普通构建失败后，另一个原生诊断命令会将相关真实源文件临时接成一个
编译单元，借助原文件哈希和逐行映射收集被失败依赖挡住的下游错误。
该命令的输出只用于定位；验收仍要求每个独立模块及四项公理审计通过。
编译输出保存在 GitHub Actions artifacts。源码清单只记录当前
文件与哈希；旧缓存收据、checkpoint 和已提交的构建日志已移除。
历史记录仍可从原 Git 提交和对应 Actions run 查阅。

AI-assisted development。
