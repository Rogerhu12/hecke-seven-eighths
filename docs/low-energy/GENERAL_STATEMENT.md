# 一般 completed marked energy 的接口

本次推广对应 `weil_seven_eighths_revised.tex` 的
`lem:can-marked-energy`，并保留原物理能量定理的接口。
本文件描述正在原生编译核对的源码，不构成编译完成声明。

公开名称现在为 `HeckeSkeleton.completedMarkedEnergy K S D hreflection hquadratic hcubic`，
结论 `CompletedCanonicalMarkedEnergy K S D F theta` 有 `block_energy`、
`reconstruct`、`reconstruct_product`、`power_tails`、`annular_conductors` 五个字段。
原物理结论 `HeckeSkeleton.CompletedMarkedEnergy K c` 未改，证明改名为
`HeckeSkeleton.physicalCompletedMarkedEnergy`，`principalSource` 已同步使用此名称。

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

反射背景 theta 与有限 Mellin 数据 F 固定在统一常数之前。源码显示的是
这一确切量词和测试函数的有限 seminorm；尚未将任意依赖 theta 的常数
宣称为所有角型或高度变化下的统一多项式界。

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
及其真实 source index；其全 tuple/source-family energy 与估计中的行和
在取范数前相等。`SourceSupported` 只有原理想支持与互素条件。

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
编译输出保存在 GitHub Actions artifacts。源码清单只记录当前
文件与哈希；旧缓存收据、checkpoint 和已提交的构建日志已移除。
历史记录仍可从原 Git 提交和对应 Actions run 查阅。

AI-assisted development。
