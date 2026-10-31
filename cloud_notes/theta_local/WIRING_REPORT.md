# Theta 局部结果接入项目定义

任务：`cloud_tasks/WIRE_THETA_LOCAL.md`。基准提交：
`5e4c85f172c101fd0c201219c13aa28f8b520d42`，目标分支 `dtests-handoff`。

本次仅新增适配、证明与审计文件，保留所有已有定义和证明。入口为
`HeckeSkeleton.ThetaLocal.Project`，公理审计入口为
`HeckeSkeleton.ThetaLocal.ProjectAudit`。

## 有限位的四项识别均由现有算术数据推出

设 `K` 是数域，`S` 有限，`D : ThetaArithmeticData K S`，
`p : ExteriorPrime K S`。令

$$
k=\mathcal O_K/\mathfrak p,\qquad q=N\mathfrak p,
\qquad \chi=\texttt{thetaPrimeCharacter}(p).
$$

这里使用 `D` 的原有假设：指定的本原十二次根、六次根及复嵌入；
`S` 外各素位避开六且局部 different 指数为零；每个 exterior ideal
配有一个非零的 `S`-整数生成元，其主理想等于该理想在 `S`-整数环中的延拓。
这些是现有结构的输入，并非对任意 `K,S` 自动构造出的数据。

`ProjectResidue.lean` 证明以下识别；没有把这些识别增列为假设。

| 识别 | 新定理 | 证明所用的实际对象 |
| --- | --- | --- |
| 有限域基数等于绝对范数 | `residue_card_eq_absNorm` | `card_primeIdealResidueField` |
| 乘性特征阶恰为六 | `thetaPrimeCharacter_orderOf` | 给定 `D.root6`、嵌入及原有 `sexticResidueCharacter_order` |
| 主相位及其本原性 | `projectPrimePhase_apply`、`projectPrimePhase_isPrimitive` | 沿 `sIntegerResidueEquiv` 拉回实际主加性特征 |
| 二次幂的 Gauss 归一化 | `thetaGamma_two_eq_gammaTwo` | 素理想唯一素因子的重数为一，再沿剩余域等价重排有限和 |

具体而言，`projectPrimePhase_mk` 证明对整元素代表元 `a`，
相位正是项目已有的

$$
\psi(\bar a)=\operatorname{sLocalPrincipalPhase}
  \bigl(a/D.\operatorname{generator}(\mathfrak p)\bigr).
$$

因此生成元选择及其相位单位修正被原样保留。并且

$$
\texttt{thetaGamma}(\mathfrak p,2)
=q^{-1/2}\sum_{x\in k}\chi(x)^2\psi(x)
=\texttt{ResidueField.gammaTwo}(\chi,\psi).
$$

## 项目现有有限和得到完整数字表

`ProjectFinite.lean` 逐一证明项目的 `localTau`、`digitMask`、
`sphericalDigit`、`localWeylScalar`、`localWeylExponent`
与上一轮有限域核心的对应对象相等，然后将核心结论用于这些项目定义。

记

$$
\tau_j=G(\chi^{-j},\psi),\qquad
\gamma_2=q^{-1/2}G(\chi^2,\psi),\qquad
W_e=\texttt{sphericalDigit}(p,e).
$$

对所有 `j : Fin 6`、`e : ℕ`，得到

$$
\texttt{localWeylScalar}(p,j,e)=
\begin{cases}
-q^{-1/2}\gamma_2,&e=0,\ j=0,\\
G(\chi^{(j+2)\bmod6},\psi)/\tau_j,&e=0,\ j\ne0,\\
(q-1)W_e/\tau_j,&e>0,\ j=4,\\
0,&e>0,\ j\ne4.
\end{cases}
$$

其中 `e % 3 = 2` 时标量为零。对任意单位参数 `t`，实际有限和的
单位依赖由 `localWeyl_phase_separation` 证明为
`χ(t) ^ localWeylExponent j e`。指数就是项目原有的

$$
\begin{cases}(8-j)\bmod6,&e=0,\$4+2e)\bmod6,&e>0.\end{cases}
$$

均匀 active mark 的表由 `marked_localWeyl_table` 给出：

$$
\begin{cases}q^{-1/2}\gamma_2\chi(t)^2,&e=0,\\0,&e>0.\end{cases}
$$

`digitMask_fourier` 保留零阶数字的单位指示函数约定：

$$
\sum_{x\in k}\texttt{digitMask}(p,j,x)\psi(tx)=(\chi^j)(t).
$$

右侧 `j=0` 的 `MulChar.one` 在零点取零，不是常值一。
同时证明非零数字 `j ≠ 0` 的 `localTau` 非零且模长为 `√q`、
`thetaGamma(p,2)` 的模长为一、
row prime 标量的模长为一，以及 frozen 标量的两条统一界：

$$
|s_{j,3k+1}|\le q^{-k},\qquad
|s_{j,3(k+1)}|\le\sqrt q\,q^{-(k+1)}.
$$

`ProjectDigitTable.lean` 进一步以这些真实算术对象定义

$$
W(p,e,u)=
\begin{cases}
0,&e<0,\\
\chi(u)^{2e}\,\texttt{sphericalDigit}(p,e),&e\ge0,
\end{cases}
$$

并通过 `projectSphericalDigitTable_input` 构造现有
`LocalThetaInput K S D W` 的全部字段。

## 复位使用实际 Hecke 参数并保留明确常数

在一个复位，令

$$
m=\texttt{heckeComplexWeight}(\theta),\quad
\tau=\texttt{heckeComplexParameter}(\theta),\quad
\rho=\texttt{archRadial}(\theta)=-\tau,\quad
a=(|m|+1)/2.
$$

`ProjectArchimedeanWhittaker.lean` 将实际向量 `archRootVector`、
Weyl 作用及 Whittaker 值专化到这些参数；
`ProjectArchimedean.lean` 将其接到真实 Bessel 轮廓

$$
D_\theta(t)=t^{a+i\rho}K_{1/3}(c\sqrt t),\qquad
H_\theta(t)=t^{a-i\rho}K_{1/3}(c\sqrt t),\quad c>0,\ t>0.
$$

Whittaker 识别还明确假设 `β : ℂˣ`、
`hβ : (β : ℂ) = (c : ℂ)`，即模型参数与正实尺度一致，
并在非零自变量 `y : ℂˣ` 上陈述。记
$\varphi_m=\texttt{archRootVector}\ c\ \beta\ m$，用 $W_\beta$
表示该参数下的 Whittaker 值。
其中 `directProfile_from_whittaker_character` 与
`reflectedProfile_from_whittaker_character` 直接使用现有
`complexHeckeComponent`，证明

$$
W_\beta(\varphi_m,y)\theta_v(y)^{-1}=D_\theta(|y|^2),\qquad
W_\beta(\pi(w)\varphi_m,y)\theta_v(y)=H_\theta(|y|^2).
$$

记 `A = 4/c²`，

$$
G_\theta(s)=\Gamma(a+s+i\rho-1/6)\Gamma(a+s+i\rho+1/6).
$$

直接 Mellin 公式的常数为
`C₋ = (1/2) A^(a+iρ)`，反射轮廓为
`C₊ = (1/2) A^(a−iρ)`。
两个 `HasMellin` 定理同时提供绝对可积性与积分值。
在共同收敛条带 `−1/3 < Re(s) < 1/3` 内，

$$
\mathcal M H_\theta(s)=
\mathcal M D_\theta(-s)\,
A^{2s}A^{-2i\rho}
\frac{G_{\theta^{-1}}(s)}{G_\theta(-s)}.
$$

将反射轮廓乘以明确的固定单位相位 `A^(2iρ)` 后，公式中的
`A^(−2iρ)` 消失。所有整数角权都使用同一开条带。
有限个复位的乘积公式也已写出；它陈述局部 Mellin 变换的有限乘积，
没有预设全局商空间上的测度分解。

## 按任务规矩 3 给出径向符号修正

`reflectionMultiplier_eq_gamma_quotient` 展开项目原定义，得到其
Gamma 部分如下；本节的 `Gθ` 表示对所有复位取乘积，即项目的
`archGammaProduct K θ`：

$$
\frac{G_\theta(s)}{G_{\theta^{-1}}(-s)}.
$$

上述真实正向轮廓的反射公式需要

$$
\boxed{\frac{G_{\theta^{-1}}(s)}{G_\theta(-s)}}.
$$

本次保留原定义，新增

```lean
directReflectionMultiplier K S F θ u κ s :=
  reflectionMultiplier K S F θ⁻¹ u κ s
```

并证明其精确分解。这是对正确陈述的明确适配。
若所有复位的径向参数均为零，
`directReflectionMultiplier_eq_of_radial_zero` 证明两者相同。

对每个复位取 `cᵥ > 0`，在共同条带 `−1/3 < Re(s) < 1/3`
及明确的尺度归一化 `F.A₀ = ∏v (4/cᵥ²)` 下，
`directReflectionMultiplier_mellin_product` 进一步证明：正向局部
Mellin 变换在 `−s` 的乘积乘以这个修正乘子，等于反射后的归一化
局部 Mellin 变换在 `s` 的乘积，再乘以现有的
`F.C₀⁻¹ * finiteMellinFactor K S F u κ s`。因此实际有限因子和常数
都保留在等式中。

`ProjectArchimedeanSign.lean` 给出非零径向参数下两个局部 Gamma 商
不同、且不能用非零固定标量相互补偿的可检验见证。见证使用 Mathlib 总定义 Gamma 函数在零点的值及
复数除法约定，明确作为特殊函数表达式的区分；没有声称见证点位于
上述积分的收敛条带。其位置是 `s = a − 1/6 − iρ`，
实部 `a − 1/6 ≥ 1/3`，仍位于项目乘子使用的 `Re(s) > −1/3` 半平面内。

## 本任务完成的接口与其余全局任务

本次完成项目有限位定义的识别、有限和计算与数字接口，以及复位实际
向量、轮廓、Mellin 对和正确乘子的接线。`LocalThetaInput` 本身在原项目中
定义为数字表接口，因此构造该接口的意义与原声明一致。

仍属其他任务的内容是全局 KP 系数数据、该全局模型中的有限位向量实现、
全局商空间的测度分解/Fubini 及完整 marked reflection。
这里的有限和接线直接针对 `MarkedThetaReflection` 的定义完成，
没有调用旧报告中未编译的 `ActualExteriorAdapter.lean.txt`。

## 编译与公理审计

2026-10-30（UTC），[定向 CI 验证通过](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41127778382)。验证提交为
[`6b23655615d0d1dcdd75859b81138ac023ee18a7`](https://github.com/Rogerhu12/hecke-seven-eighths/commit/6b23655615d0d1dcdd75859b81138ac023ee18a7)。本报告的补充提交仅新增报告，八个 Lean 文件与该验证提交一致。

| 项目 | 已验证结果 |
| --- | --- |
| Lean | `4.35.0-rc3`，commit `470d5ce1400764999581fd26d5d72b00d990b0f4`，Linux x86_64 |
| Mathlib | `0493595ecd5da8ef14742febab99728f98e948e8` |
| 项目编译选项 | `autoImplicit = false`、`relaxedAutoImplicit = false` |
| `lake build HeckeSkeleton.ThetaLocal.ProjectAudit` | 通过，Lake 报告 `Build completed successfully (9318 jobs).`；此计数含依赖缓存复用 |
| 独立运行 `ProjectAudit.lean` | 通过，86 个显式公开定义/定理均有公理记录 |
| 公理白名单检查 | 86 项均通过，公理并集为 `propext`、`Classical.choice`、`Quot.sound` |

完整构建入口涵盖以下八个新增模块：

- `HeckeSkeleton.ThetaLocal.ProjectResidue`
- `HeckeSkeleton.ThetaLocal.ProjectFinite`
- `HeckeSkeleton.ThetaLocal.ProjectDigitTable`
- `HeckeSkeleton.ThetaLocal.ProjectArchimedeanSign`
- `HeckeSkeleton.ThetaLocal.ProjectArchimedean`
- `HeckeSkeleton.ThetaLocal.ProjectArchimedeanWhittaker`
- `HeckeSkeleton.ThetaLocal.Project`
- `HeckeSkeleton.ThetaLocal.ProjectAudit`

新增 Lean 源码没有 `sorry`、`axiom` 声明或 `native_decide`。
CI 沿用仓库原始导入与配置，并自动检查审计清单非空、每个声明均有输出，且公理集合没有超出上述三项。

完整项目环境中的复现入口：

```sh
lake build HeckeSkeleton.ThetaLocal.ProjectAudit
lake env lean HeckeSkeleton/ThetaLocal/ProjectAudit.lean
```

AI-assisted：本次适配、证明审查与验证由 OpenAI ChatGPT
（GPT-6 Astra Pro）协助完成。
