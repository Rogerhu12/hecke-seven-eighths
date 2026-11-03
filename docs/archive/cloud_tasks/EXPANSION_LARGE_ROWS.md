# EX-LARGE：实际绝对大行尾

## 本批范围与验证状态

本批新增实际大行估计链，末端为 `Expansion.Project.actual_tLargeRowInput`。
它直接估计仓库的 `absoluteLargeRowTerm`，不另造目标函数，不把大行结论、
prime normalizer 界或无限求和收敛性作为输入。

本批静态复核与 `git diff --check` 已完成。Lean 编译和各末端 `#print axioms`
仍等待统一构建 / 普通 CI；不能将以下源码陈述写成已通过验证。

## 文件与实际依赖

| 文件 | 提供的实际结果 |
| --- | --- |
| `HeckeSkeleton/ExpansionModels/LargeRowMellin.lean` | 对所有固定 `sigma > 0`，原 additive Fourier 的加权积分在真实 radial Haar 上可积，且原 additive Mellin 在整条竖线上一致有界；annular denominator 在任意固定实线上有界。 |
| `HeckeSkeleton/ExpansionModels/LargeRowCorrection.lean` | 原 full correction 在 `(2,2,sigma)`，`sigma >= 1`，满足 `C N(u)^eta Z^(sigma/6)`。所有行素数和全部局部表保留。 |
| `HeckeSkeleton/ExpansionModels/LargeRowAllScales.lean` | 在每一个原始尺度，直接以有限 tuple/subset 总和构造独立于行的正 majorant；不使用 eventual prime-window cutoff，不除以局部 Euler 因子。 |
| `HeckeSkeleton/ExpansionModels/LargeRowTail.lean` | 对真正的完整 frequency-row 集合，由既有线性计数推出所有负指数 `p < -1` 的 Summable，以及严格尾 `C U^(p+1)`。 |
| `HeckeSkeleton/ExpansionModels/LargeRowKernel.lean` | 原 kernel 在完整三条绝对竖线上满足 `C |primeNormalizer^-1| Z^(53/32+(13/16)sigma) N(u)^(eta-sigma)`。 |
| `HeckeSkeleton/ExpansionModels/LargeRowSum.lean` | 所有 `Z>=1,H>=1` 的原 `absoluteLargeRowTerm` 真正 Summable；渐近总和得到论文精确幂 `-17/32+(13/16+zeta)eta`。 |
| `Expansion/ActualLargeRowBound.lean` | 复用 `Expansion.ActualPrimeNormalizer`，对原空 ray-filter normalizer 吸收 `Z^(1/64)`，构造 `TLargeRowInput ... zeta (1+3/zeta) (1/2)`。 |

`LargeRowMellin` 没有假设 Fourier transform 可积。它使用实际 Fourier closure
得到任意 Schwartz 的 archimedean 因子和局部常值紧支撑的 finite 因子。
当 `sigma>1` 时，提高 Schwartz 阶数到 `M >= 2 sigma + 1`，逐 complex
coordinate 用

\[
 (1+r)^{-M} r^{2\sigma}\le (1+r)^{-3}r^2
\]

支配到已有、真正可积的 `sigma=1` multiplicative Haar envelope。
finite-place 正 Mellin 矩适用于所有 `sigma>0`。最后保留已有的正 Haar
比较标量，转回原 radial measure，再用已证明的 Fubini 恒等式识别
`additiveMellin`。

## 精确数值

固定 `zeta>0`，令 `sigma=1+3/zeta`。原 kernel 的三个尺度因子加起来是

\[
 \frac{17}{48}\left(\frac12-\sigma\right)+(1+\sigma)+\frac{23}{48}
 =\frac{53}{32}+\frac{31}{48}\sigma.
\]

真实 full correction 贡献 `sigma/6`，所以全 kernel 的尺度次幂为
`53/32+(13/16)sigma`。所有标量 L 因子在实部至少二处由实际 Euler
series / Euler logarithm 一致控制，行次幂只剩 `eta-sigma`。

对严格尾 `N(u)>U`，真正线性计数和几何求和给出

\[
 \sum_{N(u)>U}N(u)^{\eta-\sigma}\le C U^{1+\eta-\sigma},
 \qquad \eta<\sigma-1.
\]

取 `U=Z^(13/16+zeta)`，最终精确指数是

\[
 \frac{53}{32}+\frac{13}{16}\sigma+
   \left(\frac{13}{16}+\zeta\right)(1+\eta-\sigma)
 =-\frac{17}{32}+\left(\frac{13}{16}+\zeta\right)\eta.
\]

本批选取预先固定的 `eta=1/(64(1+zeta))`，保留至少 `33/64` 的绝对 saving。
真正 normalizer 的逆因子用 `1/64` 次幂吸收后，得到

\[
 \sum_u\operatorname{absoluteLargeRowTerm}(u)
 \le C Z^{-1/2}(1+H)^3.
\]

三次盒积分仅贡献原盒体积 `(2H)^3` 与已有 `(2 pi)^(-3)`，没有交换一个
移动行集与积分。对每个固定严格行尾，先证明 Summable 再使用其 `tsum`。

## 参数与对象约束

中间几何 / correction / tail 常数在全部行、scale、height 之前选择。
`zeta` 和相应实 contour 在目标之前固定，末端目标相关常数由实际测试函数、
局部 Haar、固定场及排除素数集决定。高度估计对所有 `H>=1` 成立；旧接口所需
`H<=Z^ceiling` 可取 `ceiling=1`，高度次数为三。

末端只要求 totally complex 的原场、实际 probe、`ThetaCalibrationInput`、
目标在原 exterior primes 处不分歧，以及 `zeta>0`。绝对大行不需要共同零界、
non-norm 排除或只删去某些有界例外行。

`TLargeRowInput.absolute` 要求所有 `Z>=1`，并非只要求渐近大 `Z`。因此本批
专门保留 `LargeRowAllScales`：它直接对原有限 subset compensation 求绝对值，
在固定 `Z` 构造行无关的 scalar mass，再接已经证明的整个 row power 的
Summable。这个步骤覆盖 asymptotic local cutoff 以下的全部尺度。

新 `physicalPoissonScalar` 和修正后的 `physicalResidueNormalizer` 均保留在
literal kernel factorization 中；固定的正 Poisson 标量只并入固定常数，没有
更换原 kernel 的值。最终目标 theorem 与真实原 row/prime 窗口语义保持一致。
