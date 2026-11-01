# EX-SMALL：实际小行估计接线

本说明记录 PR #5 的小行证明链。以下新模块目前仍须通过整条 Lean 构建和声明公理审计；不能仅凭源码无占位把 EX-SMALL 标为完成。

## 固定的实际表达式

估计对象是 `finiteRowContourBlock`，其行集恰为

```lean
(frequencyRows K S (Z ^ (1 / 16 : ℝ))).filter
  (fun u => 0 < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u)
```

每一行采用原 `compensatedRowMellinKernel`、原算术 `arithmeticHighEulerData`、原全部 prime-window 槽和全部子集补偿。三条线固定为 `(B + e, 1/2, 17/50)`。

所用前提是已有的算术校准、允许生成元、目标在原 Hecke packet 中、目标在 S 外不分歧，以及原公共零边界 B。没有把小行估计、完整校正因子估计或所需 reciprocal 估计写成新输入结构。

## 证明模块

| 模块 | 实际结论 |
| --- | --- |
| `SmallRowNumerator` | 同一真实 row character 的 conductor 比较；所有非主行在 Re w=1/2 的 deleted L 分子为 `O(N(u)^(3/5) (2+|Im w|)^k)`；加行权和实际计数得到 63/50。 |
| `SmallRowEulerBounds` | 五种真实分歧局部表均满足带 q^s 权误差界；从相应外轮廓半空间推导平方根代价。 |
| `SmallRowCorrection` | 未分歧和全部分歧局部补偿的外轮廓界；非零分母来自真实有限表 cutoff，不是附加局部界假设。 |
| `SmallRowCorrectionSums` | 实际完整 correction 为 `O(N(u)^eta Z^(17/300))`，包括所有槽、所有子集和原未标记 Euler product。 |
| `SmallRowNormContinuation` | 原 norm-twist continuation 的逐点公式 `Q(s)/(s-1-it)`；Q 来自实际 pole-cleared theorem，其多项式增长由实际 principal ray-character convexity 与整函数唯一性得到。 |
| `SmallRowNormReciprocal` | `Q(s)/(s-it)` 的实际 Euler logarithm 和缓冲 reciprocal 界，唯一零排除前提仍是原公共边界 B。 |
| `SmallRowReciprocal` | 一个常数覆盖全部物理行的分母，包括有界 pure-norm 例外。 |
| `SmallRowMellin` | 原 additiveFourier 的真实正 Mellin 绝对矩可积；通过实际径向 Haar 与 Fubini 得 additiveMellin 在 Re z=17/50 上的统一界；原 annular denominator 在 Re w=1/2 的统一界。 |
| `SmallRowKernel` | 原完整 kernel 的逐行界，精确外尺度为 `B + e - 629/800`，行尺度为 `13/50 + 2*eta`。 |
| `SmallRowSum` | 对原有限小行集求和、按原三次 set integral 积分，得到 1/50 saving；显式保留尚待独立证明的 primeNormalizer 逆因子。 |

## 纯 norm 例外没有被删去

有限阶 row character 不改变背景的无限位径向参数。因此，对于固定 psi，任何等式

```lean
psi * conjugate (R.character u) = heckeNormTwist K t
```

都会强制 `t = -heckeRadialParameter K v psi`，其中 v 在选择常数前固定。所有有界例外行可使用同一个实际 norm-twist 函数，不依赖高行 cutoff 或有限纤维截断。

令 `f(s)=Q(s)/(s-it)`。在 `Re s≥1/2` 上，

\[
\left|\frac{s-1-it}{s-it}\right|\le1,
\qquad
|L(s,N^{it})^{-1}|\le |f(s)^{-1}|.
\]

第二个不等式使用原选定 continuation 的逐点等式，包含原 pole 点的总除法取值 0；该点没有被删除。Q 在 pole 非零由已有真实简单极点定理供应。其余区域非零性只用原公共 packet 边界。

## 精确指数

分子 3/5、原行权 -17/50、两个独立 row-subpower 因子给逐行幂

\[
\frac35-\frac{17}{50}+2\eta=\frac{13}{50}+2\eta.
\]

三个物理尺度因子与完整 correction 的尺度相加为

\[
\frac{17}{48}\left(\frac12-\frac{17}{50}\right)
+B+e+\frac{17}{50}-1
+\frac{23}{48}\left(\frac12-1\right)
+\frac{17}{300}
=B+e-\frac{629}{800}.
\]

真实频率行的线性计数，结合 `U=Z^(1/16)`，再增加

\[
\frac{1+13/50+2\eta}{16}=\frac{63}{800}+\frac\eta8.
\]

故 `exists_actual_small_block_before_normalizer_bound` 的结论为

\[
\bigl|\text{finiteRowContourBlock}\bigr|
\le C\,|\text{primeNormalizer}(Z)^{-1}|\,
Z^{B-11/16-1/50+e+\eta/8}(1+H)^A.
\]

该结论对所有 `H≥1` 成立，未利用高度 ceiling；原 `TSmallRowInput` 允许的高度多项式由三次有限盒积分增加 3 次幂。实际固定 `physicalResidueNormalizer` 的逆保留并吸收到常数中。

## 仍须消去的独立归一化因子

最终接入实际 `TSmallRowInput` 还需要 actual empty-ray `primeNormalizer` 的任意小正幂 reciprocal 界。目前 `HeckeSkeleton/PrimeNormalizer.lean` 的旧 `normalizer_smallPower` 经过 `window_prime_lower` 的 admission，因此本证明链没有调用它。

一旦该独立实际标量界完成，对所需 `loss>0` 取上面的 `eta=4*loss`，再给 normalizer 分配 `loss/2`，即得到原目标的总 `loss`，不改变 1/50 saving、行集、轮廓或常数的量化顺序。

完整构建目标可用 `HeckeSkeleton.ExpansionModels.SmallRowSum`。所有新增 endpoint 的 `#print axioms` 必须只包含 `propext`、`Classical.choice`、`Quot.sound`，且其模块必须实际构建成功。
