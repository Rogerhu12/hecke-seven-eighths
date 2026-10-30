# 接线：素数槽消去 → 项目的 Hecke L 函数与矩模型

`PrimeCancellation/` 是上一轮交付的消去核心（23 个模块，只依赖 Mathlib）。它从抽象的 L 函数数据出发：全纯、无零区、多项式增长、Euler 恒等式，推出配对能量界。

**目标**：给 `HeckeSkeleton/Moments.lean` 的 MI-P-PRIME-CANCELLATION-BELOW-ONE（`paired_primes_below_one`）提供实际输入，包括以下几项：
- 用项目的 `heckeDeletedContinuation`、`primeCoefficient` 实例化它的 L 函数数据；
- 无零区来自 `c.family.boundary`；
- 增长界可参考 `HeckeSkeleton/HeckeStripPolynomial.lean`、`HeckeUniformStripGrowth.lean`、`HeckeBufferedReciprocal.lean`。

上一轮报告指出了几处项目陈述的缺陷，见 `PrimeCancellation/README.txt` 第五节和 `MOMENT_WIRING_AUDIT.txt`：
- `WholeMomentProfileControl` 没有覆盖素数窗口；
- 非主性需要额外的条件；
- 校准只覆盖物理行。

这些缺陷请一并给出修正方案。`momentModels` 仍是 `sorry` 数据（MI-M-MODELS），所以最终接线可以停在"对任意满足某组性质的模型"成立的形式，但这组性质要是实际模型能够满足的。
