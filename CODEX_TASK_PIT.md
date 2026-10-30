# 独立任务：窗口中的素理想定理（PR-WINDOW-PIT）

本说明自成一体。构建与工作区约定同 [CODEX_TASK_DESCENT.md](CODEX_TASK_DESCENT.md) 的"环境与构建"一节：只做单模块构建，不跑全量构建，不提交，不碰论文文件。

**内存很紧。** 本机同时还有别的代理在编译，每个 lean 进程约占 3.3 GB 内存、8.4 GB 提交。一次只跑一个构建；遇到 "failed to read file …olean" 就等几分钟再跑。

## 目标（2026-10-30 晚更新）

PR-NORMALIZER-POSITIVE 和 PR-NORMALIZER-SMALLPOWER 已经由 `HeckeSkeleton/PrimeNormalizer.lean` 从下面这一条推出，推导部分已编译通过。现在只剩这一条：

```lean
-- OBLIGATION PR-WINDOW-PIT（HeckeSkeleton/PrimeNormalizer.lean）
theorem window_prime_lower (w : SmoothAnnularTest)
    (hre : ∀ y, (w.toFun y).im = 0) (hnn : ∀ y, 0 ≤ (w.toFun y).re)
    (hne : ∃ y, w.toFun y ≠ 0) (hsupp : Function.support w.toFun ⊆ Set.Ioo 1 2) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X / Real.log X ≤
        ∑ p ∈ windowPrimes K S X, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re
```

其中 `windowPrimes K S X` 是范数不超过 2X、不在 S 中的素理想。证明写在新模块里（例如 `HeckeSkeleton/WindowPIT.lean`），由主代理替换 `PrimeNormalizer.lean` 中的 `sorry`；不要改 `Principal.lean`。估计 6,000–8,000 行。

下面"定义"和"需要的数论输入"两节保留作背景。

## 定义（`HeckeGeneral/Analysis/PhysicalProbePrincipal.lean`、`PhysicalProbeData.lean`）

- 归一化常数：`primeNormalizer = (-1)^slots · Z^(-1/36) · ∏ᵢ normalizerSlot i`；
- 每个槽的和：`normalizerSlot i = ∑_{p ∈ primeWindow i} windowWeight i p · N(p)^(-5/6)`；
- 窗口：`primeWindow i` 由范数不超过 2·primeScale 的素理想 p ∉ S 组成，且要求 `(g.weight i)(N p / primeScale) ≠ 0`；
- 尺度：`primeScale = Z^((1/6)/slots)`；
- 窗口几何 `PrimeWindowGeometry` 的条件：`slots` 为偶数，所以 (−1)^slots = 1；权重非负实值、光滑、不恒为零，支撑在 (1,2) 内且两两不交。

## 需要的数论输入

需要证明：对每个这样的权重 w，存在 c > 0 和 X₀，使得对所有 X ≥ X₀，

  ∑_{p ∉ S} w(N p / X) · N(p)^(-5/6) ≥ c · X^(1/6) / log X。

由此两项都成立：

- 每个窗口的和是正实数，所以 Re(primeNormalizer) > 0；
- primeNormalizer ≫ Z^(-1/36) ∏ᵢ primeScale^(1/6)/log Z ≍ (log Z)^(-slots)，因此 1/primeNormalizer = O(Z^ε)。

注意：w 的支撑是 (1,2) 中某个开区间，所以这里需要在固定比例区间 (αX, βX) 里的素理想计数，也就是素理想定理（Landau）。Chebyshev 型的上下界不够用。

## 可能的路线

Mathlib 里没有素数定理，也没有 Wiener–Ikehara。可以考虑：

- **用 Axiom 上游的零点自由半平面。** `DedekindZetaZeroFree`：ζ_K(s) 在 Re s > 31/32 没有零点，见 `Challenge/DedekindZetaChallenge.lean` 与 `Solution/`。有了它，用光滑化的 Perron 公式（对 w 做 Mellin 变换，围道移到 Re s = 31/32 + δ），可以得到

    ∑ Λ_K(𝔞) w(N𝔞/X) = X · ∫ w + O(X^(31/32+2δ))，

  再去掉素理想幂和 S 中的素理想。需要 −ζ_K′/ζ_K 在该半平面内竖直方向上的多项式增长界，先在 Axiom 和 HeckeGeneral 里搜索：`HeckeContinuation`、`HeckeStripPolynomial`、`MellinInverseLine`、`VerticalLineIdentity`、零点检测相关模块、对数导数界。
- **或者在 Mathlib 之上自己形式化一个 Tauberian 定理**，例如 Newman 的证明。工作量更大。

先调研，选定路线后在 `CODEX_PIT_PLAN.md` 写一页计划，再动手。

## 完成标准

1. 新模块构建通过，没有 sorry，给出与 `window_prime_lower` 完全相同的陈述。
2. `PrimeNormalizer.lean` 引用它之后能编译。
3. `#print axioms` 只有 `propext, Classical.choice, Quot.sound`。
4. 写 `PIT_CODEX_REPORT.md`，内容包括：路线、文件与行数、检查输出。
