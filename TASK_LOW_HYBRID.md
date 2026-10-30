# 独立任务：混合能量与冻结立方（LOW-HYBRID 与 LOW-FROZEN-CUBE）

估计约 1.1 万行（LOW-HYBRID 约 4,500，LOW-FROZEN-CUBE 约 6,500）。本文件自成一体。

## 1. 数学内容

论文引理 4.6–4.8（`weil_seven_eighths_revised.tex` 第 2008–2339 行：`lem:completed-quadratic-reduction`、`lem:can-hybrid`、`lem:can-marked-energy`）要估计带标记反射的 theta 行能量。本任务覆盖其中两个与 theta 反射无关的部分：

**LOW-HYBRID（引理 4.6–4.7，二次–三次混合范数）。** 对外部理想上的系数 a(P)、β(n, b)，证明对所有 K₀、N₀、B₀、L₀ ≥ 1：

  Σ_{k 行} | Σ_P a(P)/√N(P) · [P 与 k 互素] · Σ_{n,b} β(n,b) · χ_k(nb)³ · χ_P(n)^{-2} · [P 与 b 互素] |²
    ≤ C · (K₀N₀B₀L₀)^ε · (K₀ + N₀B₀) · B₀ · (N₀ + L₀ + (N₀L₀)^{2/3})。

这里 χ_k(x) 是六次剩余符号。证明只用两个已证的大筛：
- 二次大筛 `QuadraticSieveBound`；
- 三次大筛 `CubicSieveBound`（BGL n = 3）。

要点是 Cauchy–Schwarz 的顺序：**不要对每个 b 单独做 Cauchy**。旧笔记 `…\Hecke L\.cache\hard-splits-20261029\low-hybrid-complete-paper-reduction.md` 有一份完整的纸面推导，可只读参考。

**LOW-FROZEN-CUBE（引理 4.8 的行分解部分）。** 把行理想分解为 k = k_pow · k_sup · d，各素位的赋值写成 e_p = e_min + 3x_p，完整立方写成 b = x · n′。然后证明：
- 系数 a(P)、β(c′, b) 与行无关；
- 碰撞掩码；
- 重叠为零的引理。

最后得到可以直接喂给 LOW-HYBRID 的形式。

## 2. Lean 中的现有对象

- **六次符号**：`HeckeGeneral.ThetaSkeleton.Global.idealSymbol K S D I a`，其中 `D : ThetaArithmeticData K S`。允许生成元为 `D.generator I`，互反为 `AllowedGeneratorInput.reciprocity`。
- **两个大筛**（`HeckeSkeleton/Moments.lean` 第 244–265 行，均已证明）：

```lean
def QuadraticSieveBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (ExteriorIdeal K (places K c)),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K (places K c) I ≤ X) →
      (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm K (places K c) J ≤ Y) →
      ∀ z : ExteriorIdeal K (places K c) → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J * idealSymbol K (places K c) (probeData K c).arithmetic J
            ((probeData K c).arithmetic.generator I) ^ 3‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y) * ∑ J ∈ B, ‖z J‖ ^ 2

def CubicSieveBound : Prop :=   -- 同样形式，指数 e = ±2，右端 (X + Y + (X*Y)^(2/3))
```

- **证明位置**：`HeckeAxiom/QuadraticSieve.lean`（`HeckeAxiom.quadratic_sieve_bound`，对任意 `ArithmeticChoice` 成立）和 `CubicSieve/Complete.lean`（`CubicSieve.Complete.targetBound`）。
- **陈述方式**：新定理对一般的 `S`、`D` 陈述，以两个大筛的结论为假设，不要绑定 `TargetContext`。

## 3. 建议的陈述

```lean
theorem hybrid_energy (hq : QuadraticSieve-形式假设) (hc : CubicSieve-形式假设) (ε) (hε : 0 < ε) :
  ∃ C, 0 < C ∧ ∀ K₀ N₀ B₀ L₀ ≥ 1, ∀ (rows : Finset (ExteriorIdeal K S)) (a β …), （支撑与范数条件）→
    ∑ k ∈ rows, ‖…‖ ^ 2 ≤ C * (K₀*N₀*B₀*L₀)^ε * (K₀ + N₀*B₀) * B₀ * (N₀ + L₀ + (N₀*L₀)^(2/3:ℝ)) * (系数质量)
```

系数质量与精确的支撑条件，以论文引理 4.7 为准。

LOW-FROZEN-CUBE 的出口：把引理 4.8 中行能量的相应部分改写成 `hybrid_energy` 的左边，并给出各参数的账本，即论文的 (can-terminal-ledger)。

## 4. 可用材料

- openai 的 ℚ(ω) 版本（只读）：
  - `C:\Users\Boyang\Desktop\Math\Hecke L\.cache\openai-math-fd4aeeb2\lean\OAI\NumberTheory\DirichletL\Descent\{Hybrid,HybridBound,HybridReduction,SieveComposition,SourceHybrid,Quadratic}.lean`
  - `Reflection/UniformSieve.lean`
  - `Reflection/{Frozen*,Cube*,Inactive*,MarkedOverlap,Cofactor,Columns,Sector*}.lean`
  - 推广方式：ℤ[ω] 的理想换成 `ExteriorIdeal K S`，元素换成允许生成元，三次符号换成 `idealSymbol` 的幂。
- 已完成的移植样例：`HeckePort/CenteredMoment/`。

## 5. 完成标准与约束

**完成标准**
1. 新模块（`HeckeSkeleton/LowHybrid.lean`、`HeckeSkeleton/LowFrozenCube.lean`，或其下的子目录）构建通过，没有 `sorry`、`axiom`、`native_decide`。
2. `#print axioms` 只有标准三条。
3. 写一页报告：各定理的陈述和假设，以及与引理 4.6–4.8 的对应关系。

**约束**
- 一次只构建一个模块。
- 不修改现有文件，不提交。
- openai 与旧缓存只读。
