# 独立任务：theta 反射的局部部分（TH-REFL-ARCH 与 TH-REFL-EXTERIOR-DIGITS）

估计约 1.05 万行（阿基米德部分约 5,500，外部数字表约 5,000）。本文件自成一体。

## 1. 数学内容

论文的固定型 theta 反射（`weil_seven_eighths_revised.tex` 第 634–1206 行：命题 3.4 `prop:fixed-type-theta`、引理 3.2/`lem:mark-digits`、定理 3.5 `thm:marked-expansion`）把带标记的 theta 和反射成对偶和。全局反射需要两类局部计算，本任务只做这两类，都是**纯局部**的，不依赖全局的 KP 系数表。

**TH-REFL-ARCH（阿基米德侧）。**
- 在每个复位上，取高 K-型向量 φ_m = E^m φ°，对应的 Whittaker 函数为
  W(z) = |z|^a (z/|z|)^m K_{1/3}(c |z|^{1/2})，
  并满足 π(w) φ_m = φ_{−m}。
- 证明正向与反射的 Mellin 对：
  M[反射轮廓](s) = M[正向轮廓](−s) · A₀^{2s} · ∏_v (Gamma 商)，
  也就是乘子恒等式 (theta-multiplier)。
- 给出常数 C₀、A₀ 的显式值，供后续的 KP 系数表使用。
- 固定无穷型 (m_v, τ_v) 是新内容：Axiom 只有角权 ±1、τ = 0 的情形，即 Γ(s+5/6)Γ(s+7/6)。

**TH-REFL-EXTERIOR-DIGITS（外部素位的数字表，引理 3.2）。**
- 标记数字表：
  - 不活跃分支取值 q^{-1}；
  - 活跃分支取值 q^{-1/2} γ₂ χ(t)²，只在 e = 0 时出现。
- 普通表（can-weyl-table）。
- 把骨架里已定义的局部对象，与 Weyl 作用下的实际局部计算一一对应：`localWeylScalar`、`localWeylExponent`、`digitMask`、`sphericalDigit`、`localTau`（见 `HeckeGeneral/Analysis/MarkedThetaReflection.lean` 及其邻近文件，用 grep 查找）。

## 2. 交付形式

在新模块中证明局部恒等式与估计。陈述只涉及：
- 单个复位、或单个外部素位的对象；
- 显式的 Gamma、Bessel 函数；
- `idealSymbol`、`thetaGamma` 等算术对象。

不要碰 `finiteMellinData`（全局 KP 数据，另一个任务）。

**建议的出口**

```lean
-- 阿基米德侧（新定义 archDirectProfile、archReflectedProfile）
theorem arch_reflected_mellin (m : ℤ) (τ : ℝ) … :
  mellin (archReflectedProfile …) s =
    mellin (archDirectProfile …) (-s) * A₀ ^ (2 * s) * (Gamma 商)
-- 外部数字表
theorem mark_digit_table (p) (e : ℕ) … : localDigit … = （按引理 3.2 的分支取值）
```

精确形式以论文第 634–1206 行为准；凡是要新增的定义，在报告中列出。

## 3. 可用材料

- **Axiom**（项目内 `DedekindZetaZeroFree/`）：
  - `Theta/Whittaker/ComplexRootDerivativeVectors.lean`（`whittaker_complexUpperRootDerivatives`）
  - `Theta/Whittaker/ArchimedeanDerivativeMultipliers.lean`
  - `Theta/Profiles/ThirdBesselMellinTransform.lean`
  - `Theta/Digits/SexticReflectedLocalModel.lean`
  - `Theta/Digits/Exterior/LocalDigitValues.lean`（`nonzero_localDigit`）
- **旧仓库**（只读）：`C:\Users\Boyang\Desktop\Math\Hecke L\experiments\Axiom435Intake\AngularThirdBesselMellin.lean`，255 行，在 4.35 上原生编译通过。内容是一般 (a, τ) 的正向 Mellin，可直接复制改用。
- **openai**（只读）：`…\Hecke L\.cache\openai-math-fd4aeeb2\lean\OAI\NumberTheory\DirichletL\Descent\{MarkedPhase,MarkedReflection,MarkedFourier}.lean`，ℚ(ω) 上的标记数字。
- **项目内**：`HeckeGeneral/Analysis/ArchimedeanGamma*.lean`；`HeckeSkeleton/ThetaKernel/Gamma.lean`（竖带上 Gamma 商的多项式界，已证）。

## 4. 完成标准与约束

**完成标准**
1. 新模块（`HeckeSkeleton/ThetaLocal/*.lean`）构建通过，没有 `sorry`、`axiom`、`native_decide`。
2. `#print axioms` 只有标准三条。
3. 写一页报告：新定义、定理陈述，以及哪些部分与论文对应。

**约束**
- 一次只构建一个模块。
- 不修改现有文件，不提交。
- openai、旧仓库只读。
