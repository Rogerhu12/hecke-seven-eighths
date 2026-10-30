# 独立任务：高 bin 行的 Euler 数据（HB-EULER-INITIAL 与 HB-EULER-EXCEPTIONAL）

估计约 1 万行（初始校准约 5,000，例外表约 4,000，数据构造约 1,000）。本文件自成一体。

## 1. 数学内容

论文命题 6.3 的高 bin 估计（`weil_seven_eighths_revised.tex` 式 (6.10)、(6.13)，第 38–42 页）要用一个**四理想行的 Fourier 级数**。对每个频率行 u，把它写成三变量 (s, w, z) 的 Euler 乘积，并解析延拓：

  初始级数 = ζ_K^{(S)}(6z) · L^{(S)}(w, χ_u) / L^{(S)}(s, ψ·χ̄_u) · R_u(s, w, z)。

其中：
- `initialRowEulerSeries`：在 Re s > 4、Re w > 4、Re z > 2 上绝对收敛的理想和；
- χ_u：行特征；
- R_u：逐素位的修正乘积。
  - 在**正则素位**上，R_u 的局部因子是一个有理函数（已定义为 `localRowCorrection`）。
  - 在**例外素位**上，即整除行理想或属于固定集合 Q 的素位，局部因子是一张**有限有理表**（`FiniteEulerRational`），要从初始级数的局部 Euler 因子实际算出来。

本任务分三步：
1. **构造数据**：给出例外素位上的有理表，作为 `RowEulerData.exceptionalFactor`。
2. **HB-EULER-INITIAL**：证明在初始区域上级数绝对收敛、等于上面的延拓式；证明修正乘积在区域 `rowEulerRegion` 上可乘、解析。
3. **HB-EULER-EXCEPTIONAL**：在动态直线 Re s = a + 16e、Re w = 1 − a − 6e、Re z = 17/50 上，对范数超过某个截断的例外素位 p ∉ Q，证明 |表值 − 1| ≤ C · N(p)^β，其中 β = −10e（p 整除 u），否则 β = −1 − 10e。

## 2. 现有的 Lean 定义

`HeckeGeneral/Analysis/PhysicalProbeContours.lean`：

```lean
def rowExceptionalPrimes (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) :
    Finset (ExteriorPrime K S) := exteriorSupport K S u.ideal ∪ Q

structure RowEulerData (P : ProbeData K S) where
  rows : RowCharacterInput K S P
  exceptionalFactor : ∀ (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S),
    {p : ExteriorPrime K S // p ∈ rowExceptionalPrimes K S Q u} → FiniteEulerRational

def localRowCorrection (P : ProbeData K S) (ψ χ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s w z : ℂ) : ℂ :=
  let q : ℂ := (p.val.asIdeal.absNorm : ℂ)
  let V := q ^ (-6 * z)
  let W := primeCoefficient K χ p.val * q ^ (-w)
  let D := primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) * q ^ (-s)
  let E := primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 * q ^ (4 - 6 * s) * V
  rowEulerRationalValue q q⁻¹ V W D E

def rowCorrection P ψ (E : RowEulerData K S P) Q u (s w z : ℂ) : ℂ :=
  ∏' p : ExteriorPrime K S,
    if hp : p ∈ rowExceptionalPrimes K S Q u then
      finiteEulerRationalValue (E.exceptionalFactor Q u ⟨p, hp⟩) (p.val.asIdeal.absNorm : ℝ) s w z
    else localRowCorrection K S P ψ (E.rows.character u) p s w z

def rowEulerContinuation P ψ E Q u (s w z : ℂ) : ℂ :=
  heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) *
    heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w /
    heckeDeletedContinuation K (ψ * conjugate (E.rows.character u)) (exceptionalPrimes K S) s *
    rowCorrection K S P ψ E Q u s w z

structure RowEulerCalibrationInput P ψ E : Prop where
  initial_absolute : ∀ Q u (s w z : ℂ), 4 < s.re → 4 < w.re → 2 < z.re →
      Summable (initialRowEulerTerm K S P ψ Q u s w z)
  initial_identity : ∀ Q u (s w z : ℂ), 4 < s.re → 4 < w.re → 2 < z.re →
      initialRowEulerSeries K S P ψ Q u s w z = rowEulerContinuation K S P ψ E Q u s w z
```

`HeckeGeneral/Analysis/TInputRanges.lean`：

```lean
def rowEulerRegion : Set (ℂ × ℂ × ℂ) :=
  {v | 1/2 < v.1.re ∧ 0 < v.2.1.re ∧ 0 < v.2.2.re ∧ 1 < v.1.re + v.2.1.re ∧
       5/6 < v.1.re + v.2.2.re ∧ 2 < v.1.re + v.2.1.re + 6 * v.2.2.re}

structure TRowEulerInput P ψ (E : RowEulerData K S P) : Prop where
  initial : RowEulerCalibrationInput K S P ψ E
  local_product : ∀ Q u (v : ℂ × ℂ × ℂ), v ∈ rowEulerRegion → Multipliable (fun p => …)
  correction_analytic : ∀ Q u, AnalyticOnNhd ℂ (fun v => rowCorrection K S P ψ E Q u v.1 v.2.1 v.2.2) rowEulerRegion
```

- 初始项 `initialRowEulerTerm`、初始级数 `initialRowEulerSeries` 在 `HeckeGeneral/Analysis/PhysicalProbeRows.lean`（约第 85–100 行）。
- `FiniteEulerRational`、`finiteEulerRationalValue`、`rowEulerRationalValue` 也在 HeckeGeneral 中。
- 骨架中的目标 `HeckeSkeleton/HighBin.lean` 第 205–250 行：

```lean
theorem highInitialEulerControl (c : TargetContext K) :
    TRowEulerInput K _ (targetData K c).probe (targetCharacter K c) (actualHighPresentation K c).euler
theorem highExceptionalEulerControl (c : TargetContext K) :
    HighExceptionalEulerControl K c (actualHighPresentation K c)
```

**阻塞点**：`actualHighPresentation` 本身还是 `sorry` 数据（HB-PRESENT），它的 `.euler` 字段正是要在本任务中构造的对象。

**做法**：在新模块中定义 `highEulerData (P) (ψ) : RowEulerData K S P`，并对它证明
- `TRowEulerInput K S P ψ (highEulerData …)`；
- 一个与 `HighExceptionalEulerControl` 等价的、不依赖 presentation 的一般例外表估计：对给定的 e、a 范围和直线，有统一的常数与截断。

主代理会在构造 `actualHighPresentation` 时取 `euler := highEulerData …`，再把这两条接上。`.rows` 字段用骨架已有的 `momentRowCharacters K c` 或 `arithmeticRowCharacterInput`。

## 3. 可用材料

- **已证的正则素位部分**：`HeckeSkeleton/HighEulerAlgebra.lean`、`HeckeGeneral/Analysis/RowEulerCompatibility.lean`、`RowEulerRational.lean`，还有 `fullHighEulerControl_of_initial_exceptional`（HighBin.lean）里正则素位的估计。
- **Hecke L 函数的删除型延拓**：`HeckeGeneral/Analysis/HeckeEulerDeletion.lean`（`heckeDeletedContinuation`）。
- **openai 的 ℚ(ω) 版本**（只读）：`C:\Users\Boyang\Desktop\Math\Hecke L\.cache\openai-math-fd4aeeb2\lean\OAI\NumberTheory\DirichletL\Detector\HighRows{Euler,Excluded,Local,Multiplicative,Prime,Region,Series,Summability,Unramified,Weights,Closed,Families,Ramified,Scalar,SharpScalar,ScalarBounds,Recurrence,Tail}.lean`、`Detector/HighValuations.lean`、`Detector/GaussValuation.lean`、`Hecke/LocalEulerIdentities.lean`、`FiniteEulerFactors.lean`。
- **旧缓存**（未编译，仅作参考）：`…\Hecke L\.cache\davenport-hasse-20261012\`，有限 Euler 系数。

## 4. 完成标准与约束

**完成标准**
1. 新模块（例如 `HeckeSkeleton/HighEuler.lean`）构建通过，没有 `sorry`、`axiom`、`native_decide`。
2. `#print axioms` 只有 `propext, Classical.choice, Quot.sound`。
3. 写一页报告：给出定义的数据，以及两条定理的确切陈述。

**约束**
- 一次只构建一个模块，不跑全量构建。
- 不修改现有文件，不提交。
- openai 目录与旧缓存只读。
