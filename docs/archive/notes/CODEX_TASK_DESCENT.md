# 独立任务：关闭阿贝尔下降的 4 个 sorry（DE-*）

本说明自成一体：做这件事不需要了解骨架的其他部分。项目背景见 [HECKE_PORT.md](HECKE_PORT.md)，但不必先读。

## 目标

`HeckeSkeleton/Descent.lean` 里的 4 个 sorry：

| 义务 | 声明 | 内容 |
|---|---|---|
| DE-ARTIN-CHARACTERS | `artinCharacters : Finset (HeckeCharacter F)` | Gal(F(ζ₁₂)/F) 的有限特征，经类域论看成 F 上的 Hecke 特征 |
| DE-TRIVIAL-FACTOR | `one_mem_artinCharacters` | 平凡特征属于这个集合 |
| DE-EULER-FACTORIZATION | `artinEulerProduct` | 在 Re s > 1 上，`heckeContinuation (Extension F) (normPullback F χ) s = ∏ ψ ∈ factors F χ, heckeContinuation F ψ s`，其中 `factors F χ = (artinCharacters F).image (χ * ·)` |
| DE-POLE-MATCHING | `poleMatching` | 在 Re s > 7/8 的每一点，要么所有因子都解析；要么恰有一个因子有单极点，此时上层 L 函数在该点也有单极点，其余因子都解析 |

这里 `Extension F = CyclotomicField 12 F`，文件里已经给了 `FiniteDimensional` 和 `IsAbelianGalois` 实例。`normPullback` 已经定义好，是沿真实的 idele 类群范数做拉回。下游的 `continuedFactorization`、`factorizationData` 和 `descend` 都已从这 4 项推出，消费者是 `HeckeGeneral/Analysis/HeckeEndpointTarget.lean` 中的 `HeckeFactorizationDescentData`。

**不要改这 4 个声明的陈述，也不要改 `HeckeFactorizationDescentData`。** 如果某一项按现有陈述证不出来（最可能出问题的是分歧素位处的 Euler 因子），就停下来，写清楚卡在哪里。

## 完成标准

1. `LEAN_NUM_THREADS=4 lake build HeckeSkeleton.Descent` 通过，`Descent.lean` 里不再有 sorry。
2. 在一个临时文件里写：

   ```lean
   import HeckeSkeleton.Descent
   #print axioms HeckeSkeleton.Descent.descend
   ```

   用 `lake env lean <临时文件>` 运行，结果只能是 `propext, Classical.choice, Quot.sound`。`descend` 把 TIP 输入当作假设，所以 4 项都关掉以后，这里不应再出现 `sorryAx`。
3. 最后跑一次 `LEAN_NUM_THREADS=4 lake build HeckeSkeleton.Audit 2>&1 | grep -o 'SKELETON_DECL|[^|]*|[^|]*|true' | sort -u | wc -l`。现在的结果是 60，做完应为 56。
4. 在项目根目录写 `DESCENT_CODEX_REPORT.md`，内容包括：新增文件及行数、从候选代码复用了什么、遇到的陈述问题、以上三项检查的输出。

## 工作范围

- **新代码的位置**：放在 `HeckeSkeleton/Descent/` 下，例如 `HeckeSkeleton/Descent/ArtinFactors.lean`，命名空间用 `HeckeSkeleton.Descent.Artin` 之类，避免和文件本身的命名空间冲突。`HeckeSkeleton` 库的 glob 是 `HeckeSkeleton.+`，新文件会自动归入这个库。
- **已有文件**：只改 `HeckeSkeleton/Descent.lean`，可以加 import，并填这 4 个 sorry。
- **不要改的东西**：骨架的其他文件、`HeckeGeneral/`、`HeckeAxiom/`、`HeckePort/`（另一个代理正在那里工作）、`DedekindZetaZeroFree/`、`vendor/`、`lakefile.toml`、`lake-manifest.json`。
- **不要碰论文**：项目根目录的 `weil_seven_eighths_revised.tex` 是作者未公开的稿子。
- **不要提交**：改动留在工作区，由用户提交。
- **禁止的写法**：不用 `sorry`、`axiom`、`native_decide`、`implemented_by`、`opaque`。

## 环境与构建

- **系统与工具链**：Windows 11，项目根目录 `C:\Users\Boyang\Desktop\Math\Hecke L 435`（路径带空格，要加引号）。Lean 4.35.0-rc3，Lake。所有依赖都已编译好，包括 Mathlib、Axiom 上游、HeckeGeneral，以及 vendored 类域论包的全部 1,658 个模块。
- **构建范围**：只构建单个模块，例如 `LEAN_NUM_THREADS=4 lake build HeckeSkeleton.Descent HeckeSkeleton.Descent.ArtinFactors`。不要跑全量的 `lake build HeckeAxiom HeckeSkeleton SkeletonInputs`，也不要 `lake clean` 或 `lake update`。
- **内存**：每个 lean 进程约 3.3 GB，同一台机器上还有别的代理在编译。偶尔会报 "failed to read file …olean"，重跑即可。
- **只做类型检查时**：用 `lake env lean <文件>`，它不写 `.lake`。
- **可以忽略的警告**："imports … designed for use with the module system" 是项目里的普遍现象。
- **4.35 工具链的细节**：
  - `dif_pos`/`dif_neg`/`if_pos`/`if_neg` 已弃用，分别改用 `dite_eq_left`/`dite_eq_right`/`ite_eq_left`/`ite_eq_right`；
  - `omit … in` 和 `include … in` 要写在 docstring 前面；
  - HeckeGeneral 里很多引理把 K、S 等作为显式参数，不能用点记号调用。

## 可用的材料

**项目里已编译的部分**

- `HeckeGeneral/Characters/HeckeCharacter.lean`：`HeckeCharacter`。
- `HeckeGeneral/Analysis/HeckeContinuation.lean`：`heckeContinuation`、`meromorphicOn_heckeContinuation`。
- `HeckeGeneral/Analysis/HeckeEulerProduct.lean`：`hasProd_heckeLSeries`，即 Re s > 1 时局部 Euler 因子的 `HasProd`。
- `HeckeGeneral/Analysis/HeckeSeries.lean`：`heckeLocalEulerFactor_ne_zero`。
- `HeckeGeneral/Analysis/HeckeEulerDeletion.lean`：删除多项式在 Re s > 0 非零，并保持零点阶。
- `HeckeGeneral/Analysis/HeckeNormPole.lean`：`heckeContinuation_pole_iff`、`meromorphicOrderAt_heckeContinuation_normTwist`。只有范数幂型的特征才有极点。
- `HeckeGeneral/Characters/FiniteCircleDual.lean`、`FiniteCircleFourier`：有限对偶、分离性、正交性。
- `HeckeSkeleton/ActualHeckeNormPullback.lean`：`normPullback` 所用的范数与拉回。

**vendored 类域论包**（`vendor/class-field-theory/Lean4/ClassFieldTheory/`，已编译）

- `GlobalClassFieldTheory/Reciprocity/TopologicalGlobalNormResidue.lean`：
  - `globalNormResidueContinuousMulEquiv`：C_F / N(C_K) ≃ₜ* Gal(K/F)；
  - `ideleClassNormQuotient_discreteTopology`；
  - `ideleClassNormQuotientContinuousMonoidHom`。
- `GlobalClassFieldTheory/GlobalClassFields/NormConductor.lean`：`ideleClassNorm_range_isOpen`，以及范数像的 `FiniteIndex`。
- `GlobalClassFieldTheory/GlobalClassFields/UnramifiedPrimeArtin.lean`：未分歧素位的 Artin 元，其阶等于局部次数。
- `AlgebraicNumberTheory/Idele/Extension/OnePlaceBaseNorm.lean`：支撑在单个素位上的 idele 的范数就是完备化域的范数。
- `AlgebraicNumberTheory/Idele/Extension/NormLocalOrder.lean`：范数的局部阶与惯性次数的关系。

**未编译的候选代码**（2026-10-11 写成，约 2,200 行，在旧仓库缓存中）

这些目录只读：可以把有用的部分复制到本项目再改，不要在原处编辑或运行脚本。

- `C:\Users\Boyang\Desktop\Math\Hecke L\.cache\hecke-artin-factors-20261011\`
  - `ActualHeckeArtinFactors.lean`：有限因子族。构造是 Q = C_F / N(C_K)，取全对偶 Q →* Circle，得到 Artin Hecke 特征；证明了单射性，以及因子个数等于 [K:F]。这基本就是 `artinCharacters` 和 `one_mem_artinCharacters`。
  - `ActualHeckeArtinLocalEuler.lean`、`ActualHeckeArtinPrimeAssembly.lean`、`ActualHeckeDeletedEulerProduct.lean`、`ActualHeckeArtinFactorization.lean`、`FiniteCircleEulerProductCandidate.lean`：Euler 乘积的组装。
  - `README.md` 和各个 `*STATIC-REVIEW*.md`：静态审查记录，以及还缺哪些连接。
- `C:\Users\Boyang\Desktop\Math\Hecke L\.cache\hecke-artin-frobenius-20261011\`：`ActualHeckeArtinFrobenius.lean`、`ActualHeckeArtinPrimeArithmetic.lean`。
- `C:\Users\Boyang\Desktop\Math\Hecke L\.cache\hecke-local-norm-20261011\`：`ActualHeckeLocalNorm.lean`、`ActualHeckeLocalNormCoefficients.lean`。
- `C:\Users\Boyang\Desktop\Math\Hecke L\.cache\hecke-norm-pullback-20261011\`：`ActualHeckeNormPullbackPoleMatching.lean`（附 `POLE-MATCHING-REVIEW.md`）、`ActualHeckeNormPullbackTwist.lean`。

这些候选是按旧仓库的路径（`formal/HeckeGeneral/...`）和 `...Draft` 命名空间写的，从没编译过，API 对不上是意料中的事。

## 数学路线

1. **`artinCharacters`**：取 F 上在 N_{K/F}(C_K) 上平凡的 Hecke 特征，也就是 C_F / N(C_K) ≅ Gal(K/F) 的有限对偶，照候选 `ActualHeckeArtinFactors.lean` 的构造做。由此 `one_mem` 直接成立。
2. **`artinEulerProduct` 在未分歧素位处**：候选 README 列出了还缺的三步：
   - 把项目里局部 uniformizer 上的特征值（`localComponent`/`localUniformizerUnit`）和类域论包的 `IdeleGroup.finitePlaceIdeleClass`、单点范数对齐，得到 `primeCoefficient K (χ∘N) W = primeCoefficient F χ v ^ f(W/v)`；
   - 把 `artinHeckeCharacter ρ` 在 uniformizer 上的值和素 Artin 元（Frobenius）对齐；
   - 证明有限对偶上的局部多项式恒等式 ∏_ρ (1 − ρ(g) X) = (1 − X^{ord g})^{|Q|/ord g}。
   然后沿每个 F 的素位上方的有限纤维重排上层 Euler 乘积，再交换有限乘积与 Euler 乘积。
3. **分歧素位处**：位于 2、3 上方的素位以及 χ 的导子处。陈述是精确等式，所以这里需要局部恒等式 ∏_{w|v} L_w(s, χ∘N) = ∏_δ L_v(s, χδ)。骨架的注释允许"matching deletions"：两边去掉同一组有限多个素位后先证等式，再逐个对上被删掉的因子。这一步若超出现有 API，按上面说的停下来报告。
4. **`poleMatching`**：极点只来自范数幂型的特征（`heckeContinuation_pole_iff`）。`factors F χ` 中两两不同的特征在同一点不会同时有极点；若某个因子有极点，上层 L 函数在该点也有单极点。参考候选 `ActualHeckeNormPullbackPoleMatching.lean`。

## 规模预估

全部做完估计 0.5–1.5 万行，候选代码提供约 2,200 行起点。如果中途发现某一项明显要动骨架的陈述或别的库，先停下来报告，不要自行扩大范围。
