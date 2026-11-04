# 任务：为 Hecke 7/8 主定理写 Solution，接上 comparator

分支 `challenge/hecke-seven-eighths`，PR #49（draft，目标 `dtests-handoff`）。所有编译都交给 PR 的整仓 CI，不要在本地编译整个项目。

## 背景

`src/Challenge/HeckeSevenEighthsChallenge.lean` 只用 Mathlib 的概念写出论文定理 1.2（Hecke 解析核心）。它在文件里定义了 `HeckeSevenEighths.HeckeCharacter`、`IsUnramifiedAt`、`primeValue`、`coeff`，并陈述了 `HeckeSevenEighths.heckeL_zeroFree`，证明处写的是 `sorry`。

库里已经证明的终点是 `HeckeSkeleton.generalHeckeSevenEighths_skeleton : GeneralHeckeSevenEighths`，见 `src/HeckeGeneral/Analysis/HeckeEndpointTarget.lean`。它说的是 `MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (7 / 8))`。另外有这些现成的结论：
- `src/HeckeGeneral/Analysis/HeckeContinuation.lean`：`meromorphicOn_heckeContinuation`、`heckeContinuation_eq_series`、`differentiable_heckeContinuation_of_nonNorm`、`heckeContinuation_normBranch`。范数分支的极点是 `heckeNormPole t = 1 + t·i`。
- `src/HeckeGeneral/Analysis/HeckeSeries.lean`：`hasSum_heckeLSeries`。
- `src/HeckeGeneral/Characters/PrimeCoefficients.lean`：`primeCoefficient`，取法是"非分歧时取 `localUniformizerUnit` 上的值，否则为 0"。

## 要做的事

1. 新建 `src/Solution/HeckeSevenEighthsSolution.lean`，并在 `lakefile.toml` 登记库 `HeckeSevenEighthsSolution`（`srcDir = "src/Solution"`）。这个文件**不导入 Challenge**。它要逐字照抄 Challenge 里的四个定义（命名空间、名字、正文都完全相同），然后证明同一个 `HeckeSevenEighths.heckeL_zeroFree`。写法照 `base/Solution/DedekindZetaSolution.lean`。
2. 证明分两步：
   - **系数桥接**：对非零理想 `I`，证明 Challenge 的 `coeff χ I` 等于库里的 `heckeIdealCoefficient K χ`（`I = ⊥` 时两边都按零处理）。要点有三个：Challenge 的 `IsUnramifiedAt` 与库的 `UnramifiedAt` 等价；非分歧时，`χ` 在任意两个均匀化元上取值相同；`normalizedFactors` 上的乘积等于库的 `nonzeroIdealCoefficient`。由此推出，Challenge 的级数和 `heckeLSeries` 有相同的和。
   - **解析部分**：取 `f = heckeContinuation K χ`。非范数分支取 `P = ∅`。范数分支有两种情况：如果 `1 + t·i` 处真有极点（阶 < 0），取 `P = {1 + t·i}`，并从 `Q / (s - p)` 读出 `g = Q`、`Q p ≠ 0`；如果阶为 0，就把 `f` 在该点改成连续延拓值，取 `P = ∅`。无零点由 `MeromorphicZeroFreeOn` 加上 `MeromorphicZeroFreeOn.ne_zero` 得到。
3. 新建 `src/Challenge/comparator.json`，内容如下：
   ```json
   {"challenge_module": "HeckeSevenEighthsChallenge", "solution_module": "HeckeSevenEighthsSolution",
    "theorem_names": ["HeckeSevenEighths.heckeL_zeroFree"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
   ```
4. 在 `.github/workflows/integration-build.yml` 的公理打印里加上 `#print axioms HeckeSevenEighths.heckeL_zeroFree`（导入 Solution 模块）。

## 规矩

- **不许改 Challenge 的陈述。** 如果发现陈述有缺陷（证不出来，或者比论文弱或强），在 PR #49 上写清楚原因，由协调员决定。
- Solution 里只能有一个 `theorem heckeL_zeroFree`，桥接引理放进 `src/HeckeGeneral/` 里新建的文件。不要有 `sorry`、`axiom` 或 `native_decide`。
- 完成标准：
  - 整仓 CI 绿；
  - `HeckeSevenEighths.heckeL_zeroFree` 的公理只有三条标准公理；
  - Solution 里四个定义与 Challenge 逐字相同（提交前用 diff 核对）；
  - 在 PR #49 报告。
