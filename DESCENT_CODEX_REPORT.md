# Descent Codex report

日期：2026-10-30（Asia/Taipei）。工作区：`C:\Users\Boyang\Desktop\Math\Hecke L 435`。
起始 Git 分支：`dtests-handoff`；起始 HEAD：`4099803226a21debfb84f2eb8261f308ae5b0b8b`。

## 结果与停止边界

本任务尚未全部完成。按 `CODEX_TASK_DESCENT.md` 关于分歧素位和保持陈述的约束，
停在 **DE-EULER-FACTORIZATION 的完整、未删除 Euler 因子匹配**。
未发现该数学陈述的反例，也没有证明它为假；当前核查的候选和 API 尚未补出它。

| 义务 | 本次结果 |
|---|---|
| DE-ARTIN-CHARACTERS | 已关闭，使用真实范数商的完整有限对偶 |
| DE-TRIVIAL-FACTOR | 已关闭，平凡对偶给出平凡 Hecke 特征 |
| DE-POLE-MATCHING | 已关闭，使用实际范数拉回相容性及 common fiber |
| DE-EULER-FACTORIZATION | 未关闭，原声明与原 `sorry` 保留 |

保留原来的四个声明及 `HeckeFactorizationDescentData` 的陈述。
没有把删因子等式替换为完整等式，没有增加公理或把缺口移成一个新的假设。
最终接入及检查结果见下文。

## 已复用的候选

- `hecke-artin-factors-20261011/ActualHeckeArtinFactors.lean`：实际范数商
  `C_F / N(C_K)`、全有限 Circle 对偶、连续 Hecke 特征、平凡成员、单射性、
  common norm-pullback fiber 和与扩张次数相等的基数。
- `hecke-norm-pullback-20261011/ActualHeckeNormPullbackTwist.lean`：
  Mathlib 模与 vendored absoluteNorm 的倒数比较、真正相对范数的模相容性、
  同一个实参数的范数扭曲拉回。
- 同目录 `ActualHeckeNormPullbackPoleMatching.lean`：显式解析分支的非解析点分类、
  极点位置参数的单射性、同一范数拉回纤维内的唯一极点匹配。

以上原缓存只读。本次新文件改用本项目 import 路径与 `HeckeSkeleton.Descent`
下的命名空间；本次编译状态与原缓存的 UNCOMPILED 状态分别记录。

## 完整 Euler 等式的具体缺口

旧缓存根目录：`C:\Users\Boyang\Desktop\Math\Hecke L\.cache\`。

1. `hecke-artin-factors-20261011/ActualHeckeArtinFactorization.lean:60-79`
   的 `good_prime_artin_euler_identity` 同时要求 χ 在 v 未分歧和 K/F 在 v 未分歧。
   `:83-92` 的 `actual_deleted_artin_identity` 只给出删去坏素位的等式。
   `:96-102` 的 full zero-free descent 调用另一个 deleted consumer；
   它不是当前 `Descent.artinEulerProduct` 所要求的完整函数等式。
2. 当前 `HeckeGeneral/Characters/PrimeCoefficients.lean:23-34` 的定义正确地
   把局部分歧特征的 Euler 系数置为零。可是 χ 分歧不能推出所有 χδ 分歧：
   取 χ = δ⁻¹ 时，χδ = 1。因此不能把两边删去的 Euler 因子一律视为 1。
3. 当前 `HeckeGeneral/Analysis/HeckeEulerDeletion.lean:51-53` 定义
   `L^S = E_S · L`。其中 `:39-47`、`:63-78` 的非零性与阶保持只能说明
   删除不改变零极点阶，不能说明两边的删除多项式相等。
   从 `E_K L_K = (∏ψ E_F,ψ)(∏ψ L_F,ψ)` 恢复精确的
   `L_K = ∏ψ L_F,ψ` 还需要匹配 `E_K = ∏ψ E_F,ψ`。
4. vendored `AlgebraicNumberTheory/Idele/Extension/NormLocalOrder.lean:292-304`
   提供实际范数赋值 `ord(Nx) = f · ord(x)`；
   `GlobalClassFieldTheory/GlobalClassFields/UnramifiedPrimeArtin.lean:191-200`
   的 prime Artin 阶公式仍要求 `ChosenFinitePlaceIsUnramified`。
   `GlobalClassFieldTheory/Reciprocity/LocalGlobalArtinCompatibility/Factorization.lean:775-779`
   提供局部与全局 Artin 相容性，但这些结果本身不是分歧处的 Euler 乘积公式。

决定性缺失引理是下式，**不能附加 χ 或 K/F 未分歧的假设**：

```text
∏_{w|v} L_w(s, χ ∘ N) = ∏_ρ L_v(s, χ · δρ).
```

具体来说，令 `q_v : F_vˣ → C_F/N(C_K)` 为实际局部商映射，`U_v` 为局部整数单位群。
右边有贡献的 ρ 应满足对所有 `u ∈ U_v`，
`ρ(q_v(u)) = χ_v(u)⁻¹`。这些指标构成惯性像 `q_v(U_v)` 的消灭子的陪集，或者为空。
还需要把筛选后的有限对偶乘积与上层范数 Euler 因子对齐，并证明相应的惯性次数
和上方素位重数公式。这里不只是把未分歧公式中一个假设删掉。

本次核查覆盖任务列出的缓存链、当前局部系数和删除定义，以及 vendored 的
全局/局部互反律、范数赋值、惯性相关模块；没有穷尽全库逐定理证明不存在可用引理。
未移植未分歧候选链，也不把其约两千行的静态代码报告为已编译证明。

## 新增文件与候选适配

| 文件 | 行数 | 内容 |
|---|---:|---|
| `HeckeSkeleton/Descent/ArtinFactors.lean` | 169 | 真正范数商的全有限对偶、因子族及其性质 |
| `HeckeSkeleton/Descent/PoleMatching.lean` | 262 | 范数模比较、范数扭曲相容性及极点匹配 |

新增证明源文件共 431 行。主文件通过上述模块填入原有三个证明体；
完整 Euler 等式保留原来的唯一 `sorry`。

候选适配包括：`finiteOrder_iff_pointwise` 的显式字符参数、
新增 finset 陈述所需的 Classical 作用域、`WithZero.log` 简化 API，
以及单位/NNReal 逆元的强制转换。未改变数学对象或加入未证明的相容性假设。

两个辅助模块均已单独构建成功：

```text
lake build HeckeSkeleton.Descent.ArtinFactors
Built HeckeSkeleton.Descent.ArtinFactors (118s)
Build completed successfully (10234 jobs).
exit = 0

lake build HeckeSkeleton.Descent.PoleMatching
Built HeckeSkeleton.Descent.PoleMatching (96s)
Build completed successfully (9874 jobs).
exit = 0
```

所有构建均设置 `LEAN_NUM_THREADS=4`。jobs 是单目标依赖图中的动作计数，
日志中的依赖绝大多数为 `Replayed`，没有请求全量库构建。

## 三项最终检查

### 1. 主文件单模块构建

```powershell
$env:LEAN_NUM_THREADS = '4'
lake build HeckeSkeleton.Descent
```

最终输出：

```text
Built HeckeSkeleton.Descent.PoleMatching (95s)
Built HeckeSkeleton.Descent (105s)
warning: HeckeSkeleton/Descent.lean:55:8: declaration uses `sorry`
Build completed successfully (10269 jobs).
DESCENT_BUILD_EXIT=0
```

构建通过，但完成标准 1 的「不再有 sorry」尚未达到。
唯一此类警告对应保留的 `artinEulerProduct`。

### 2. 递归公理检查

临时文件 `HeckeSkeleton/Descent/CheckAxioms.lean` 导入主模块，打印公理，
并用 `Lean.collectAxioms` 对八个已完成声明逐个检查：出现标准三公理以外的依赖就报错。
临时文件在检查结束后删除。

```powershell
$env:LEAN_NUM_THREADS = '4'
lake env lean HeckeSkeleton/Descent/CheckAxioms.lean
```

关键原始输出：

```text
'HeckeSkeleton.Descent.artinCharacters' depends on axioms: [propext, Classical.choice, Quot.sound]
'HeckeSkeleton.Descent.one_mem_artinCharacters' depends on axioms: [propext, Classical.choice, Quot.sound]
'HeckeSkeleton.Descent.Artin.card_artinFactors' depends on axioms: [propext, Classical.choice, Quot.sound]
'HeckeSkeleton.Descent.poleMatching' depends on axioms: [propext, Classical.choice, Quot.sound]
'HeckeSkeleton.Descent.continuedFactorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'HeckeSkeleton.Descent.descend' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
DESCENT_AXIOM_CHECK_EXIT=0
```

八项守卫检查都通过，公理集均恰为 `propext, Classical.choice, Quot.sound`：

- `HeckeSkeleton.Descent.artinCharacters`
- `HeckeSkeleton.Descent.one_mem_artinCharacters`
- `HeckeSkeleton.Descent.Artin.artinFactors_common_normPullback`
- `HeckeSkeleton.Descent.Artin.card_artinFactors`
- `HeckeSkeleton.Descent.PoleMatching.heckeNormPullback_normTwist`
- `HeckeSkeleton.Descent.PoleMatching.pole_matching_of_common_normPullback`
- `HeckeSkeleton.Descent.poleMatching`
- `HeckeSkeleton.Descent.continuedFactorization`

**完成标准 2 尚未达到**：最终 `descend` 仍依赖 `sorryAx`；
不能把上述八项已证明声明的干净公理集算成 `descend` 已经证明。

### 3. Audit 计数

按任务要求只构建 `HeckeSkeleton.Audit`，并用 PowerShell 做与给定 grep/sort/wc
相同的去重计数：

```powershell
$env:LEAN_NUM_THREADS = '4'
lake build HeckeSkeleton.Audit *> HeckeSkeleton/Descent/AuditBuild.log
$admissions = @(Select-String -LiteralPath HeckeSkeleton/Descent/AuditBuild.log `
  -Pattern 'SKELETON_DECL\|[^|]*\|[^|]*\|true' -AllMatches |
  ForEach-Object { $_.Matches.Value } | Sort-Object -Unique)
$admissions.Count
```

最终输出：

```text
SKELETON_DIRECT_ADMISSIONS_COUNT=55
SKELETON_DECL|HeckeSkeleton.Descent.artinEulerProduct|HeckeSkeleton.Descent|true
SKELETON_ENDPOINT_AXIOMS|propext,sorryAx,Classical.choice,Quot.sound
SKELETON_GRAPH_VISITED|2433
Build completed successfully (12176 jobs).
DESCENT_AUDIT_BUILD_EXIT=0
```

本次 Audit 中属于 `HeckeSkeleton.Descent` 的 direct admission 只有上面这一项。

**基线差异不能算成本次的额外成果。** 任务说明给出的基线是 60，
但本次开始时 `Base.lean`、`Principal.lean` 已有其他工作的未提交改动，
其中包括替换原有 sorry 的证明。本次没有修改它们，也没有在修改 Descent 前重跑 Audit。
因此不能把说明中的 `60 → 55` 全部归于本次；本次可直接核对的成果是
Descent 的四项中关闭三项、保留一项。当前总计数虽小于说明中的目标 56，
仍不能据此判定本任务四项全部完成。

最后静态检查确认：两个新增证明文件均没有 `sorry`、`admit`、`axiom`、
`native_decide`、`implemented_by` 或 `opaque`；主文件唯一 `sorry` 在第 59 行。
`git diff --check -- HeckeSkeleton/Descent.lean` 通过。
临时检查源文件及冗长构建日志在记录上述结果后删除；最终保留两个辅助证明文件和本报告。

## 工作区边界

已有源文件只修改 `HeckeSkeleton/Descent.lean`，新增 Lean 代码只放在
`HeckeSkeleton/Descent/` 下；本报告按任务要求放在根目录。
没有修改 `HeckePort/`、`HeckeGeneral/`、`HeckeAxiom/`、`vendor/`、Lake 配置或论文，
没有运行全量构建、`lake clean`、`lake update`，也没有提交。
开始时工作区已有其他修改和未跟踪文件，未还原或纳入本任务。
