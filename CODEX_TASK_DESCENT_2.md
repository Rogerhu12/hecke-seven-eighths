# 独立任务（第二阶段）：删除坏素位后的 Artin Euler 恒等式

接 [CODEX_TASK_DESCENT.md](CODEX_TASK_DESCENT.md) 和 [DESCENT_CODEX_REPORT.md](DESCENT_CODEX_REPORT.md)。第一阶段关闭了 DE-ARTIN-CHARACTERS、DE-TRIVIAL-FACTOR 和 DE-POLE-MATCHING。剩下的 `artinEulerProduct`（DE-EULER-FACTORIZATION）卡在分歧素位处精确的局部因子匹配。

本阶段**不碰分歧素位**，只做删除坏素位以后的恒等式。下降接口已经放宽成"差一个有限 Euler 因子"：`HeckeSkeleton/Descent.lean` 中原来的 `artinEulerProduct` 已换成存在形式的 `deletedEulerFactorization`（仍是 sorry），`descend` 已由它推出。所以证完本阶段，DE 这一项就关了。

## 目标

在新模块 `HeckeSkeleton/Descent/DeletedEuler.lean` 中证明下面形式的定理。坏素位集合的具体定义由你选，但必须满足下述要求，并在报告中写清楚：

```lean
/-- F 的有限坏素位：χ 在此分歧，或 K/F 在此分歧（包括 2、3 上方的素位）。 -/
def badPlaces (χ : HeckeCharacter F) : Finset (HeightOneSpectrum (𝓞 F)) := ...

/-- K = Extension F 中位于 badPlaces χ 上方的素位。 -/
def badPlacesUp (χ : HeckeCharacter F) :
    Finset (HeightOneSpectrum (𝓞 (Extension F))) := ...

theorem artinDeletedEulerProduct (χ : HeckeCharacter F) :
    ∀ s : ℂ, 1 < s.re →
      heckeDeletedContinuation (Extension F) (normPullback F χ) (badPlacesUp F χ) s =
        ∏ ψ ∈ factors F χ, heckeDeletedContinuation F ψ (badPlaces F χ) s
```

这里 `heckeDeletedContinuation K χ S = heckeEulerDeletionPolynomial K χ S * heckeContinuation K χ`，定义在 `HeckeGeneral/Analysis/HeckeEulerDeletion.lean`。

对坏素位集合的要求：

- 它是有限集；
- 包含 χ 的全部分歧素位，以及 K/F 的全部分歧素位；
- 上层集合恰为下层集合上方的全部素位。

这样，在其余素位上，χ、每个 ψ = χδ 以及 χ∘N 都是未分歧的，只需要未分歧的 Euler 恒等式。

## 路线

缓存 `C:\Users\Boyang\Desktop\Math\Hecke L\.cache\hecke-artin-factors-20261011\` 中的未分歧链（约 2,000 行，未编译）基本就是这条路线：

- `ActualHeckeArtinLocalEuler.lean`
- `ActualHeckeArtinPrimeAssembly.lean`
- `ActualHeckeDeletedEulerProduct.lean`
- `ActualHeckeArtinFactorization.lean`：其中的 `good_prime_artin_euler_identity`、`actual_deleted_artin_identity`
- `hecke-artin-frobenius-20261011` 和 `hecke-local-norm-20261011` 里的 Frobenius 与局部范数文件

该目录 `README.md` 末节列出了缺的三处连接：

1. 项目的局部 uniformizer 特征值，与类域论包的单点 idele 范数对齐：`primeCoefficient K (χ∘N) W = primeCoefficient F χ v ^ f(W/v)`；
2. Artin 特征在 uniformizer 上的值，与素 Artin 元（Frobenius）对齐（`UnramifiedPrimeArtin.lean`）；
3. 有限对偶上的局部多项式恒等式 ∏_ρ (1 − ρ(g) X) = (1 − X^{ord g})^{|Q|/ord g}。

第一阶段新增的 `HeckeSkeleton/Descent/ArtinFactors.lean` 已有因子族、单射性和基数等于 [K:F]，直接沿用。

## 接入骨架

证完以后，在 `HeckeSkeleton/Descent.lean` 中 import 新模块，并把 `deletedEulerFactorization` 的 sorry 换成

```lean
  exact ⟨badPlaces F χ, badPlacesUp F χ, artinDeletedEulerProduct F χ⟩
```

（按你实际的名字与命名空间调整）。这是本阶段对 `Descent.lean` 唯一允许的改动。不要改 `deletedEulerFactorization` 的陈述。

## 完成标准

1. `LEAN_NUM_THREADS=4 lake build HeckeSkeleton.Descent` 通过，`Descent.lean` 和新文件里都没有 sorry。
2. 用 `lake env lean` 对 `HeckeSkeleton.Descent.descend` 做 `#print axioms`，结果只有 `propext, Classical.choice, Quot.sound`。
3. 在项目根目录写 `DESCENT_CODEX_REPORT_2.md`：新增文件与行数、复用了哪些候选、坏素位集合的定义、两项检查的输出。

## 约束

与第一阶段相同。特别是：

- **只新增 `HeckeSkeleton/Descent/` 下的文件。** 对 `HeckeSkeleton/Descent.lean` 只做上面"接入骨架"那一处改动。
- **不改其他目录。** 不改 `HeckeGeneral/`、`vendor/`、`lakefile.toml`、其他骨架文件，以及 `GramCoreInputs/`、`HeckeSkeleton/Gram*.lean`（另一个代理正在那里工作）。
- **只做单模块构建。** 不跑全量构建，不 `lake clean`，不提交。
- **报告卡点。** 如果发现删除型恒等式也需要分歧素位的信息（例如 Artin 特征在 K/F 未分歧的素位处不能证明是未分歧的），停下来写清楚。
