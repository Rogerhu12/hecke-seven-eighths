# MOM_PRIME_BELOW_ONE：B < 1 时的素数相消

先读 [MOMENTS_README.md](MOMENTS_README.md)（并行规则）和 [README.md](README.md)（通用规矩）。

## 论文

论文 §4.6（第 2614–2685 行），式 (4.38)：B < 1 时，有限阶特征的对数导数与光滑素数 Mellin 估计给出配对素数乘积的相消。

## 目标

证明 `HeckeSkeleton.paired_primes_below_one`（`HeckeSkeleton/Moments.lean`，MI-P-PRIME-CANCELLATION-BELOW-ONE），把它的 `sorry` 换成调用。

## 已有的部分

- `HeckeSkeleton.PrimeCancellationWiring.paired_primes_below_one_of_models`（PR #14 合入）已经对任意满足 `PrimeSlotModelControl M` 的模型 `M` 给出原结论 `PairedPrimeProductBound K c M (2 * c.family.B - 1)`。
- 缺的是对实际的 `momentModels K c` 构造 `PrimeSlotModelControl`：槽数上界、槽系数的逆属于 theta、窗口等于槽的 profile 且支撑在 [1, 2]、窗口的有限 Schwartz 半范数关于 T 多项式增长、导子对数关于 `momentBase` 的控制。
- `momentModels` 现在来自 EXPANSION 的实际配方（`expansionRecipeRaw`、`recipeMomentModels`，经 PR #17 合入）。MOM_PRIME（`HeckeSkeleton/Moments/MOM_PRIME/`）为 κ = 1 端点证过同一实际配方的素数 profile、支撑和统一常数，可以直接复用。
- PR #17 把配对行窗口从 U 放宽到 2U（`rowWidthFor`，U^ρ = 2U），相关引理的新旧陈述见 PR #17 说明。

## 交付

- 分支 `cloud/mom-prime-below-one`，PR 到 `dtests-handoff`。
- 新代码放在 `HeckeSkeleton/Moments/MOM_PRIME_BELOW_ONE/` 下。只在最后把 `paired_primes_below_one` 的 `sorry` 换成调用。
- `PrimeSlotModelControl` 和 `PrimeCancellation*` 文件归本任务。如果某个字段对实际配方不成立（例如支撑区间与 2U 行窗口不匹配），按 README 规则 3 修正结构并修好受影响的证明。
- 完成标准：
  - `paired_primes_below_one` 编译通过，`#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`；
  - 全项目编译门禁（`integration-build.yml`）通过。
- CI 的编译记录和日志放在 Actions artifact 里，不要提交进仓库。
