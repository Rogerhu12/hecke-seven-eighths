# MOM_PRIME：普通反射、素数因子与例外终端

估计约 2 万行。先读 [MOMENTS_README.md](MOMENTS_README.md)（并行规则）和 [README.md](README.md)（通用规矩）。

## 论文

论文 §4.6（第 2614–2685 行）和 §4.7（第 2685–2748 行），包括引理 4.11（lem:can-exceptional，等积相消）。

## 目标

- 证明 `paired_primes_endpoint`（MI-P-PRIME-ABSOLUTE-ENDPOINT，κ = 1）和引理 4.11。
- `paired_primes_below_one` 不在本任务内。
- 骨架注释提到已有部分迁移：`ActualPrimeGeometryAbsoluteBound`、`ActualPairedSlotRemoval`。

## 交付

- 分支 `cloud/mom-prime`，PR 到 `dtests-handoff`。
- 新代码放在 `HeckeSkeleton/Moments/MOM_PRIME/` 下。只在最后把自己负责的 `sorry` 换成调用。
- 完成标准：目标定理编译通过，`#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`。
- CI 的编译记录和日志放在 Actions artifact 里，不要提交进仓库。
