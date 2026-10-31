# MOM_BASE：共享底座：有限系数与背景

估计约 1.7 万行。先读 [MOMENTS_README.md](MOMENTS_README.md)（并行规则）和 [README.md](README.md)（通用规矩）。

## 论文

论文 §4.2（第 1690–1909 行），包括引理 4.3（canonical-theta-bridge，规范系数与立方补全）和引理 4.4（paired-phase-invariant，配对整积相位的保持）；另含 §4.1 的矩陈述（第 1561–1690 行）中用到的有限背景。

## 目标

- 把 `HeckePort/Moments/` 里以显式假设出现的 ℤ[ω] 专用输入，换成对实际 `ThetaArithmeticData` / `TargetContext` 的证明；
- 证明引理 4.3、4.4，供逆归纳与四阶矩归纳共用。
- 本任务不对应单独的 `OBLIGATION`，交付的是供其他任务 import 的定理；陈述以论文为准。

## 交付

- 分支 `cloud/mom-base`，PR 到 `dtests-handoff`。
- 新代码放在 `HeckeSkeleton/Moments/MOM_BASE/` 下。只在最后把自己负责的 `sorry` 换成调用。
- 完成标准：目标定理编译通过，`#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`。
- CI 的编译记录和日志放在 Actions artifact 里，不要提交进仓库。
