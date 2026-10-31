# MOM_INV_STEP：规范逆归纳的单步

估计约 3.5 万行。先读 [MOMENTS_README.md](MOMENTS_README.md)（并行规则）和 [README.md](README.md)（通用规矩）。

## 论文

论文 §4.5（第 2341–2614 行）命题 4.10（prop:can-canonical）证明中的一步递推：两次真 Poisson 变换，子掩码、标签与固定三元组纤维，以及一步的能量不等式。

## 目标

- 在 `HeckeSkeleton/Moments/MOM_INV_STEP/Interface.lean` 写出单步结论的陈述（见并行规则 3），然后证明它。
- 骨架中对应 `canonical_inverse_models`（MI-I-CANONICAL-RECURSION）注释里的前两项。

## 交付

- 分支 `cloud/mom-inv-step`，PR 到 `dtests-handoff`。
- 新代码放在 `HeckeSkeleton/Moments/MOM_INV_STEP/` 下。只在最后把自己负责的 `sorry` 换成调用。
- 完成标准：目标定理编译通过，`#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`。
- CI 的编译记录和日志放在 Actions artifact 里，不要提交进仓库。
