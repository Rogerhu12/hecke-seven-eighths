# MOM_ENGINE_STEP：四阶矩归纳的单步

估计约 4 万行。先读 [MOMENTS_README.md](MOMENTS_README.md)（并行规则）和 [README.md](README.md)（通用规矩）。

## 论文

论文 §4.8（第 2748–3041 行）中配对四阶矩递推的一步：完整的中心化系数、完整的非本原相关、放大器池与赋值 1/6/7、子支撑与容量账本。

## 目标

- 在 `HeckeSkeleton/Moments/MOM_ENGINE_STEP/Interface.lean` 写出单步结论的陈述，然后证明它。
- 这一步对所有槽（零槽、正槽）通用，不要按槽拆开证明。

## 交付

- 分支 `cloud/mom-engine-step`，PR 到 `dtests-handoff`。
- 新代码放在 `HeckeSkeleton/Moments/MOM_ENGINE_STEP/` 下。只在最后把自己负责的 `sorry` 换成调用。
- 完成标准：目标定理编译通过，`#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`。
- CI 的编译记录和日志放在 Actions artifact 里，不要提交进仓库。
