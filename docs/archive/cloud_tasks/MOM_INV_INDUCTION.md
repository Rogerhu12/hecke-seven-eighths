# MOM_INV_INDUCTION：规范逆归纳与定理 4.1

估计约 3.5 万行。先读 [MOMENTS_README.md](MOMENTS_README.md)（并行规则）和 [README.md](README.md)（通用规矩）。

## 论文

论文 §4.5（第 2341–2614 行）命题 4.10 的归纳部分（前因子、严格余量、有限终止），以及由它和终端（引理 4.8、推论 4.9）推出定理 4.1（thm:can-inverse，第 1589 行）。

## 目标

- 证明 `HeckeSkeleton/Moments.lean` 的 `canonical_inverse_models`（MI-I-CANONICAL-RECURSION）。
- 单步结论按并行规则 3 作为假设。引理 4.8（LOW-REFLECTED-ENERGY，PR #3）也作为假设，用 `HeckeSkeleton.completedMarkedEnergy` 的陈述。

## 交付

- 分支 `cloud/mom-inv-induction`，PR 到 `dtests-handoff`。
- 新代码放在 `HeckeSkeleton/Moments/MOM_INV_INDUCTION/` 下。只在最后把自己负责的 `sorry` 换成调用。
- 完成标准：目标定理编译通过，`#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`。
- CI 的编译记录和日志放在 Actions artifact 里，不要提交进仓库。
