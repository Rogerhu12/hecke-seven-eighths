# MOM_UNIFORM_AMPLIFY：一致性与六次方放大

估计约 2.5 万行。先读 [MOMENTS_README.md](MOMENTS_README.md)（并行规则）和 [README.md](README.md)（通用规矩）。

## 论文

论文 §4.9（第 3041–3204 行：引理 4.12 polylog-propagation、命题 4.14 can-uniformity）和第 5 章（第 3204–3273 行：引理 5.1 amplification，式 (5.2)–(5.4)），以及 §7.1 的有限扇区重排。

## 目标

- 证明 `HeckeSkeleton/Moments.lean` 中的 `MI-M-PROFILE-UNIFORMITY`、`MI-M-FIBER-ELIGIBILITY`、`MI-M-FINITE-SECTOR-REINDEX`、`MI-I-SIXTH-POWER-ZEROS`、`MI-I-INDEPENDENT-AMPLIFICATION`、`MI-I-AMPLIFIED-WITNESS-CALIBRATION`。
- `WholeMomentProfileControl` 未覆盖素数窗口的问题（见 MOMENTS_README 并行规则 4）由本任务负责修正。

## 交付

- 分支 `cloud/mom-uniform-amplify`，PR 到 `dtests-handoff`。
- 新代码放在 `HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/` 下。只在最后把自己负责的 `sorry` 换成调用。
- 完成标准：目标定理编译通过，`#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`。
- CI 的编译记录和日志放在 Actions artifact 里，不要提交进仓库。
