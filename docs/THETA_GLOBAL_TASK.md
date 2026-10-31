# 任务：theta 反射的全局部分（约 2 万行）

## 目标

`project/HeckeSkeleton/Theta.lean` 中以下义务：

| 义务 | 定义或定理 |
|---|---|
| TH-KP-DATA | `finiteMellinData`，目前是 `sorry` 数据：实际旋转后的 KP 系数表 |
| TH-FINITE-VALUATION-CUTOFF | `finite_valuation_cutoff` |
| TH-FINITE-VALUATION-DECAY | `finite_valuation_decay` |
| TH-MARKED-REFLECTED-ABSOLUTE | `marked_reflected_absolute` |
| TH-MARKED-REFLECTION | `marked_reflection`，固定型带标记的 theta 反射，即论文命题 3.4、引理 3.2、定理 3.5 |

论文位置：第 3 节，约第 600–1210 行。

## 已有的部分

- **核引理已对一般数据证完**：三个 TH-KERNEL 义务在 `HeckeSkeleton/ThetaKernel*.lean`，只要求 `FiniteMellinAdmissible`，即数据满足截断、衰减和绝对 Mellin 收敛。
- **局部部分另有任务在做**：阿基米德侧的高 K-型向量、Mellin 对、乘子恒等式，以及外部素位的数字表。你可以把这些结论写成显式假设，或者自己证。
- **算术数据来自同一次 Axiom 选择**：`HeckeSkeleton/Base.lean` 的 `axiomChoice`，`HeckeAxiom/ArithmeticChoice.lean` 中的 `A` 和上下文 `C`。Axiom 的 theta 机器（`Theta/Unfolding`、`Whittaker`、`Digits`、`Profiles`，以及 `Moments/Reflected/RankOneExpansion`）只处理主特征、固定 Gaussian、无标记的情形。
- **一个已知需要的事实**：`finiteMellinData` 应当带一个规格，说明系数等于局部壳层积分。全局反射要用到它。

---

## 环境与交付

- **材料**（都在本压缩包里）：
  - `project/`：项目源码原文。包括 HeckeSkeleton（顶层骨架，剩余的 `sorry` 都标有 `-- OBLIGATION <ID>`）、HeckeGeneral、HeckeAxiom，以及与本任务相关的上游 Axiom 库（DedekindZetaZeroFree）目录。
  - `openai_reference/`：openai/math 中对应结论在 ℚ(ω) 上的完整形式化，可参考。
  - `prior_deliverables/`：之前几轮的云端交付，若与本任务有关。
  - `paper/weil_seven_eighths_revised.tex`：论文全文。
- **目标环境**：Lean 4.35.0-rc3，Mathlib 0493595ecd5da8ef14742febab99728f98e948e8。你拿不到这个项目已经编译好的依赖；可以只依赖 Mathlib 写自包含的模块，也可以写直接引用项目定义的模块。两种都可以，但要在报告里分清哪些编译过、哪些没有。
- **交付物**：
  1. 全部 `.lean` 文件；
  2. 一份报告，包括：
     - 每个主定理的确切陈述和全部假设；
     - 与上面列出的项目目标之间还缺什么；
     - 编译情况与公理清单；
     - 发现的项目定义或陈述错误。
- **要求**：
  - 不用 `sorry`、`axiom`、`native_decide`。确实证不了的地方，写成独立的命名引理，并在报告中说明。
  - 不要把要证的结论当作假设。
  - 如果项目里的某个陈述本身是错的，或者缺了必要的假设，请指出，并给出修正后的陈述。之前几轮你已经这样找出过两处问题。
