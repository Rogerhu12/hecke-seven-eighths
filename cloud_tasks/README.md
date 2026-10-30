# 云端任务

**仓库**：`Rogerhu12/hecke-seven-eighths`，分支 `dtests-handoff`。论文是根目录下的 `weil_seven_eighths_revised.tex`。顶层骨架在 `HeckeSkeleton/`，其中尚未完成的部分都标有 `-- OBLIGATION <ID>`。

**参考**：openai/math（https://github.com/openai/math ，路径 `lean/OAI/NumberTheory/DirichletL/`）。

**环境**：Lean 4.35.0-rc3，Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。

**规矩**
1. 每个任务在自己的新分支上做，用 PR 交付到 `dtests-handoff`；不要直接推送 `dtests-handoff`。
2. 一个 PR 只做一个任务。
3. 不要改动已有的证明和定义。发现陈述有错或缺少必要的假设，就在 PR 说明里指出，并给出修正后的陈述。
4. 不要用 `sorry`、`axiom`、`native_decide`。
5. PR 说明写清楚四件事：
   - 主定理的陈述与假设；
   - 还差什么；
   - 编译了哪些模块、在什么环境下编译；
   - 公理清单。
