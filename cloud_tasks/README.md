# 云端任务

**仓库**：`Rogerhu12/hecke-seven-eighths`，分支 `dtests-handoff`。论文是根目录下的 `weil_seven_eighths_revised.tex`。顶层骨架在 `HeckeSkeleton/`，其中尚未完成的部分都标有 `-- OBLIGATION <ID>`。

**参考**：openai/math（https://github.com/openai/math ，路径 `lean/OAI/NumberTheory/DirichletL/`）。

**环境**：Lean 4.35.0-rc3，Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。

**持续工作**：领到任务后要一直做到完成标准全部达到才算结束，即目标定理编译通过、公理检查只含三条标准公理、PR 标为可审查。不要中途停下来汇报阶段性进展，也不要停在"草稿"状态。某一部分被卡住时，把原因记在 PR 里，转去做其他部分，全部能做的都做完才停。

**规矩**
1. 每个任务在自己的新分支上做，用 PR 交付到 `dtests-handoff`；不要直接推送 `dtests-handoff`。
2. 一个 PR 只做一个任务。
3. **可以修改骨架中的定义和陈述**，用来修正缺陷或补上必要的假设，但必须满足以下条件：
   - **最终目标不变**：顶层定理（一般数域 Hecke L 函数在 Re s > 7/8 无零点）的陈述不能动，任何改动都不得削弱最终结论；
   - **可审查**：PR 说明列出新旧陈述对照，并说明修正版为什么仍符合论文原意（给出论文行号）；
   - **共享定义只由一个任务修改**：`WholeMomentProfileControl` 归 MOM_UNIFORM_AMPLIFY。改别的任务负责的共享定义之前，先在对方 PR 里留言；
   - **受影响的证明一起修好**：改了定义，依赖它的已有证明要一并修到编译通过；
   - **不要停在相对版本**：发现缺陷后直接修正并继续往下做，不要只写一个带额外假设的相对定理就停下。
4. 不要用 `sorry`、`axiom`、`native_decide`。
5. PR 说明写清楚四件事：
   - 主定理的陈述与假设；
   - 还差什么；
   - 编译了哪些模块、在什么环境下编译；
   - 公理清单。
