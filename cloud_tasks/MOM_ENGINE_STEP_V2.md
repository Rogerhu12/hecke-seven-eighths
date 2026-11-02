# MOM_ENGINE_STEP_V2：配对引擎单步的紧凑重写（B 线）

先读 [README.md](README.md)（通用规矩，特别是规矩 3、4、6）。

## 背景

PR #9 的 MOM_ENGINE_STEP 现在有 1009 个模块、约 30 万行，其中 578 个文件还没进 `dtests-handoff`，正由 8 个组按 [MOM_ENGINE_STEP_GROUPS.md](MOM_ENGINE_STEP_GROUPS.md) 逐个修，这是 A 线。作为对照，数学角色相近的 MOM_INV_STEP 只有 274 个模块、5.8 万行。

ENGINE_STEP 大的原因主要是写法，不是数学本身：
- 字面量构造占了 12.8 万行；
- Pool / Direct / FirstBlock / FirstSource 以及它们的 Dual 版本、左右两侧，同一个论证各抄一份；
- Actual / Original / Canonical 三套表示，之间还要互相转换。

B 线用更紧凑的设计重写这部分，和 A 线赛跑。哪条线先达到完成标准就用哪条。

## 目标

在 `dtests-handoff` 之上证明 `HeckeSkeleton.Moments.EngineInduction.Source.PairedStepHypothesis`（`HeckeSkeleton/Moments/MOM_ENGINE_INDUCTION/StepHypothesis.lean`）。也可以先证一个等价的单步定理，再推出它。

- 这个结构的输出类型引用了已经合入 base 的定义，例如 `EngineStep.PairedEngineConclusion`、`RecipeMellinStrictFamily`。这些定义、它们的陈述，以及已合入的 431 个 STEP 模块，都可以直接使用。
- 不要改已合入的定义和陈述。如果确实必须改，按 README 规矩 3 办。

## 方向调整（2026-11-02 18:20）：改为蓝图

第一阶段的产出改为一份**蓝图**，不再是"所有定义加所有陈述"的骨架。要求如下：

1. **只保留必要的中间陈述**：从 base 到 `PairedStepHypothesis` 之间，按论文 §4.8（第 2741–3074 行）的引理和步骤，每一步写成一个陈述。每个陈述只依赖 base 和其他蓝图陈述，规模控制在一个会话能独立证完，目标是一个陈述不超过 3000–5000 行证明。
2. **数据定义只保留陈述里用得到的**，而且必须是真实定义，不能写 sorry，尽量直接用 base 里已有的定义。A 线那套字面量机制不要搬进蓝图；A 线代码只在证明阶段由各任务按需参考。
3. **证明全部写 `sorry`**。蓝图要能在 CI 上编通，而且应该很快。
4. **先证组装定理**：只把蓝图陈述当作前提，证明能推出 `PairedStepHypothesis`。组装定理本身不能用 sorry。这一步证通，才说明拆分是完整的。
5. **发布任务清单**：每个陈述一项，写明名字、所在文件、依赖、论文行号、估计规模，以及可以参考的 A 线代码。之后每项交给一个会话：它在自己的文件里证明，私有辅助引理随便加，但不改蓝图陈述；确实需要改时，先在 PR #31 提出。

下面"做法"一节里与此冲突的地方，以本节为准。

## 任务会话（证明阶段）

B 线在 PR #31 发布了任务总表（S1–S6、N1–N9、T1–T4、U1，共 23 项）。只有标为**已冻结**的任务才能开工。负责某一项任务的会话按下面的规矩做：

1. 从 `cloud/mom-engine-step-v2` 的最新 head 切出自己的分支，命名为 `cloud/mom-v2-<任务编号小写>`，例如 `cloud/mom-v2-n5a`。开一个标题带 `[不合并]` 的 draft PR 到 `dtests-handoff`，用来触发 V2 的专用 CI。
2. 只改本任务的文件（把其中的 `sorry` 换成证明），以及在它旁边新建的私有辅助文件。新建的文件要登记进 manifest 和 Interface。不要改任何已冻结的公开陈述，也不要动其他任务的文件。确实需要改陈述时，先在 PR #31 提出。
3. 边写边编，分批推送，等每一轮 CI 跑完再推下一批。今天踩过的坑（linter、全局实例、记号检查）见上文的规矩。
4. 完成标准：本任务文件里没有 `sorry`，CI 全绿，对本任务声明做的公理检查只含三条标准公理。达到后在 PR #31 留言，由 B 线合入 `cloud/mom-engine-step-v2`。

## 做法

### 第一阶段：设计和陈述骨架

1. 读论文里对应的部分。PR #9 的说明里有论文对照，从那里找起。
2. 参考两份代码：
   - MOM_INV_STEP，它是体量合适、已经编通的样板；
   - A 线的代码，即分支 `cloud/mom-engine-step` 和骨架分支 `cloud/mom-engine-step-skeleton`。
   A 线代码可以复制、改写、拆用。
3. 设计紧凑的模块结构：
   - 几个变体共用的论证（有限叶子、覆盖、终端校准、Fintype 实例等）写成通用定义和引理，各变体只做实例化；
   - 左右两侧尽量用同一套定义，参数化处理。
4. 先写**陈述骨架**：所有定义和定理陈述写全，证明一律用 `sorry`，然后在 CI 上编通。
5. 在 PR 说明里写模块计划：模块列表、依赖层次、每个模块的估计行数，以及分成哪几组。每组不超过 100 个模块，总量目标在 10 万行以内。

### 第二阶段：并行写证明

骨架编通、分组计划贴出后，在本 PR 留言说明。协调员会按分组再开会话，本会话负责第一组的证明，并维护骨架。

## 规矩

- 新代码放在 `HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2/`，命名空间用 `HeckeSkeleton.Moments.EngineStepV2`，不要和 A 线的名字冲突。
- 在 `cloud/mom-engine-step-v2` 分支上工作。开一个标题带 `[不合并]` 的 draft PR 到 `dtests-handoff` 用来跑 CI。
- 自己写一个只编本线模块的 workflow，可以照抄骨架分支上的 `.github/groups/group_build.py` 和 `.github/workflows/mom-step-group.yml`。整个项目的门禁很慢，到最后再跑。
- **边写边编**：每写完一批文件就在 CI 上编一次，不要攒到最后。
- 每个文件在 import 之后加 `set_option linter.unusedSectionVars false`。
- 挂在 `abbrev` 上的 Fintype 等实例，只能用 local 注册，需要它的模块自己显式启用。全局注册会让下游的实例搜索变得极慢，这个教训见 PR #9 #issuecomment-6571400398。
- 局部 notation 的右边如果投影另一个 notation，要加 `set_option quotPrecheck false`。

## 完成标准

- `PairedStepHypothesis`，或者推出它的单步定理，编译通过，证明里没有 `sorry`，`#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`；
- 全项目编译门禁（`integration-build.yml`）通过；
- PR 标为可审查。

第一阶段的里程碑是骨架编通并贴出分组计划。达到之后不要停下，接着做第一组的证明。
