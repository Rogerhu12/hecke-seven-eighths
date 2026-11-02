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

B 线在 PR #31 发布了任务总表（S1–S6、N1–N9、T1–T4、U1，共 23 项）。**草案任务也可以直接开工**，不必等冻结：
- 如果 B 线已经在 V2 里写好了该任务的 Lean 陈述，直接证它；
- 如果还没写好，就按总表里的描述和论文行号，在自己的任务文件里先写出陈述并编通，再在 PR #31 贴出来，由 B 线采纳或修改。

陈述以 B 线最终冻结的版本为准。陈述变了，就调整自己的证明去适配。证明过程中发现陈述是错的、缺条件，或者证不出来，尽早在 PR #31 报告，这本身就是在检验蓝图。负责某一项任务的会话按下面的规矩做：

1. 从 `cloud/mom-engine-step-v2` 的最新 head 切出自己的分支，命名为 `cloud/mom-v2-<任务编号小写>`，例如 `cloud/mom-v2-n5a`。开一个标题带 `[不合并]` 的 draft PR 到 `dtests-handoff`，用来触发 V2 的专用 CI。
2. 只改本任务的文件（把其中的 `sorry` 换成证明），以及在它旁边新建的私有辅助文件。新建的文件要登记进 manifest 和 Interface。不要改任何已冻结的公开陈述，也不要动其他任务的文件。确实需要改陈述时，先在 PR #31 提出。
3. 边写边编，分批推送，等每一轮 CI 跑完再推下一批。今天踩过的坑（linter、全局实例、记号检查）见上文的规矩。
4. 完成标准：本任务文件里没有 `sorry`，CI 全绿，对本任务声明做的公理检查只含三条标准公理。达到后在 PR #31 留言，由 B 线合入 `cloud/mom-engine-step-v2`。

## 组装会话（2026-11-02 22:15 起）

组装定理交给一个单独的会话，B 线专心修基线、冻结陈述。组装会话的规矩如下：

1. 目标：在 V2 里写出并证明 `pairedStepHypothesis_of_blueprint`。它以全部 23 个任务的陈述作为前提（显式参数，或者一个汇总所有任务证明的结构体），推出 `EngineInduction.Source.PairedStepHypothesis (WithLp 2 (ℝ × ℝ)) c`，本身不能有 `sorry`。B 线已经写好的组装零件（AssemblyCore、BudgetAssembly、OutputAssembly、EmptyAssembly、NormalizationAssembly、PrimitiveAssembly、UniformAssembly 等）直接用。
2. 分支 `cloud/mom-v2-assembly`，从 `cloud/mom-engine-step-v2` 最新 head 切出，开 `[不合并]` draft PR 到 `dtests-handoff`。
3. 只新增组装模块，必要时也可以改 Interface 和 manifest。不改任何任务文件，也不改任务陈述。发现陈述拼不上（缺条件、类型对不上、两个任务的接口不一致）时，在 PR #31 写清楚，由 B 线改陈述，各任务会话跟着调整。这是蓝图最重要的检验。
4. 有些任务陈述放在 RawContracts / OrdinaryData 里，这两个模块在基线修好前编不过。可以先写完、先编不依赖它们的部分，基线修好后再整体编通。
5. 完成标准：组装模块没有 `sorry`；CI 只编组装模块，并对这些模块做公理检查，只出现三条标准公理（任务陈述作为前提不会引入 sorryAx）；在 PR #31 报告。

## 基线并行修复（2026-11-03 01:00 起）

RawContracts 和 OrdinaryData 编不过，挡住了 8 个任务和组装。协调员的诊断（PR #31 上的评论，分支 `diag/v2-kernel`）结论如下：
- 卡在 Lean 内部的 `getFunInfo → collectDeps`。这一步不检查心跳，也不缓存，所以心跳上限、skipKernelTC、noncomputable、关 linter 都不起作用。
- 一旦要比较两个写法不同的 `SourceClassKey.AllocationKey …`（或这一族的其他 abbrev），就会卡住。
- 能编过的写法：柯里化的 `leafAt (i) (v : SourceClassKey …) (allocation : SourceClassKey.AllocationKey v)`（10s）；结构体键 `KeyS`，用字段调 `leafAt`（14s）；用有名字的 def 包起 fibre 的 Σ 键，Fintype 用 `unfold …; infer_instance`。
- 仍然卡住的写法：Σ 键与柯里化参数互相转换，即投影、match、`Sigma.casesOn`、`Sigma.uncurry`、`obtain` 加 `unfold` 这几种；Ordinary 的 `branch.val : AllocationKey packet.key`，以及它与 `HybridAllocationLabel …` 之间的 `rfl`。

下面的修法同时进行，**哪个先通过就由 B 采纳**，其余停止：

| 方案 | 负责会话 | 内容 |
|---|---|---|
| A | 新会话 1 | 把 RawLeafData 里 `SourceClassKey` 这一族的段落变量（E、hΓ、μv、hDiff、G、finiteTest 等）打包成一个结构体参数，缩短隐式参数串。然后看原来的 Σ `Key` 加 match 版本的 `leaf`，以及 OrdinaryData 的 `ordinaryBranchKey`，能不能编过。 |
| B | 新会话 2 | Key 改成结构体 `KeyS`（i、v、allocation），`leaf`、`classKey`、`LiveKey` 都基于它。需要找到一种 Fintype 实例的写法，全程不把 Σ 和结构体互相转换（例如对 fibre 用 `unfold` 加 `infer_instance` 的路子，或者直接构造 Finset）。 |
| D | 新会话 3 | OrdinaryData：重写 `ordinaryBranchType` / `ordinaryBranchKey`，不再要求 `branch.val` 直接是 `AllocationKey packet.key`。例如把分支类型定义成 `AllocationKey packet.key` 的子类型，或者让 `ordinaryBranchKey` 返回分支本身，另外给出对应关系。下游陈述的意思不变。 |

规矩：
1. 从 `diag/v2-kernel` 切出 `diag/v2-fix-<方案字母小写>`。把 `.github/workflows/v2-kdiag.yml` 的触发分支改成自己的分支，在 `.github/kdiag/` 放自己的探针（可以是 B 当前 head 的整份 RawContracts.lean 或 OrdinaryData.lean 的改写版），矩阵列出探针名。每个探针 100s 上限，超时自动抓调用栈。一次可以并行好几个探针。
2. 通过标准：改写后的整份 RawContracts.lean（或 OrdinaryData.lean）每个都在 100s 内编完；冻结陈述的数学意思不变；列出下游要跟着改的地方。
3. 每轮结果贴到 PR #31，写明哪些写法过了、哪些卡了。不要推送 `cloud/mom-engine-step-v2`，B 负责采纳。

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
