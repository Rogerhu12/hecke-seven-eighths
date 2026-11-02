# MOM_ENGINE_STEP E 线：先批量清机械错误，再修证明错误

先读 [README.md](README.md)（通用规矩，特别是规矩 6），再把 PR #9 的全部评论分页读完。

## 背景

PR #9（分支 `cloud/mom-engine-step`）是配对引擎的单步部分。A2 是唯一 owner，负责把各线的修复采用进主分支。A、B2、D 三条线各自认领了一批文件。

- 还没进 `dtests-handoff` 的 STEP 文件有 578 个，其中五百多个至今没有带着真实证明编过。
- 协调员在 `probe/mom-engine-step-map-2` 上跑 sorry 探针（只用于找错，永不合并），每次的错误清单都贴在 PR #9。
- 已经编过的部分里，约三分之一的模块有错。其中一半是可以批量处理的机械错误，另一半是局部的证明错误。

## 工作方式

- 在 `cloud/mom-engine-step-e` 上工作，从最新的 `cloud/mom-engine-step` 切出。需要跑 CI 时，开一个标题带 `[不合并]` 的 draft PR。
- 先在 PR #9 认领，再动手。别人已经认领的文件不要改；在那些文件里发现问题，就把位置告诉认领人。
- 修好的整份文件交给 A2 采用，流程和其他线一样。不要推送 `cloud/mom-engine-step` 或其他线的分支。

## 第一步：批量清机械错误

扫描全部未进 base 的 STEP 文件，处理下面两类问题。

1. **换行的字段投影**：上一行已经是完整的接收者表达式，下一行却以 `.field` 开头。Lean 会把这个 `.field` 当成一个参数，报 `Function expected`。处理方法是把它接回上一行末尾，只删换行和缩进。真正的匿名构造参数（例如传给函数的 `.inl h`）不要动。已采用的例子见 `CanonicalLiteralPoolAtlas`、`CanonicalLiteralCommonLeaf`、`CanonicalLiteralChartLocations`。
2. **universe 没定下来**：结构体字段或定义的 binder 里出现了不带 universe 的 `PUnit`，报 `Failed to infer universe levels`。处理方法是显式写成 `PUnit.{1}`，写法和已采用的 `DirectSecondStages`（blob e1016c8a）、`CanonicalLiteralExtraction` 一致。

另外，任何文件编译超过几分钟，就按规矩 6 在 import 之后加 `set_option linter.unusedSectionVars false`。

## 第二步：修证明错误

接手探针清单和各线日志里还没有人认领的证明错误。只改证明体，不改陈述和定义；需要改共享定义或陈述时，先交 A2 裁定。每批修完都送正常编译和 fresh 公理检查。

## 完成标准

PR #9 的三道门在同一棵最终源码树上全部通过：

- 完整的 Interface 构建；
- fresh 遍历整个 `HeckeSkeleton.Moments.EngineStep`（含 private/generated），只允许 `propext`、`Classical.choice`、`Quot.sound`；
- 全项目 20 个库的 Whole 构建。
