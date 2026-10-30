# 来源与改写说明

本包数学任务、论文摘录及旧仓库笔记由用户提供，原件未修改。

部分有限和与产品纤维证明参考 OpenAI 的 `openai/math` 项目，提交前缀 `fd4aeeb2`，尤其：

```text
lean/OAI/NumberTheory/DirichletL/Descent/SieveComposition.lean
```

`HeckeSkeleton/LowHybrid/SieveComposition.lean` 对其中的有限纤维组织方式作了改写：改为任意有限索引，补入本包需要的基础能量证明，显式保留二次与三次两个不同产品的纤维损失，并重新构造固定块组合接口。该文件并非上游文件的原样副本，其模块头保留来源说明。

上游对应源树采用 **Apache License 2.0**。完整许可证原文保存在 `LICENSES/Apache-2.0.txt`。其他 OpenAI 参考文件用于比照纸面结构，未作为本包的依赖导入。

本包依赖的 Mathlib 不随包分发；精确版本与官方源码地址记录于 `PROVENANCE.json`。生成报告时使用公开 Noto Sans SC 字体，PDF 内仅嵌入所需字形子集，未分发完整字体文件。

所有本轮新增与改写的证明均由指定 Lean 版本重新核查；该核查不替代尚未完成的实际 `ExteriorIdeal` 项目实例化，详见接线文档。
