# 一般数域三次大筛

`Complete.targetBound` 已完成并通过 Lean 4.35.0-rc3 编译及递归公理审计；
它只依赖 `propext`、`Classical.choice`、`Quot.sound`。
初始估计与实际 Poisson 指数改善均由具体证明提供，最终定理没有把它们作为假设。

对原算术数据、原 S 和原生成元，结论为：

```text
对每个 ε>0，存在 Cε>0，统一于 X,Y≥1、任意满足范数上界的平方自由
外部理想有限集 A,B、e=±2 和任意复系数 z：
energy(A,B,z,e) ≤ Cε (XY)^ε [X+Y+(XY)^(2/3)] Σ_{J∈B}|zJ|²。
```

入口：`CubicSieve/Complete.lean`。原目标接口：
`CompleteBridge.moment_cubic_sieve : HeckeSkeleton.CubicSieveBound K c`。
`SkeletonBridge.target_iff_skeleton` 通过 `Iff.rfl` 核对两边陈述完全相同。

按协作约定，没有修改 `HeckeSkeleton/Moments.lean`；原文件的 sorry 尚未替换。
独立定理与原目标兼容桥均已通过递归三公理审计；
当前 `TargetContext` 和 `momentMesh` 也只依赖三项标准公理。
主线接入方法、完整范围与证据见 [REPORT.md](REPORT.md)。

## 构建与审计

只构建本目录模块，使用现有依赖 olean，不运行全量 Lake 构建：

```powershell
python -I CubicSieve/compile.py CubicSieve.CompleteAudit
python -I CubicSieve/compile.py CubicSieve.ArithmeticOperatorAudit
```

`CompleteAudit` 对独立终点和原目标接口均严格拒绝任何非标准公理。
`ArithmeticOperatorAudit` 另覆盖不在主终点闭包内的双算子接口。
其余局部审计及最终联合验证命令列在报告中。

编译产物、日志和源码哈希回执位于忽略目录 `.build/`；
当前交付清单见 [BUILD_MANIFEST.json](BUILD_MANIFEST.json)。
`compile.py` 用两个跨进程锁限制本队最多两个 Lean 编译进程，每个进程一个线程。

78 个 Lean 文件，共 11,790 个物理行（含注释和空行）；
未计入旧草稿、依赖库、构建产物或说明文档。
