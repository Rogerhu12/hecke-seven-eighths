# EXPANSION 使用的实际 Euler 依赖

本分支需要真实补偿核的局部算术分解来完成小行、绝对大行与物理槽接线。
因此复用 HIGHBIN PR #7 的提交
`d88663c8e2c9461cdd942267631e829d72d1f9b3` 中
`ActualNormFormFullCorrection`、`ActualEulerProduct` 及其缺失的
`HeckeSkeleton/HighBinSupport` 依赖，共 45 个模块。

这些模块的定义、定理陈述和证明保持来源提交的内容。为兼容本分支尚未拆分的
原声明文件，只替换以下导入路径；对应数学声明在本分支已经存在：

| 来源模块 | 本分支原声明文件 |
| --- | --- |
| `HeckeGeneral.Analysis.AnnularTest` | `HeckeGeneral.Analysis.GlobalThetaData` |
| `HeckeGeneral.Analysis.PrimeWindowGeometry` | `HeckeGeneral.Analysis.PhysicalProbeData` |
| `HeckeGeneral.Analysis.PhysicalProbeRowData` | `HeckeGeneral.Analysis.PhysicalProbeRows` |
| `HeckeGeneral.Analysis.FiniteEulerRational` | `HeckeGeneral.Analysis.PhysicalProbeRows` |
| `HeckeGeneral.Analysis.RowEulerRegion` | `HeckeGeneral.Analysis.TInputRanges` |

没有覆盖 HIGHBIN 的 `ActualHighPresentation`，也没有导入来源分支较旧的
`TSmallRowInput` 陈述。本分支继续采用论文所需的小行截断 `Z^(1/16)` 与
相对指数节省 `1/50`。

需要区分两个对象：实际完整修正槽包含主素数项及 regular、valuation-one、
repeated 三类误差；共享 recipe 的 `primePolynomial` 是用于幅度和矩估计的
归一化主素数多项式。接线必须证明实际共轭方向、外部幂因子和原始删除掩码
的身份，不能直接把完整修正槽替换为裸多项式。

来源证明被纳入本分支的普通 Lean 构建与传递公理检查。复用源码不等于当前
依赖图已通过验证；验证结果以本分支对应提交的 Actions 日志及 artifact 为准。
