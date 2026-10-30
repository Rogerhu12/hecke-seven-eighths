# 接线：混合能量与冻结立方 → 实际对象

`HeckeSkeleton/LowHybrid*`、`HeckeSkeleton/LowFrozenCube*` 是上一轮交付的自包含核心（82 个模块），对一个一般的算术模型证明了论文引理 4.6–4.8：素指数坐标、乘法范数、六次符号律、两条大筛。

**目标**：把这个模型实例化到项目的实际对象上，得到对实际对象成立的混合能量与冻结立方结论：
- 外部理想 `ExteriorIdeal K S`；
- 允许生成元 `ThetaArithmeticData.generator`，以及 `AllowedGeneratorInput`；
- `idealSymbol`；
- 已证的 `QuadraticSieveBound`、`CubicSieveBound`，见 `HeckeSkeleton/Moments.lean`、`HeckeAxiom/QuadraticSieve.lean`、`CubicSieve/`。

实际对象最终要供 `HeckeSkeleton/Principal.lean` 的 `completedMarkedEnergy`（LOW-REFLECTED-ENERGY）使用。上一轮列出的缺失项见 `cloud_notes/low_hybrid/WIRING_NOTES.md`。
