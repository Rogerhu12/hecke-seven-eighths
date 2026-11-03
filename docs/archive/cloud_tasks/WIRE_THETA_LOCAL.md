# 接线：theta 反射的局部部分 → 项目定义

`HeckeSkeleton/ThetaLocal/` 是上一轮的交付，包括两部分：
- 复位：高 K-型向量、π(w)φ_m = φ_{−m}、Mellin 对与乘子恒等式；
- 有限位：数字表，以一般有限域的版本给出。

**目标**：把它们与项目里的对象对上，即 `HeckeGeneral/Analysis/MarkedThetaReflection.lean` 及其相关文件中的 `localTau`、`digitMask`、`sphericalDigit`、`localWeylScalar`、`localWeylExponent`、`thetaGamma`、`reflectionMultiplier`、`archRadial`。

上一轮报告（`cloud_notes/theta_local/THETA_LOCAL_TECHNICAL_REPORT.txt`）列出了必须核对的四个识别和一个约定：
1. q = `absNorm p`；
2. 特征的阶恰为 6；
3. `primePhase` 的规范化；
4. `thetaGamma(p,2)` 与 Gauss 和的规范化一致；
5. 径向参数 ρ = −heckeComplexParameter 的符号约定。

若项目的定义与论文不一致，按规矩 3 处理。未编译的候选适配在 `cloud_notes/theta_local/ActualExteriorAdapter.lean.txt`。
