# MOM_BASE：有限系数、规范补全与配对背景

本目录实现 `cloud_tasks/MOM_BASE.md`，对应论文 §4.1–4.2，特别是引理 4.3 和 4.4。供其他 moments 任务使用的统一入口是：

```lean
import HeckeSkeleton.Moments.MOM_BASE.Main
```

所有声明位于 `HeckeSkeleton.Moments.MOM_BASE`；配对背景的声明位于其子命名空间 `Paired`。本任务没有独立的骨架 `OBLIGATION`，也不修改已有定义或证明。

## 规范系数和立方补全

`CanonicalCalibration.lean` 使用 `TargetContext` 已固定的同一个 `axiomChoice`，证明平方自由外部理想上的实际校准：

\[
\gamma_2(I)^3=\mu_K(I)\Lambda(I),\qquad
a_0(I)\gamma_1(I)=\mu_K(I)G(I),\qquad
\mu_K(I)\overline{\gamma_1(I)}=a_0(I)\overline{G(I)}.
\]

这里 `canonicalCoefficient` 是 \(a_0=\bar\Lambda\gamma_2\)，`canonicalPeriod` 是 \(\Lambda^{-1}\nu\)。校准、单位模长和 `G` 的有限阶性质均由实际算术选择导出。

`FiniteBackground.lean` 证明有限扭曲保持实际径向参数、复位角权重和非零角条件。它还由同一个 `TargetContext` 的 `Lambda_weight`、`representative_angular` 和 `G` 的有限阶性质，直接证明 `Θ ∪ ψΘ` 背景的规范周期具有非零角权；`momentData_canonicalPeriod_nonzero_angular` 接入实际 `MomentData.directed_background`，无需另加角条件。

`Arithmetic.lean` 把实际六次剩余符号扩展到所有整数理想；排除素数处取零。`canonicalTau` 同时包含 Hecke 系数、实际剩余符号和原始互素 puncture，并证明完全乘法性。六次幂、十二次幂保留互素指示函数，不能在零点处替换成常数一。

`CubeMobius.lean` 和 `CubeInversion.lean` 对实际整数理想证明立方 Möbius 反演。`canonicalCubeInversion` 的假设仅为：完全乘法的 `tau`、任意 whole-index 权重 `d`、正尺度 `X` 和测试函数的支撑有上界。`canonicalCubeInversion_of_hasCompactSupport` 给出论文中的紧支撑形式。有限支撑与重排所需的可和性在模块内证明。

`ThetaBridge.lean` 将反演后的项逐项识别为仓库原有的 `completedTerm`，保留原来的 puncture、whole-index 标记和权重。`weightedCompletedTheta` 在权重恒为一时就是原有的 `completedThetaSum`。

主要入口如下。

| 声明 | 作用 |
|---|---|
| `canonicalCompletedTerm_eq_actual` | 实际完成项的逐项系数等式，包括所有零值掩码 |
| `canonicalCompletedSum_eq_weightedTheta` | 从所有理想的反演和限制到实际外部理想 theta 和 |
| `actualCompletedSummand` | 证明 `HeckePort.Moments.Descent.Completion` 所需的有限支撑接口 |
| `canonicalThetaBridge` | 对实际 `ThetaArithmeticData` 的加权立方补全 |
| `targetCanonicalThetaBridge_of_support` | 对单个 `TargetContext`、实际行 `k * generator(f)^4` 和实际周期的规范系数等式 |
| `targetCanonicalThetaBridge` | moments 所用的 `SmoothAnnularTest` 版本 |
| `targetCanonicalNormalizedThetaBridge` | 中央归一化的平方自由多项式；完成测试为 `sqrt(y) * W(y)` |

提取理想 `h` 后的权重严格是 `d(h^3 A)`，尺度严格是 `X / N(h)^3`。提取系数中出现 `nu(h)^3`，活跃 theta 周期仍为 `conjugate(Lambda) * nu`。`Marks.lean` 证明原始 mark-priority 分配和联合行—标签平方范数的收缩，标签十二次幂仍是其原始互素掩码。

## 有限相关和删除接口

`LocalGauss.lean` 从 `TargetContext` 已有的实际算术选择出发，证明任意 S-整数频率上的规范素数幂 Gauss 公式，包括零频率。非平凡分支的模长为 `sqrt(P^(n-1))`，且只在频率属于原始 `p^(n-1)` 而不属于 `p^n` 时非零；`6 ∣ n` 的分支给出原始两个理想成员指示函数的 Ramanujan 差。商环基数、单位乘统一化元的分解及其与原始理想支撑的关系均在模块内导出。

`FiniteCoefficients.lean` 用 `ThetaArithmeticData` 给出的六次单位根、嵌入和排除条件，证明实际外部素数上的六次角色阶数、素数 Gauss 模长、素数幂角色、零值保持和相关表。实际 CRT 入口从互异素数导出所需的两两互素性，不把它作为额外算术公理。

`FiniteArithmetic.lean` 将该 CRT 角色直接识别为同一 `ThetaArithmeticData` 的实际理想剩余符号。它覆盖任意 S-整数分子，保留所有零值；`canonicalTau_actualCRT` 进一步给出实际 Hecke 系数、CRT 角色与原始 puncture 的精确乘积。

`SupportedCorrelation.lean` 使用实际允许生成元，证明完整相关的零频对角、共同理想对频率的支撑限制、共同因子的精确分解，以及在插入 Möbius 掩码前固定的扩展。剩余生成元使用原生成元的**字面商**；独立生成元之间的单位差和 `R` 修正均保留在公式中。

对实际完整素数幂模数，相同重数给出 `P^a` 上界，以及非平凡指数、单位除后频率处的 `P^(a-1)` 上界；不同重数 `a > b` 给出 `6 ∣ b` 和单位除后频率的必要条件，以及 `P^b` 上界。

`CoefficientInterfaces.lean` 证明实际 `canonicalTau` 满足 `HeckePort.Moments.IdealCoeff`，并给出实际 plain 和的可和性与精确有限素数删除公式。没有把仅在互素对上成立的结论冒充成完全乘法性。

## 配对 whole-product 背景

`PairedPhases.lean` 给出核心不变量：若活跃 plain 角色为 `omega * xi`，指定 slot 为 `omega⁻¹ * theta`，则实际素数系数先取消背景，再送入有限阶角色 `xi * theta`。需要保留原始 `xi` 与 `theta` 的分歧掩码，因为二者乘积可能消去分歧。

| 模块 | 内容 |
|---|---|
| `PairedPhases` | 指定 slot 配对、有限扭曲及两次有限变换、whole-product 提取、共同因子取消、单位模长和允许的共轭操作 |
| `PairedPolynomials` | 对实际 `MomentData` 的 plain/prime/slot 多项式和 centered 表达式的等式 |
| `PairedContext` | 从实际 `TargetContext` 导出外部素数处的背景不分歧性，提供上下文入口 |
| `PairedFiniteRay` | 实际归一化 cyclic-ray 表、两次表展开、先于行和素数固定的正阶数，以及 frozen/live slot 的分配 |

整行换向同时共轭 plain 列、每个 slot、系数和测试。对单个已反射 plain 因子的共轭只用于其乘积绝对平方；centered 差在拆开矩形之前保留共同 profiles 和 whole-product 角色。

## 陈述边界

`ThetaArithmeticData` 提供实际局部符号、生成元和商环数据。全局校准与选定的背景则使用 `TargetContext` 的同一个算术选择，不能从任意生成元数据直接推出。

原有 `MomentData.theta` 是有限集合，没有对乘积或逆封闭的字段。因此有限扭曲的结论是实际 `FiniteOrder`，以及在变换前选定的有限表；不声称扭曲后仍属于未经扩大的同一个集合。

原有 `SupportedCorrelation.CharFamily` 要求所有 S-整数上的互反相位都实值且对称；允许生成元截面不提供这个更强的陈述。本目录通过实际外部理想相关与字面生成元商给出正确的消费接口，保留单位修正，不添加该全局假设。

## 验证

固定环境为 Lean `4.35.0-rc3`、Lean commit `470d5ce1400764999581fd26d5d72b00d990b0f4`、Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。安装固定工具链并取得官方 Mathlib 缓存后，运行：

```sh
python3 scripts/verify_mom_base.py
```

专用 Actions workflow 在官方 Mathlib 缓存之后调用仓库的 `restore-lake-cache` action，恢复最新已发布的 `lake-cache-*`。标准 `lake build` 负责校验依赖缓存的源码、配置、依赖和产物哈希；本目录的编译产物在验证前移除，确保 18 个任务模块（含单独重编的 `Audit.lean`）每次均重新编译。

验证脚本同时检查源码中的全部 230 个公开 theorem/lemma 与显式审计清单完全一致，再重新执行递归 `#print axioms`。每个入口的公理集必须包含于 `{propext, Classical.choice, Quot.sound}`；缺失目标、重复目标、源码变化或任何额外公理均使验证失败。脚本不会复用旧的自定义对象缓存，也不需要历史 Actions artifacts。

编译输出、固定环境、源码哈希、release 缓存 manifest 与 SHA256SUMS、公理清单只放在 Actions artifact 中。
