# LOW-HYBRID / LOW-FROZEN-CUBE

本包按 `TASK.md` 的云端补充条款，交付仅依赖 Mathlib 的自包含证明。内容从原始混合和、素位指数与原始局部表出发，构造完整的有限归约，推出混合能量、冻结源能量及其终端参数账本。它不以最终能量界、正常形等式或产品纤维估计作为主定理假设。

实际 `ExteriorIdeal K S`、允许生成元及 `idealSymbol` 到本包一般模型的实例字典，因项目传递依赖未完整提供，另列于 `WIRING_NOTES.md`。本包不声称完整的用户项目已在云端构建。

**最终核验：82 个 Lean 模块全部通过；570 条公开定理/引理、3 条私有辅助定理；全环境审计覆盖 955 个定理常量。源码合计 12,597 行。**

## 1. 阅读顺序

| 文件 | 内容 |
|---|---|
| `LOW_HYBRID_REPORT.pdf` | 一页报告：主结论、假设、论文对应与接线范围。 |
| `HeckeSkeleton/LowHybrid.lean` | 混合能量及全部辅助模块的入口。 |
| `HeckeSkeleton/LowFrozenCube.lean` | 冻结分解、局部表、原始源项、计数与账本的入口。 |
| `THEOREM_INDEX.md` | 每条源码定理的原样签名，包含私有辅助定理。 |
| `ELABORATED_TYPES.md` | Lean 从最终环境直接导出的完整类型；包含继承的 section 参数、隐式参数和类型类假设。 |
| `NORMAL_FORM_PROOF.md` | 原始混合和到联合加权块的证明路线。 |
| `BOUNDARY_REVIEW.md` | 独立数学审查和支撑、质量、常数量词核查。 |
| `WIRING_NOTES.md` | 实际项目字典、可见入口及逐项“需核对”的缺失上游名称。 |
| `build_logs/verification.json`、`VERIFICATION.txt` | 模块、版本、成功状态与源码哈希证据。 |
| `build_logs/HeckeSkeleton.LowAudit.log` | 全部新定理的公理依赖审计。 |

旧的 `hybrid_proof.md`、`weighted_proof.md` 是辅助纸面推导。最终形式化范围与声明以本 README、完整类型附录和实际 Lean 源码为准。

## 2. 混合能量主结论

记

\[
E=\sum_k\left|\sum_P\frac{a(P)}{\sqrt{N(P)}}1_{(P,k)=1}
 \sum_{n,b}\beta(n,b)\chi_k(nb)^3\chi_P(n)^{-2}1_{(P,b)=1}\right|^2.
\]

`HeckeSkeleton.LowHybrid.hybrid_energy_bounded` 证明：对每个正数 ε，存在正数 C，在选择全部尺度、有限支撑集与系数之前选定，使

\[
E\le C(KNBL)^\epsilon(K+NB)B\{N+L+(NL)^{2/3}\}.
\]

尺度满足 K,N,B,L≥1。行 k、标记 P 和 n 平方自由，分别位于相应的范数上界内；b 的范数不超过 B，且不要求平方自由。系数满足 |a(P)|≤1、|β(n,b)|≤1。`a : A → ℂ` 与 `β : A → A → ℂ` 的类型直接保证它们所允许依赖的变量；固定的额外支撑限制可以编码到有限集或系数中。

`hybrid_energy` 保留精确的标记质量

\[
\sum_{P\in\mathrm{marks}}\frac{|a(P)|^2}{N(P)}.
\]

`hybrid_energy_with_beta_mass` 允许任意 β，右端再乘有限支撑上的真实 `betaSquaredMass`，即 max |β(n,b)|²；空支撑时质量为零。这里不会重复计算 β 的平方质量。

### 基础假设

主定理的一般模型使用：

1. 交换幺半群 A 与唯一素指数坐标 `A ≃* Multiplicative (ι →₀ ℕ)`。
2. 乘法实值范数 `normI`，它等于正自然数值 `q`，以及有限范数球的线性计数界 `LinearNormCounting q Ccount`。
3. 六次符号的两变量乘法与精确六次幂掩码律：共同素位时为零，互素时六次幂为一。
4. 题设二次大筛 `QuadraticSieveInput` 和三次大筛 `CubicSieveInput`。三次大筛使用整数指数 −2。

主定理不依赖 `TargetContext`。除两条大筛外，所用有限 Möbius 展开、范数截断、乘积纤维、平方自由除数、调和和与任意小幂均由上述基础算术数据在本包内部证明。

### 关键证明组织

实际分解是 b=g t²、n=c m、g=c h；只要求 c,m,h 两两互素，允许 g 与 t 共有素因子。两次完整 Möbius 展开分别处理标记与行、c 与行的掩码，原始零值在全部重排中保留。

加权 Cauchy 作用于联合的 t,c 索引。随后先用平方自由产品 m h 的二次筛，保留真实的立方预算，再对联合 m,c 列应用三次筛。没有对每个 b 分别作 Cauchy 而损失一个额外的 B。

保留标记质量的主定理中，小幂吸收明确计入五个除数因子、五个调和因子及两条筛的因子，内部参数取 η=ε/12。无质量的 `hybrid_energy_bounded` 再将最终 ε 平分：一半交给上述主定理，另一半吸收原始标记质量的调和和。系数列的除数质量单独记账，不能遗漏或假定为一。

### 独立的完成二次结论（引理 4.6）

`HeckeSkeleton.LowHybrid.completed_quadratic_energy_bounded` 单独证明

\[
\sum_k\left|\sum_{n,b}\beta(n,b)\chi_k(nb)^3\right|^2
\le C_\varepsilon(KNB)^\varepsilon(K+NB)NB.
\]

它只使用二次大筛、素坐标、自然乘法范数、线性计数、符号第二变量乘法与六次幂掩码律；不要求三次大筛或全符号互反。常数在全部尺度、有限支撑和系数之前选取。假设是 K,N,B≥1，k、n 平方自由并满足对应范数上界，b 任意且范数不超过 B，原始系数 |β(n,b)|≤1。

证明先按实际产品 y=nb 聚合系数，再规范写为 y=s t²。原 n 的平方自由性把产品重数限制在 y 的实际平方自由除数数内；原 k,t 碰撞零值保留到 t 固定后。任意聚合系数的 `CompletedQuadratic.completed_quadratic_positive` 给出正性归约，随后以真实支撑计数和 η=ε/5 吸收两个除数、两个调和与一个筛小幂。该正性式保留产品聚合后的实际支撑；它没有逐字另行封装论文的 dyadic `(T,G,C,r)` 展示公式。混合证明所需的完整双掩码正性化由前述正常形与加权组合完成。

## 3. 冻结立方出口

冻结模块从原始行和原始局部指数出发，构造

\[
k=k_{\rm pow}k_{\rm sup}d,\qquad e_p=e_p^{\min}+3x_p,
\qquad a'=a_{\min}x^3,\qquad b=xn'.
\]

原始局部表先删除零项，再推出合法指数、唯一最低指数与完整立方重排。`a(P)` 与 `β(c′,b)` 的行独立性是实际构造的结论。原始局部表、相位与系数经过这一出口后才应用混合能量定理。

两个支撑范围有意区分：`Data.support` 控制行和标记的排除条件，`Data.ordinary` 是活动普通素位集 f₀。对偶变量 c′、n′ 只需避开 f₀；不活动素位仍可出现在对偶变量中。

`Overlap.lean` 对整个完成指标 c·n³ 证明标记重叠为零，并提供实际源项的行、列及完整立方碰撞零引理。它允许列与立方变量共有素因子，也允许标记槽重复。

`weighted_raw_hybrid_bound` 保留平方自由列的 1/√N(c) 和真实剩余行的 K₀ 环带。局部归一化给出准确的 `(tableMajorant/Bmin)²/Nmin` 因子。`LocalBudget.lean` 再从逐素 Gauss 平方界证明计费理想界，而非要求调用者给出已组装好的系数损失。

`source_energy_ledger` 把原始源能量接到反射指数 E_ref。`TerminalSource.lean` 使用明确的导子比较、保留范围及裕度条件，将其转为终端三分支界和固定幂节省。这些条件是论文账本中的标量前提，不是预设的源能量结论。

冻结块数由实际素坐标证明：强力部分通过平方—立方配对计数，受支撑平方自由部分通过实际素支持计数。`FrozenPartition.lean` 给出原始行和的精确正项分块。强力部分的 O/2 只支付一次。

统一版本把纯算术数据固定后，先选 C，再允许冻结支撑、局部数字和最低指数变化。它们与具体名字、完整参数一起列在类型附录中；不得把固定 D 版本的量词自动解释成跨所有 D 的统一结论。

## 4. 与论文及实际项目的边界

| 论文内容 | 本包实现 |
|---|---|
| 引理 4.6 的完成二次归约 | `completed_quadratic_energy_bounded` 对原始 n,b 双和给出仅用二次筛的完整 `(KNB)^ε(K+NB)NB` 界；`CompletedQuadratic.completed_quadratic_positive` 给任意聚合系数的正性形式。原始分解、完整掩码与继承支撑也进入混合证明。 |
| 引理 4.7 的混合范数 | 原始字面能量的完整任意 ε 界，以及精确系数质量版本。 |
| 引理 4.8 的冻结行分解 | 原始局部表 → 合法冻结指数 → 完整立方 → 行独立系数与碰撞掩码 → 混合能量出口。 |
| 终端参数账本 | 局部平方损失、实际冻结块计数、共同核标量与 E_ref、终端分支及裕度。 |

本包不重证题设已经提供的二次、三次大筛，也不宣称重证 theta 反射、共同 Mellin/profile 分离或无限级数尾项。冻结源能量定理针对已经分离的有限原始源块；共同核及导子等几何参数以论文中的明确标量条件进入。

仍需在完整项目识别：外部理想及范数与素坐标模型；`idealSymbol` 及允许生成元的乘法、六次幂与互反字典；原反射系数与本包显式局部表的定义。最需本地核对的是允许生成元的六次 S-unit 误差如何消去，以及实际局部表的精确识别。`WIRING_NOTES.md` 逐项列出已看到的入口与未提供的上游名称，没有杜撰项目定理。

## 5. 复核方法

目标版本固定为 Lean **4.35.0-rc3**、Mathlib **0493595ecd5da8ef14742febab99728f98e948e8**。包中不分发 Mathlib、Lean 二进制或本次编译的 `.olean`。

在已准备好精确版本 Mathlib 的环境中运行：

```bash
python3 build_serial.py --lean /path/to/lean --mathlib /path/to/mathlib
```

Windows 可将两个路径替换为实际绝对路径。脚本按本包 import 拓扑顺序，每次只启动一个 Lean 模块编译、使用 `-j1`，首个失败即停止；不自动构建或下载其他依赖。每个日志记录版本、命令、源码 SHA-256、编译期间源码是否保持不变及退出码。

`LowAudit.lean` 枚举两个新命名空间的全部定理，包括归一化私有名称后的辅助定理，使用 Lean 的公理依赖收集器检查允许集恰为 `propext`、`Classical.choice`、`Quot.sound`。任何额外公理都会使审计编译失败；各定理可以只依赖该集合的一个子集。

`LowDeclarations.lean` 从最终核验环境导出完整定理类型，避免源码签名省略 section 参数。`SHA256SUMS` 覆盖交付文件。原输入压缩包和解出的参考文件保持原样；没有修改原工程文件或创建提交。

作者标注：Roger Hu / GPT-6 Astra Pro。来源及参考许可见 `THIRD_PARTY_NOTICES.md`、`PROVENANCE.json` 与 `LICENSES/`。
