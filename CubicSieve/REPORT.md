# 三次大筛交付报告

日期：2026-10-30，Asia/Taipei。所有本次改动均在 `CubicSieve/` 内。

## 结果与边界

**独立的无条件尖锐三次大筛证明已完成。**
`CubicSieve.Complete.targetBound` 已编译，递归收集的公理恰为
`propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。
实际初始指数 2 和实际 Poisson 改善都已填入；最终定理不要求调用者
另行提供初始大筛、尖锐大筛、`FullEstimate` 或 bootstrap 指数估计。

`CubicSieve.CompleteBridge.moment_cubic_sieve` 已编译，证明原来的
`HeckeSkeleton.CubicSieveBound K c`。两边通过 `Iff.rfl` 定义相等：
任意原 `TargetContext c`、原 `axiomChoice.A.Sf`、原 `probeData.arithmetic`、
原允许生成元、任意 ε>0、统一常数、任意 X,Y≥1、任意范数有界的平方自由
外部理想有限子集、e=±2 和任意独立复系数，均保持原量词与核。
常数在 X,Y、两个有限集、e 和系数之前选择。保留公共素因子的零值，
不假设两个支撑互素，不缩到 Eisenstein 域，也不删除单位扇区。
原上下文本身已有的数域及单位根条件没有改变。

**原 `HeckeSkeleton/Moments.lean` 没有修改，原 sorry 计数尚未减少。**
这是目录协作限制下交付的同命题完整证明，主线仍需执行下文的接入编辑。
原目标兼容桥也已通过递归三公理审计；最终验证所用的 `TargetContext`
及 `momentMesh` 均只依赖三项标准公理。原 `moment_cubic_sieve` 声明本身仍有
`sorryAx`，因为其原证明体尚未按下文替换，不能把新定理通过等同于原文件已改。

## 证明路线

1. `CubicCharacters`、`CubicConductors`、`PrimitiveCharacters*`：实际 Kummer
   三次 Hecke 角色、平方后分歧、所有理想上的系数校准、S 外精确导子、统一 S
   导子预算、本原射线类模型及参数分离。
2. `LocalTypes*`、`Initial*`：完整有限 S 局部类型和平衡截面，接通一般导子大筛，
   得到真实核的无条件初始指数 2；不把基数界当成该初始估计。
3. `AnalyticFactorization` 至 `AnalyticDualNorm`、`OrbitRows/Kernel/DualNorm`：
   全理想行的立方因子分解、同一核的算子界、全部 Γ₆ 轨道与有限单位类。
4. `Gauss*`、`ProfileGaussian`、`GaussPairOrbitalPoisson`：实际有限剩余环和混合
   Gauss 相位、所有频率（含非单位及零频率）、物理 Gaussian Fourier 的精确常数，
   以及原单位扇区的轨道 Poisson。
5. `ProfileSpectrum/Separation/Transfer`、`PoissonBlocks/Tail`：实际 Mellin 反演、
   双列范数的共同参数分离、带零点温和奇性的轮廓和全部轨道的可和尾界。
6. `PoissonOrigin/Coefficients/Smoothed/Estimate`、`AnalyticGcd*`、
   `GcdPoissonAssembly`：真实零项、精确 Gauss 能量预算、先证明绝对可和再交换级数，
   带符号 Möbius 重排及所有真实公共因子后代的环带估计。
7. `GaussianColumnBlocks`、`Complete`：完整列支撑的精确能量分块、原完整行球的
   Gaussian 上覆，得到实际 `FullEstimate`。`Improvement/Iteration/Bootstrap`
   完成 ξ ↦ (6ξ−4)/(3ξ−1) 的有限迭代、epsilon 吸收及对称化。

## 验证证据

钉住的工具链：Lean 4.35.0-rc3。仅单模块编译，未重建外部依赖。
最终三个模块均 exit code 0：

| 模块 | 源码 SHA256 | 耗时 |
|---|---|---:|
| `Complete` | `b00b2cc805aea072100f85be63337b5b21549388a298ae4201f930bea4563bb4` | 161.8 秒 |
| `CompleteBridge` | `ddcd74688ad2d8cb5cb1fdcee41c4f3dbe959b1a84d8b77bfc477e6578d4232c` | 42.2 秒 |
| `CompleteAudit` | `d40f5cc26746d7798207540a08f6e3153f975288b8416296c2816764840280da` | 83.3 秒 |

`CompleteAudit` 对下列六个声明执行递归三公理守卫：
`PoissonEstimate.actual_annular_bound`、
`GcdPoissonAssembly.annular_smoothEnergy_bound`、`Complete.full_smooth_bound`、
`Complete.fullEstimate`、`Complete.targetBound`、
`CompleteBridge.moment_cubic_sieve`。
实际输出：

```text
CUBIC_COMPLETE_AUDIT_CHECKED|6
'CubicSieve.Complete.targetBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubicSieve.CompleteBridge.moment_cubic_sieve' depends on axioms: [propext, Classical.choice, Quot.sound]
```

局部递归审计也已通过：`InitialAudit` 9 项、`ArithmeticOperatorAudit` 11 项、
`AnalyticAudit` 18 项、`PoissonAudit` 6 项、`TailAudit` 5 项。
这些端点数有重叠，不能相加当成工作覆盖率。
`Audit.lean` 另严格检查 30 个独立声明，并分别记录旧骨架类型和兼容桥。

最终联合验证命令：

```powershell
python -I CubicSieve/compile.py CubicSieve.CompleteAudit CubicSieve.InitialAudit CubicSieve.ArithmeticOperatorAudit CubicSieve.AnalyticAudit CubicSieve.PoissonAudit CubicSieve.TailAudit --check CubicSieve/Audit.lean
```

该联合验证退出码为 0；扩展后的六项严格守卫也已单独重新编译通过：

```powershell
python -I CubicSieve/compile.py --no-deps CubicSieve.CompleteAudit
```

最终清单核对全部 78 个文件的当前源码成功回执，其中 77 个模块的
直接导入指纹与 olean 均匹配，另 1 个为仅检查的 `Audit.lean`。
外部依赖沿用现有编译产物，不声明重新核验了所有外部源码。
逐文件源哈希、行数与成功回执记录在 `BUILD_MANIFEST.json`，详细日志及回执在
`.build/logs/`，最终审计日志为 `CubicSieve.CompleteAudit.log`。
不把“编译成功”或“没有直接 sorry”代替上述递归公理检查。

顶层共 78 个 Lean 文件、11,790 个物理行（包括注释、空行和审计）。
`CompleteAudit` 的本目录闭包覆盖 71 个文件；其余 7 个是六个独立审计文件和
`CoprimeGramDual`，后者由 `ArithmeticOperatorAudit` 导入并审计。
所有文件都被至少一个审计导入；排除嵌套注释与字符串后，新增代码中
`sorry`、`admit`、`axiom`、`native_decide`、`implemented_by` 的实际语法命中均为 0。
旧的未采用草稿位于忽略目录 `.build/drafts/`，不作为交付 Lean 文件。

## 主线接入

不要在 `Moments.lean` 内导入 `CompleteBridge`，它为了比较原陈述而导入了
`Moments`。主线应导入 `CubicSieve.Complete`，然后只替换原证明体：

```lean
-- 文件顶部：import CubicSieve.Complete

theorem moment_cubic_sieve : CubicSieveBound K c := by
  change CubicSieve.ExteriorSieve.TargetBound K (places K c)
    (probeData K c).arithmetic
  exact CubicSieve.Complete.targetBound (axiomChoice K c).A
    (probeData K c).arithmetic (allowedGenerators K c)
```

接入后，主线需用自身更新的依赖 olean 编译 `Moments` 和自己的 Audit，
才能更新原 sorry 计数及全项目终点公理。以上编辑未在本轮越过目录范围执行。
独立入口不导入 HeckeSkeleton，因此不会引入该方向的导入循环。

## 来源与操作范围

数值迭代及部分域无关代数证明参考只读旧缓存中的 openai/math 三次大筛代码；
真实一般数域算术、Poisson 和分析接口接现有 HeckeGeneral、类域论及上游库。
没有把特殊域定理改名作为一般域证明。

未修改本目录以外的源码或 Lake 配置，未全量构建，未提交，
未读取或修改受限论文。全队最多两个单线程 Lean 编译进程。
`TOKEN_AUDIT.md` 是 18:39 截止时的历史统计，不代表最终整轮 token 用量。
