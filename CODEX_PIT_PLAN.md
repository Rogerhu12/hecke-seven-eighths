# PR-WINDOW-PIT 实施计划

2026-10-30，Asia/Taipei。先完成本任务，再处理 DE-EULER。

## 路线选择

本机已依赖的 TauCeti 包含任意数域素理想定理：
`TauCeti.primeCount_univ_isEquivalent_div_log`，位于
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/PrimeIdealTheorem.lean`。
它不要求本项目的 S 算术数据或单位根条件。优先复用这项完整定理，
先检查现有 olean 及递归公理；不重复形式化光滑 Perron、围道移动或 Tauberian 定理。
不能把挑战占位或条件性的边界定理当成无条件 PIT。

## 证明分解

1. 由 π_K(x)∼x/log x 推出：任意 1<a<b<2，充分大的 X 上，
   范数位于 (aX,bX] 的素理想数量至少 c₀X/log X，c₀>0。
2. 实值、非负、非零的光滑 w 在某个闭区间 [a,b]⊂(1,2) 上有统一正下界 m>0。
   这里只使用光滑性的连续性；保留目标中原有的全部假设。
3. 有限 S 中的素位在 X 足够大时均不落入该区间。
   将 TauCeti 的区间计数准确接到项目的 finitePrimeEnvelope/dyadicIdealSupport，
   再逐项比较非负权重，得到原窗口和的下界。
4. 在新入口 `HeckeSkeleton/WindowPIT.lean` 给出与原 `window_prime_lower`
   定义相同的结论。为避免循环，不导入 `PrimeNormalizer`；直接使用相同的有限集表达式。

## 文件与验证

新证明模块置于 `HeckeSkeleton/WindowPIT/`，入口为 `HeckeSkeleton/WindowPIT.lean`。
不修改 `PrimeNormalizer.lean`、`Principal.lean`、上游库或构建配置。
先记录禁止修改文件的哈希。按用户 2026-10-31 的新要求，
`compile.py` 按依赖拓扑顺序逐个调用 `LEAN_NUM_THREADS=4 lake build <模块名>`，
同时只运行一个模块构建。产物由 Lake 写入正式 `.lake/build`；
不再直接调用 lean.exe，不再写入或读取私有 `.build/out`。
遇到读取 olean 失败或内存不足，等三分钟重试。
不跑全量构建、不提交、不读取论文。

严格递归公理守卫只接受 propext、Classical.choice、Quot.sound。
在忽略的临时目录中，以原 PrimeNormalizer 的源码副本添加新 import、替换唯一 sorry，
使用 `lake env lean` 检查完整副本及追加的递归公理守卫，
不生成另一份 olean，核验主线可直接引用；原文件保持不变。
最后写 `PIT_CODEX_REPORT.md`，记录范围、来源、文件行数、实际检查命令和输出。

实查该 PIT 缺少 182 个 TauCeti 模块的 olean，共 37,317 物理行；
238 个外部 Mathlib 导入已有编译产物。TauCeti 与项目的 Lean 4.35.0-rc3、
Mathlib 固定 revision 完全相同，源码依赖闭包未见占位或新增公理。
因此选择串行补编译这个单一目标的最小闭包，产物全部放在 Lake 的正式构建目录，
而不重新开发 Perron 或修改上游库。最终仍以递归三公理审计为准。
