# PR-WINDOW-PIT 交付报告

2026-10-31，Asia/Taipei。

## 当前状态

PR-WINDOW-PIT 的新证明、正式 Lake 构建、严格递归公理审计、原消费文件接入副本检查均已完成。
新证明共 410 行 Lean（含审计）；最终入口只依赖三条标准公理。
按任务约定未修改真实 `PrimeNormalizer.lean`，主线占位由接入方按下面的一行证明替换。

## 证明路线

复用项目固定依赖 TauCeti 的无条件任意数域素理想定理
`TauCeti.primeCount_univ_isEquivalent_div_log`，得到 π_K(x)∼x/log x。
其输入是同一个数域中全体高度一素理想的真实无权计数，范数为 `Ideal.absNorm`。
没有增加零点自由区、S 算术数据或计数渐近假设。

由这个渐近得到固定比例区间 `(aX,bX]` 内的素理想数量下界。
非零、实值、非负、连续的窗口权重在某个 `[a,b]⊂(1,2)` 上具有统一正下界。
当 X 超过有限异常集 S 的素理想范数上界后，该区间避开 S；
逐项比较权重，即得原窗口和的 `cX/log X` 下界。

不需要重复形式化 Perron 公式或 Wiener–Ikehara；后者已包含在 TauCeti 的上游证明中。
初始缺少编译产物的最小 TauCeti 依赖闭包为 182 个模块、37,317 物理行；
这些是复用的上游源码，不计入新写证明行数。

## 新增 Lean 文件

| 文件 | 物理行数 | 作用 |
| --- | ---: | --- |
| `HeckeSkeleton/WindowPIT/IntervalAsymptotics.lean` | 103 | 固定比例缩放和区间下界 |
| `HeckeSkeleton/WindowPIT/PositiveInterval.lean` | 45 | 权重的正闭区间 |
| `HeckeSkeleton/WindowPIT/Envelope.lean` | 103 | 实际素理想计数与原窗口的连接 |
| `HeckeSkeleton/WindowPIT/FromCounting.lean` | 68 | 带权窗口下界 |
| `HeckeSkeleton/WindowPIT/Counting.lean` | 39 | 接入无条件素理想定理 |
| `HeckeSkeleton/WindowPIT.lean` | 25 | 与原目标对应的最终入口 |
| `HeckeSkeleton/WindowPIT/Audit.lean` | 27 | 严格递归公理守卫 |
| 合计 | 410 | 包括审计模块 |

## 接入方式

按任务范围，真实 `HeckeSkeleton/PrimeNormalizer.lean` 和 `HeckeSkeleton/Principal.lean`
不作修改。接入方在前者添加：

```lean
import HeckeSkeleton.WindowPIT
```

将其 `window_prime_lower` 的唯一 `sorry` 替换为：

```lean
exact HeckeSkeleton.WindowPIT.window_prime_lower K S w hre hnn hne hsupp
```

新模块中的 `windowPrimes` 使用与原文件逐字相同的定义体，Lean 可用定义相等识别。
新入口不导入 `PrimeNormalizer`，因此不会形成循环依赖。

## 构建与检查

`HeckeSkeleton/WindowPIT/compile.py` 按依赖拓扑顺序串行执行
`LEAN_NUM_THREADS=4 lake build <模块名>`。
编译产物全部由 Lake 写入各包的正式 `.lake/build`；不直接调用 `lean.exe`，
不再写入或读取历史 `.build/out`。读取 olean 失败或内存不足时等待 180 秒后重试。
根包现有 `weakLeanArgs = ["-j2"]` 没有修改，因此记录环境变量为 4，
不将它解释为所有根包调用实际均使用四个线程。

实际使用并成功退出的命令：

```powershell
python -I HeckeSkeleton/WindowPIT/compile.py TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem
python -I HeckeSkeleton/WindowPIT/compile.py HeckeSkeleton.WindowPIT.Audit
python -I HeckeSkeleton/WindowPIT/.build/check_integration.py
```

审计模块对 8 个关键声明检查名称存在，并递归拒绝 `propext`、
`Classical.choice`、`Quot.sound` 以外的所有公理。
集成检查只改临时源码副本，经 `lake env lean` 检查完整原消费文件，
另对原命名空间中的 `window_prime_lower`、`normalizer_positive`、
`normalizer_smallPower` 做同样的严格递归检查，不生成私有 olean。

182 个 TauCeti 依赖和 7 个新增模块的正式构建均退出 0。
`Envelope` 的 Lake 日志显示 9,407 个任务中只有目标模块新编译，其余复用缓存。
189 份构建回执记录的源码哈希和正式 olean 哈希已再次逐一核对一致，清单在
`HeckeSkeleton/WindowPIT/.build/formal-build-manifest.json`。
构建日志和回执在 `HeckeSkeleton/WindowPIT/.build/lake-logs/`。

审计实际输出的关键部分：

```text
PIT_AXIOMS|TauCeti.primeCount_univ_isEquivalent_div_log|propext,Classical.choice,Quot.sound
PIT_AXIOMS|HeckeSkeleton.WindowPIT.window_prime_lower|propext,Classical.choice,Quot.sound
PIT_AUDIT_CHECKED|8
'HeckeSkeleton.WindowPIT.window_prime_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
```

完整消费源码副本经 `lake env lean` 检查退出 0，实际输出：

```text
PIT_INTEGRATION_AXIOMS|HeckeSkeleton.PrimeNormalizer.window_prime_lower|propext,Classical.choice,Quot.sound
PIT_INTEGRATION_AXIOMS|HeckeSkeleton.PrimeNormalizer.normalizer_positive|propext,Classical.choice,Quot.sound
PIT_INTEGRATION_AXIOMS|HeckeSkeleton.PrimeNormalizer.normalizer_smallPower|propext,Classical.choice,Quot.sound
PIT_INTEGRATION_CHECKED|3
'HeckeSkeleton.PrimeNormalizer.window_prime_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
PIT_INTEGRATION_ORIGINAL_SOURCES_UNCHANGED
```

接入副本检查前后验证真实文件哈希未变：

- `PrimeNormalizer.lean`：`7f713f2119d74c2bc9175b75669263404861cbf9d24e99d10669f8152ac9d99b`
- `Principal.lean`：`41c14be9dc659159bee6e642374dddf7670536d05a5bed19791f119a3c67ac63`

固定工具链为 `leanprover/lean4:v4.35.0-rc3`；实际 TauCeti HEAD 为
`c197d7bdbae257e85d23443c89aa7cd34c13410b`，与项目固定版本一致。
这里报告的是 Lean 构建与递归公理检查；未运行额外的独立内核检查器。

## 范围

不提交，不跑全量构建，不修改上游源码和 Lake 配置，不读取论文。
本报告仅覆盖 PR-WINDOW-PIT；其他未完成的项目义务不由此关闭。
