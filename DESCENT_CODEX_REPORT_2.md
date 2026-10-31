# DE-EULER 删除型 Artin 恒等式交付报告

2026-10-31，Asia/Taipei。

## 结果

已完成 `CODEX_TASK_DESCENT_2.md`：删除坏素位后的实际 Artin Euler 恒等式已证明，
并接入原 `HeckeSkeleton/Descent.lean` 的 `deletedEulerFactorization`。
主模块构建成功；`descend` 的递归公理集恰为
`propext, Classical.choice, Quot.sound`，不再含 `sorryAx`。
原来的 `hTIP` 前提和目标陈述全部保留；本次关闭的是阿贝尔下降这一项。

## 坏素位集合

对任意有限阿贝尔数域扩张 K/F，取

```text
badPlaces F K χ =
  (χ 的全部分歧素位 ∪ K/F 的全部分歧底层素位)
    ∪ (非零主理想 (6) 的素支撑)。
```

具体定义在 `ArtinPrimeArithmetic.artinBadPrimes`，最终接口为
`DeletedEuler.badPlaces`。第一项由 `finite_ramifiedPlaces F χ` 给出；
第二项是类域论包的实际 `ramifiedBaseFinitePlaces`；第三项使用实际
`idealPrimeSupport`。三项均为真正有限集，没有输入有限性假设。
已证明 `(6)` 的素支撑成员等价于 `6 ∈ v.asIdeal`，并分别证明
`2 ∈ v.asIdeal` 和 `3 ∈ v.asIdeal` 都推出成员关系。

上层取底层集合在实际 `finitePlaceBelow` 下的完整原像。
`DeletedEuler.mem_badPlacesUp` 精确给出

```lean
w ∈ badPlacesUp F K χ ↔ finitePlaceBelow (K := F) w ∈ badPlaces F K χ
```

其有限性由现成的有限素位纤维定理证明。
在集合外，χ 和全部 Artin 扭曲均未分歧；范数拉回也未分歧。
没有使用分歧处的精确局部 Euler 因子匹配。

## 证明链与候选来源

以下旧缓存均只读，适配后的代码放在新模块中并实际编译：

- `hecke-local-norm-20261011/ActualHeckeLocalNorm.lean`、
  `ActualHeckeLocalNormCoefficients.lean`：实际单点 idele 范数与项目局部特征相容，
  得到 `primeCoefficient K (χ∘N) W = primeCoefficient F χ v ^ f(W/v)`。
  此处只要求下层 χ 未分歧，不要求扩张未分歧。
- `hecke-artin-frobenius-20261011/ActualHeckeArtinFrobenius.lean`、
  `ActualHeckeArtinPrimeArithmetic.lean`：实际 uniformizer 的商类、局部/全局 Artin 相容性、
  未分歧处的 Artin 元阶、真实素位纤维与惯性次数公式。
- `hecke-artin-factors-20261011/FiniteCircleEulerProductCandidate.lean`、
  `ActualHeckeArtinLocalEuler.lean`：完整有限 Circle 对偶的多项式乘积，及其实际 Artin 因子实例。
- 同目录 `ActualHeckeDeletedEulerProduct.lean`、`ActualHeckeArtinPrimeAssembly.lean`、
  `ActualHeckeArtinFactorization.lean`：有限删除、收敛乘积重排、未分歧局部等式及整体恒等式。

缓存 README 所说的两个局部桥尚缺，在另外两个缓存目录中已有后续候选。
本次对它们作当前 API 的适配和正式构建，没有把缓存原来的 UNCOMPILED 标记当成验证。
现有 `ArtinFactors.lean` 的真实范数商、完整因子族及单射性直接沿用。

## 新增 Lean 文件

全部位于 `HeckeSkeleton/Descent/`，按物理行计，包含注释和空行：

| 文件 | 行数 | 内容 |
| --- | ---: | --- |
| `LocalNorm.lean` | 150 | 实际局部范数与局部特征比较 |
| `LocalNormCoefficients.lean` | 124 | 未分歧拉回及素系数幂公式 |
| `ArtinFrobenius.lean` | 278 | uniformizer、Artin 商元素及其阶 |
| `ArtinPrimeArithmetic.lean` | 220 | 坏集合、纤维基数和范数公式 |
| `FiniteCircleEuler.lean` | 152 | 完整有限对偶多项式恒等式 |
| `ArtinLocalEuler.lean` | 80 | Artin 因子族的局部乘积 |
| `DeletedProducts.lean` | 87 | 实际有限删除后的收敛 Euler 乘积 |
| `PrimeAssembly.lean` | 99 | 素位纤维重排与局部到整体连接 |
| `LocalIdentity.lean` | 71 | 未分歧处两侧局部因子相等 |
| `DeletedEuler.lean` | 42 | 坏集合接口与最终删除恒等式 |
| `DeletedEulerAudit.lean` | 29 | 严格递归公理守卫 |
| 合计 | 1,332 | 其中证明模块 1,303 行，审计 29 行 |

已有的 `ArtinFactors.lean`、`PoleMatching.lean` 未改源码，不计入新增行数。
新恒等式保留一般有限阿贝尔扩张 K/F，主文件将其用于原 `CyclotomicField 12 F`。

## 主文件接入范围

对保存的本轮起点逐字节验证：`HeckeSkeleton/Descent.lean` 只增加
`import HeckeSkeleton.Descent.DeletedEuler`，并替换 `deletedEulerFactorization` 的唯一证明体。
该定理的陈述、其他定义及整个 `descend` 证明尾段均保持原样。
实际范数拉回及因子族通过原定义和 `Artin.artinFactors_eq_image` 对齐。

起点 SHA256：`0a5e345863cffb04423f0135aa13fd64fd703929d5b60ae0004f6047b366d4e4`。
接入后 SHA256：`7620fd6811052841ee1f47442e87853717e925ba8fb9d618a510ffae96c597ff`。

## 实际构建与检查输出

固定工具链：`leanprover/lean4:v4.35.0-rc3`。
`compile.py` 为每次 Lake 调用设置 `LEAN_NUM_THREADS=4`，按依赖拓扑顺序逐个执行
`lake build <模块名>`，产物均写入正式 `.lake/build`。
根包原有 `weakLeanArgs = ["-j2"]` 未改，实际根模块编译仍受这一设置影响。
没有直接调用 `lean.exe`，没有使用 `.build/out` 产物。
读取 olean 失败或内存不足时，脚本会等待 180 秒再试；本轮未发生这类资源重试。

发现上游缓存缺失时，已停止原调用，先按拓扑顺序补建缺失模块及其受影响下游；
没有修改这些上游源码。新版脚本也检查本轮新产物引起的下游缓存失效。

实际成功的入口命令：

```powershell
python -I HeckeSkeleton/Descent/compile.py HeckeSkeleton.Descent.DeletedEuler
python -I HeckeSkeleton/Descent/compile.py HeckeSkeleton.Descent
python -I HeckeSkeleton/Descent/compile.py --check HeckeSkeleton/Descent/DeletedEulerAudit.lean
```

前两个入口按序调用单目标 Lake 构建。10 个新增证明模块和主 `Descent` 均退出 0。
主模块构建记录：

```text
Built HeckeSkeleton.Descent (58s)
Build completed successfully (10294 jobs).
exit = 0
```

第三个入口实际执行 `lake env lean HeckeSkeleton/Descent/DeletedEulerAudit.lean`，
名称存在检查及严格递归白名单覆盖 10 个关键声明，全部只允许标准三公理。
关键输出如下，退出 0：

```text
DESCENT_AXIOMS|HeckeSkeleton.Descent.LocalNorm.primeCoefficient_heckeNormPullback|propext,Classical.choice,Quot.sound
DESCENT_AXIOMS|HeckeSkeleton.Descent.ArtinFrobenius.orderOf_qprime_eq_inertiaDeg|propext,Classical.choice,Quot.sound
DESCENT_AXIOMS|HeckeSkeleton.Descent.DeletedEuler.artinDeletedEulerProduct|propext,Classical.choice,Quot.sound
DESCENT_AXIOMS|HeckeSkeleton.Descent.deletedEulerFactorization|propext,Classical.choice,Quot.sound
DESCENT_AXIOMS|HeckeSkeleton.Descent.descend|propext,Classical.choice,Quot.sound
DESCENT_AUDIT_CHECKED|10
'HeckeSkeleton.Descent.descend' depends on axioms: [propext, Classical.choice, Quot.sound]
```

主文件及新增文件的代码扫描无 `sorry`、`admit`、新增 `axiom`、
`native_decide` 或 `implemented_by`；注释不作为代码扫描结果。
`git diff --check -- HeckeSkeleton/Descent.lean` 通过。
10 个新增证明模块及主模块的源码/正式 olean 哈希均与成功回执一致。
清单为 `HeckeSkeleton/Descent/.build/formal-build-manifest.json`；
构建和审计日志、回执位于同目录的 `lake-logs/`。
审计文件由 `lake env lean` 检查，没有另存私有 olean。

没有修改 `HeckeGeneral/`、vendor、构建配置、其他骨架或 Gram 源码，
没有全量构建、清理依赖、提交或读取论文。
本报告记录 Lean 构建、递归公理检查及接口语义复核，没有额外运行独立内核检查器。
