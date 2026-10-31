# 固定源数据与同源矩模型接口

本接口是 PR #5 与 Moments 任务约定的共享层。`HeckeSkeleton/SourceData.lean`
不导入 `HeckeSkeleton/Moments.lean`。泛型声明不选择 `expansionRecipeRaw`，也不把
`targetData` 或 `highExpansion` 放进默认参数。

## 旧接口与新接口

| 原有对象 | 显式固定源接口 | 保留的含义 |
|---|---|---|
| `SourceMomentIndex K c Z T` 的类型直接引用 `targetData` | `SourceMomentIndexFor K c E Z T` | 原 block、amplitude label、t、subdivision、selected slots |
| `SourceMomentModels K c` 的字段接受含实际选择的索引 | `SourceMomentModelsFor K c E` | 同一固定 E 的 inverse、paired 与独立 U/D 的 unmarked `MomentData` |
| `SourcePolynomialCalibration` / `SourceRowEligibility` | 对应 `For` 谓词 | 原角色、完整理想零掩码、所有多项式及行资格条件 |
| `WholeMomentProfileControl` | `WholeMomentProfileControlFor` | 原 J/A、T、实平移 8、虚平移 1+‖ξ‖ 区域保留；同步 #10 的 ideal tests 与 prime windows |
| `UniformMomentBound` 中索引隐含未构造 actual 选择 | `UniformMomentBoundFor` | 固定 E 与模型后才选择 A、ceiling，然后 τ、Z₀、k |
| named model、energy 与 calibration | actual aliases | 最后且仅一次以 `expansionRecipeRaw K c` 实例化 |

`MomentSourceData K c` 固定完整的 `ℝ → ℝ → HighExpansion` 和行枚举指数。
它不含能量估计、spike、profile 估计或无零点结论。
`momentBlockFor`、`momentAmplitudeFor`、`momentWitnessFor`、`momentBaseFor`、
`rowWidthFor`、`selectedLengthFor` 与所有参数、能量定义都引用这一份 E。

保留物理 capacity 的右端 1；真实行壳层仍使用 `U < N(u) ≤ 2U`，故模型枚举
宽度为 `1 + log 2 / log U`。矩多项式的长度基底仍是 U。

profile 内容使用 #10 的独立 `Moments.UniformAmplify.ModelProfileControl`，包含 inverse、
两个 plain profiles 及所有 prime windows；这是 #10 已完成的共享定义修正。
该模块本身不导入总 `Moments.lean`，因此没有反向依赖。

## 真实 recipe 的显式适配器

`HeckeSkeleton/ExpansionModels/SourceData.lean` 的每一个构造都接受明确的同一份
`RecipeExpansion R`：

- `recipeMomentSourceData K c R`：R 的全尺度展开和 dyadic 行宽度。
- `recipeMomentModels K c R`：R 的同一个 family、physical point、witness 参数生成
  inverse、paired、unmarked 三个真实模型。
- `recipeMoment_polynomial_calibration K c R`：八项字面校准。素数槽等式使用原
  `selectedSlotProduct` 变基和有限乘积定理；其余保持原系数与完整零掩码。
- `recipeMomentBase_ge_two` / `recipeMoment_rowWidth_spec`：所有 active source index
  的 U≥2，以及 `U^rowWidth=2U`。
- `recipeMomentModels_geometry`：R 的 `MomentGeometry L` 给出同一 source 的统一
  plain-length 范围和真实 evaluation 参数的 admissibility。

`SourceMomentParameterControlFor` 只陈述实际 heights/shifts 落在原 profile 区域。
`WholeMomentProfileControlFor.evaluated` 将这个几何事实代入原 profile 控制，保持原始
物理高度 T。这里没有用任意重参数化吸收未知的高度或平移。

## 论文对应与最终目标

固定背景/扇区的选择顺序对应根目录论文 1518–1526 行，profile 家族对应 1554–1559 行，
固定数据下的 paired 矩定理对应 1655–1679 行，witness 分块和长度对应 3756–3793 行，
实际 PSource 与 noSlots 对应 3795–3828 行。

这个修改抽出了原来已经需要固定的数据，没有改变一般数域 Hecke L 函数在
`Re(s)>7/8` 无零点的顶层结论。`Moments.lean` 的原公开名称保留为相同数据的 actual
aliases。泛型接口、recipe 适配器与实际 raw recipe 的构造是分别核验的事项；前两者
不替代 D-EXPANSION 及实际全局积分识别。

## 核验入口

目标模块为 `HeckeSkeleton.SourceData`、
`HeckeSkeleton.ExpansionModels.SourceData` 和兼容端 `HeckeSkeleton.Moments`。
新模块内打印关键声明的公理，正式结果由本 PR 的编译与逐声明审计记录给出。
