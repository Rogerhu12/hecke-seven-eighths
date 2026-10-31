# THETA_GLOBAL：精确声明、局部输入与下游接口

本报告对照本轮仓库真实源码，列出五个原始目标、全部新增局部输入、同一次算术选择和七个下游接口。代码块中的声明与字段从所列源文件逐字提取；若只展示声明头，会明确标为“声明头”，并省略证明体而不改动参数。

原任务明确允许将阿基米德高 K-型向量、Mellin 对、乘子恒等式及外部素位数字表写成显式假设。以下 `L`、`H` 就是这条允许的局部边界。它们的存在性不是本报告新增的结论。

目标环境：Lean `4.35.0-rc3`，Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。本报告记录声明与依赖边界；本轮原生编译、公理检查的结果须以单独保存的实际日志为准。这里不预先宣称未完成的检查通过。

## 1. 固定上下文与记号

五目标所在命名空间是 `HeckeSkeleton`，不是 `HeckeSkeleton.Theta`。源码：[HeckeSkeleton/Theta.lean](../HeckeSkeleton/Theta.lean)。共同环境逐字为：

```lean
namespace HeckeSkeleton
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)
local notation "S" => places K c
local notation "P" => probeData K c
local notation "D" => (probeData K c).arithmetic
local notation "θ" => thetaPeriod K S P (targetCharacter K c)
```

`c : TargetContext K` 的原有条件全部如下。`FamilyContext.boundary` 是既有 family 零点实部上界条件；这里完整列出，避免将它藏在上下文名下。theta 构造没有把待证的 theta 反射恒等式放入这个上下文。源码：[HeckeSkeleton/Base.lean](../HeckeSkeleton/Base.lean)。

```lean
structure FamilyContext where
  root12 : K
  primitive12 : IsPrimitiveRoot root12 12
  omega : HeckeCharacter K
  B : ℝ
  B_lower : 7 / 8 < B
  B_upper : B ≤ 1
  boundary : ∀ χ : HeckePacketIndex K omega, ∀ r ∈ heckePacketZeros K omega χ,
    1 / 2 ≤ r → r ≤ 1 → r ≤ B
  lamA : ℝ
  lamA_pos : 0 < lamA
  lamA_small : lamA ≤ 1 / 1000
```

```lean
def momentMesh (c : FamilyContext K) : {m : ℝ // 0 < m} :=
  ⟨HeckePort.Schedule.momentMeshValue c.lamA, HeckePort.Schedule.momentMeshValue_pos c.lamA_pos⟩
```

```lean
structure TargetContext where
  family : FamilyContext K
  geometry : PrimeWindowGeometry
  mesh_fine : (1 / 3 : ℝ) / geometry.slots ≤ (momentMesh K family).val
  lamB : ℝ
  lamB_pos : 0 < lamB
  target : HeckePacketIndex K family.omega
```

这些记号使用同一次 `axiomChoice K c`。`S` 是其有限素位集，`D` 是其 theta 算术数据；`P` 包含同一算术数据、修正字符与测试。`θ` 是实际 `thetaPeriod`，不是另选的 Hecke 字符。相关原定义如下：

```lean
def excludedPlaces (c : TargetContext K) :
    Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  (axiomChoice K c).places
```

```lean
abbrev places (c : TargetContext K) :=
  (excludedPlaces K c : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
```

```lean
def arithmeticData (c : TargetContext K) : ThetaArithmeticData K (places K c) :=
  (axiomChoice K c).thetaData
```

```lean
def signalCharacters (c : TargetContext K) : HeckeCharacter K × HeckeCharacter K :=
  ((axiomChoice K c).Lambda, (axiomChoice K c).G)
```

```lean
def probeData (c : TargetContext K) : ProbeData K (places K c) where
  arithmetic := arithmeticData K c
  Lambda := (signalCharacters K c).1
  G := (signalCharacters K c).2
  additive := (probeTests K c).1
  denominator := (probeTests K c).2
```

```lean
abbrev targetCharacter (c : TargetContext K) : HeckeCharacter K :=
  (representative K c).val.val
```

```lean
def thetaPeriod (P : ProbeData K S) (ψ : HeckeCharacter K) : HeckeCharacter K :=
  conjugate P.Lambda * conjugate P.G * ψ
```

最后一段定义位于 `HeckeGeneral.ThetaSkeleton.Physical`，继承其原有 `K`、`S` 上下文。下面五目标中的 `F` 是 **finite Mellin 数据的局部记号**，不是新的数域参数：

```lean
variable (L : LocalHighKMellinInput K c)
local notation "F" => finiteMellinData K c L
```

## 2. 五个原始目标的完整源码声明

本节保留声明的实际证明体。它们与上一节的 `K`、`c`、局部记号及 section 参数共同阅读。`finiteMellinData` 自己绑定 `L`；其余四项继承上文的 `L`。

### 2.1 TH-KP-DATA

```lean
def finiteMellinData (L : LocalHighKMellinInput K c) : FiniteMellinData K S :=
  FiniteSkeletonSource.data K c L
```

### 2.2 TH-FINITE-VALUATION-CUTOFF

```lean
theorem finite_valuation_cutoff : ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ → (finiteMellinData K c L).coefficient u κ l p k = 0 :=
  (FiniteSkeletonSource.admissible K c L).valuation_cutoff
```

### 2.3 TH-FINITE-VALUATION-DECAY

```lean
theorem finite_valuation_decay : ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ u κ l p k, 0 ≤ k →
      ‖(finiteMellinData K c L).coefficient u κ l p k‖ ≤ C * (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ) :=
  (FiniteSkeletonSource.admissible K c L).valuation_decay
```

### 2.4 TH-MARKED-REFLECTED-ABSOLUTE

```lean
theorem marked_reflected_absolute : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    Summable (fun i : ReflectionIndex K S d => reflectedTerm K S D d i F θ V.toFun X) := by
  intro d V X hX
  exact ThetaGlobal.ReflectedAbsoluteProject.marked_reflected_absolute K S D d F θ
    (mellinKernel K c L) V hX
```

### 2.5 TH-MARKED-REFLECTION

```lean
theorem marked_reflection (H : LocalExteriorDigitInput K c)
    (hkernel : MellinKernelInput K S F θ) : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X =
      ∑' i : ReflectionIndex K S d, reflectedTerm K S D d i F θ V.toFun X := by
  intro d V X hX
  obtain ⟨w, hw, hk⟩ := marked_angular_nonzero K c
  exact thetaFiniteSource_marked_reflection K c L H (allowedGenerators K c)
    (marked_conductor_subset K c) w hk d V hX
```

截断与衰减中隐式推断的索引类型为：`u : SixthUnitClasses K S`，`κ : SixthLocalClasses K S`，`l : Fin F.terms`，`p : S`，`k : ℤ`；衰减指数 `δ` 与常数 `C` 为实数。两条级数声明中的 `X` 是正实数，测试 `V` 是原 `SmoothAnnularTest`，反向求和索引保持原 `ReflectionIndex K S d`。

`marked_reflection` 保留显式参数 `hkernel : MellinKernelInput K S F θ`。当前证明体从 `L` 构造核输入，未使用传入的 `hkernel`；公共打包入口用已证明的 `mellinKernel K c L` 填充它。故打包入口只新增 `L`、`H` 两个独立局部输入：

```lean
theorem markedReflection (H : LocalExteriorDigitInput K c) :
    MarkedCoefficientReflectionInput K S D F θ where
  allowed_generators := allowedGenerators K c
  exterior_unramified := marked_exterior_unramified K c
  angular_nonzero := marked_angular_nonzero K c
  kernel := mellinKernel K c L
  completed_absolute := marked_completed_absolute K c
  reflected_absolute := marked_reflected_absolute K c L
  reflection := marked_reflection K c L H (mellinKernel K c L)
```

## 3. 同一次 source 与 RootAligned 的嵌入调整

原附件中的 `Base.complexEmbedding` 由 `Classical.arbitrary` 选择。任意复嵌入并不保证把给定的十二次单位根送到 KP 的固定复根。本实现把顺序写成：**先对齐 `c.family.root12` 的复嵌入，再对该嵌入选择一次算术上下文；后续 recipe、source、有限表和系数识别均使用这一次选择。**

这是本任务对已有 `Base` 选择方式的明确调整，不是把任意嵌入自动视为已对齐。当前源码为：

```lean
def complexEmbedding (c : TargetContext K) : K →+* ℂ :=
  ThetaGlobal.GlobalEmbedding.alignedEmbedding c.family.root12 c.family.primitive12
```

```lean
def axiomChoice (c : TargetContext K) :
    HeckeAxiom.ArithmeticChoice K (targetRamifiedPlaces K c) c.family.root12
      (complexEmbedding K c) :=
  ThetaGlobal.GlobalChoice.alignedChoice (targetRamifiedPlaces K c)
    c.family.root12 c.family.primitive12
```

```lean
theorem axiomChoice_modulus_top (c : TargetContext K) :
    (axiomChoice K c).A.modulus = ⊤ :=
  ThetaGlobal.GlobalChoice.alignedChoice_modulus (targetRamifiedPlaces K c)
    c.family.root12 c.family.primitive12
```

```lean
theorem axiomChoice_rootAligned (c : TargetContext K) :
    complexEmbedding K c (axiomChoice K c).A.zeta12 =
      ThetaGlobal.GlobalEmbedding.canonicalTwelfthRoot :=
  ThetaGlobal.GlobalProjectEmbedding.choice_root12 (axiomChoice K c)
```

```lean
theorem axiomChoice_coefficientEmbedding (c : TargetContext K) (z : rootsOfUnity 6 K) :
    complexEmbedding K c ((z : Kˣ) : K) =
      (DedekindZetaZeroFree.KPLocalCover.coefficientEmbedding K
        (axiomChoice K c).A.zeta12 (axiomChoice K c).A.primitive_zeta12 z : ℂ) :=
  ThetaGlobal.GlobalProjectEmbedding.choice_coefficientEmbedding (axiomChoice K c) z
```

`canonicalTwelfthRoot`、对齐嵌入和 `RootAligned` 的定义如下。`RootAligned` 的准确命名空间是 `DedekindZetaZeroFree.MomentSources`，其条件比较所有六次单位根上的嵌入值。它在固定 skeleton 入口是结论，不是新增用户假设。

```lean
def canonicalTwelfthRoot : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 12)
```

```lean
def alignedEmbedding (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : F →+* ℂ :=
  Classical.choose (exists_alignedEmbedding ζ hζ)
```

```lean
def RootAligned {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) : Prop :=
  ∀ z : rootsOfUnity 6 F, R.σ ((z : Fˣ) : F) =
    (KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 z : ℂ)
```

`GlobalChoice.exists_arithmeticChoice_top` 保留原算术存在性构造的 `A.modulus = ⊤`，供实际 principal continuation 使用；`GlobalSameChoice.recipe` 的 `A` 和 `σ` 就是所传入选择的数据，其 allowed generators 与 correction 也通过精确等式绑定到同一 `X`。固定入口逐字如下：

```lean
def thetaRecipe : PrincipalMellin.ActualRecipe (axiomChoice K c).A (axiomChoice K c).η :=
  ThetaGlobal.GlobalSameChoice.recipe (axiomChoice K c) (axiomChoice_modulus_top K c)
```

```lean
theorem thetaRecipe_aligned : RootAligned (thetaRecipe K c) :=
  axiomChoice_coefficientEmbedding K c
```

```lean
def thetaFiniteSource : ThetaGlobal.FiniteFixedSource.Source (thetaRecipe K c)
    (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c)) :=
  ThetaGlobal.FiniteFixedSource.source (thetaRecipe K c) (thetaRecipe_aligned K c)
    (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))
```

```lean
abbrev LocalHighKMellinInput := ThetaGlobal.FiniteLocalHighK.Input (thetaRecipe K c)
  (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c)) (thetaFiniteSource K c)
```

`thetaFiniteSource` 的构造先于 `L`。其中 `Source` 确实记录全局 source 的 factorization/transport 性质，但它由 `source_nonempty` 构造，固定入口没有把任意 `Source` 当作用户输入。以下声明位于 `ThetaGlobal.FiniteFixedSource`，继承的泛型参数完整为：

```lean
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
```

其实际结构和选择定义为：

```lean
structure Source (R : PrincipalMellin.ActualRecipe S η)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) where
  transport : TraceHaarTransport R
  spherical : FirstRootSphericalSeed R transport
  initialCutoffs : FirstRootCutoffs R
  projected : FirstRootProjected R transport spherical initialCutoffs
  target_kernel : ∀ p z, z ∈ projected.cutoffs.cutoff p →
    HeckeGeneral.Characters.localComponent F p.val θ z = 1
  native : SourceNativeLie R projected.base.factorization
  fullArchProduct : FiniteFullProduct.FullArchProduct R projected.base.factorization
  localArchRatio : FiniteFullProduct.LocalArchRatio R projected.base.factorization
```

```lean
theorem source_nonempty (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) : Nonempty (Source R θ)
```

上一块是 `source_nonempty` 的完整声明头，省略已实现的证明体。选择本身为：

```lean
def source (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) : Source R θ :=
  Classical.choice (source_nonempty R hR θ)
```

## 4. L：全部单处高 K-型与 Mellin 输入

准确类型是 `ThetaGlobal.FiniteLocalHighK.Input R θ C`，skeleton 别名是 `HeckeSkeleton.LocalHighKMellinInput K c`。它是携带向量、functional、尺度、常数及性质的数据结构，不是只有存在性判断的命题。

源文件：[ThetaGlobal/FiniteLocalHighK.lean](../ThetaGlobal/FiniteLocalHighK.lean)。以下原文先列实际局部表示与 profile，使后面的所有字段可直接核查。这里的 `F` 是泛型数域，`S : SArithmeticData F`，与第 1 节的有限位集合记号有不同作用域。

```lean
namespace ThetaGlobal.FiniteLocalHighK

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.KPCplxCharacterHaar
open DedekindZetaZeroFree.FourierContinuation.ComplexLines
open DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (θ : HeckeCharacter F) (C : FiniteFixedSource.Source R θ)

def localArgument (w : InfinitePlace F) (reflected : Bool) (z : w.Completionˣ) : ComplexPGL2 :=
  Matrix.ProjGenLinGroup.mk
    (KPCplxCharacterHaar.diagonal
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (R.A.complex_place w)).toMonoidHom z) * if reflected then weyl else 1)

def localProfile
    (M : KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ)
    (φ : KPGlobalResidualConstruction.complexCore)
    (w : InfinitePlace F) (reflected : Bool) (z : w.Completionˣ) : ℂ :=
  (if reflected then (infiniteComponent F w θ z : ℂ)⁻¹
    else (infiniteComponent F w θ z : ℂ)) *
    M (KPCplxActualImage.imageAction traceFrequency (localArgument R w reflected z)
      (harmonicInclusion φ)) / M (harmonicInclusion φ)
```

两个 Gamma pair 的定义为：

```lean
def gammaPair (w : InfinitePlace F) (s : ℂ) : ℂ :=
  Complex.Gamma ((archShift F θ ⟨w, R.A.complex_place w⟩ : ℂ) + s +
    Complex.I * archRadial F θ ⟨w, R.A.complex_place w⟩ + 1 / 6) *
  Complex.Gamma ((archShift F θ ⟨w, R.A.complex_place w⟩ : ℂ) + s +
    Complex.I * archRadial F θ ⟨w, R.A.complex_place w⟩ - 1 / 6)

def directGammaPair (w : InfinitePlace F) (s : ℂ) : ℂ :=
  Complex.Gamma ((archShift F θ ⟨w, R.A.complex_place w⟩ : ℂ) + s -
    Complex.I * archRadial F θ ⟨w, R.A.complex_place w⟩ + 1 / 6) *
  Complex.Gamma ((archShift F θ ⟨w, R.A.complex_place w⟩ : ℂ) + s -
    Complex.I * archRadial F θ ⟨w, R.A.complex_place w⟩ - 1 / 6)
```

`Input` 的字段完整逐字如下：

```lean
structure Input where
  vector : InfinitePlace F → KPGlobalResidualConstruction.complexCore
  functional : InfinitePlace F → KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ
  whittaker : ∀ w, functional w ∈
    KPCplxWhittakerUnique.whittakerSpace traceFrequency traceCharacter
  functional_nonzero : ∀ w, functional w (harmonicInclusion (vector w)) ≠ 0
  source_nonzero : ∀ w, C.projected.base.factorization.ell (Sum.inl w) (vector w) ≠ 0
  scale : InfinitePlace F → ℝ
  scale_pos : ∀ w, 0 < scale w
  directConstant : InfinitePlace F → ℂ
  directConstant_nonzero : ∀ w, directConstant w ≠ 0
  reflectedConstant : InfinitePlace F → ℂ
  reflectedConstant_nonzero : ∀ w, reflectedConstant w ≠ 0
  direct_integrable : ∀ (w : InfinitePlace F) (s : ℂ), -(1 / 3 : ℝ) < s.re →
    Integrable (fun z : w.Completionˣ =>
      localProfile R θ (functional w) (vector w) w false z *
        ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s)
      (archHaar R.A w (C.transport.angularHaar w))
  reflected_integrable : ∀ (w : InfinitePlace F) (s : ℂ), -(1 / 3 : ℝ) < s.re →
    Integrable (fun z : w.Completionˣ =>
      localProfile R θ (functional w) (vector w) w true z *
        ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s)
      (archHaar R.A w (C.transport.angularHaar w))
  direct_bound : ∀ (w : InfinitePlace F) (σ : ℝ), -(1 / 3 : ℝ) < σ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : w.Completionˣ,
      ‖localProfile R θ (functional w) (vector w) w false z‖ ≤
        B * (‖z.val‖ ^ 2 : ℝ) ^ (-σ)
  reflected_bound : ∀ (w : InfinitePlace F) (σ : ℝ), -(1 / 3 : ℝ) < σ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : w.Completionˣ,
      ‖localProfile R θ (functional w) (vector w) w true z‖ ≤
        B * (‖z.val‖ ^ 2 : ℝ) ^ (-σ)
  direct_mellin : ∀ (w : InfinitePlace F) (s : ℂ), -(1 / 3 : ℝ) < s.re →
    (∫ z : w.Completionˣ,
      localProfile R θ (functional w) (vector w) w false z *
        ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s ∂archHaar R.A w (C.transport.angularHaar w)) =
      directConstant w * (scale w : ℂ) ^ s * directGammaPair R θ w s
  reflected_mellin : ∀ (w : InfinitePlace F) (s : ℂ), -(1 / 3 : ℝ) < s.re →
    (∫ z : w.Completionˣ,
      localProfile R θ (functional w) (vector w) w true z *
        ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s ∂archHaar R.A w (C.transport.angularHaar w)) =
      reflectedConstant w * (scale w : ℂ) ^ s * gammaPair R θ w s
```

这里 `traceFrequency`、`traceCharacter` 和 `harmonicInclusion` 均是 `DedekindZetaZeroFree.FourierContinuation.ComplexLines` 中的实际对象；`traceFrequency` 为正实频率 `4π`。`localArgument` 是实际 diagonal 与 Weyl 元的作用；`source_nonzero` 是同一个已构造 source 的单处 functional 非零条件。

每个 integrability/bound/Mellin 字段只量化一个 infinite place 的 completed representation 和该处 Haar 积分。全局 sheet 积分、global seed、最终 marked reflection 与理想级数收敛均不是字段。`scale_pos`、两个常数的非零性和 `source_nonzero` 属于本次采用的完整局部高 K-型包，不能在报告中省略。

### 4.1 正反字符方向

由上述真实定义，正向 profile 乘 `θ`，反向 profile 乘 `θ⁻¹`；同时 `archRadial = -heckeComplexParameter`。因此正向 Gamma product 是 `archGammaProduct θ⁻¹`，反向是 `archGammaProduct θ`。本轮新增 `ThetaGlobal.LocalGammaOrientation` 将其写成无额外 Mellin 假设的正式恒等式。

若接入一个“direct profile 乘逆字符”的局部接口，应把该接口实例化于 `θ⁻¹`。这解释了局部分支不同 direct 命名与本分支原乘子的关系；不需要改动 `GlobalThetaData.reflectionMultiplier`。本段的符号桥原生编译状态仍以实际审计日志为准。

## 5. H：全部单处 exterior digit 输入

准确类型是 `ThetaGlobal.GlobalProjectLocalDigitTables.Input R D Adata`；这里 `D` 是 **实际 source factorization**，不是第 1 节中 theta arithmetic datum 的记号。固定入口中的对应关系完整为：

```lean
local notation "R" => thetaRecipe K c
local notation "Sf" => places K c
local notation "Adata" => arithmeticData K c

/-- The permitted exterior table is evaluated on the source selected
before the local high K-type vector is supplied. -/
abbrev LocalExteriorDigitInput :=
  GlobalProjectLocalDigitTables.Input R
    (thetaFiniteSource K c).projected.base.factorization Adata
```

源文件：[ThetaGlobal/GlobalProjectLocalDigitTables.lean](../ThetaGlobal/GlobalProjectLocalDigitTables.lean)。它的泛型上下文及右端实际局部值定义为：

```lean
namespace ThetaGlobal.GlobalProjectLocalDigitTables

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.OrbitExpansion
open DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectDigitProduct ThetaGlobal.GlobalProjectSignedExtraction
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

def skeletonPrime (p : P) : ExteriorPrime F Sf := ⟨p.val, p.property⟩

variable (Adata : ThetaArithmeticData F Sf)

def unitPhase (p : P) (x : Fˣ) : ℂ :=
  thetaPrimeCharacter F Sf Adata (skeletonPrime R p)
    (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x))

def sphericalValue (p : P) (x : Fˣ) : ℂ :=
  if ThetaBranch.order p.val x < 0 then 0 else
    sphericalDigit F Sf Adata (skeletonPrime R p) (ThetaBranch.order p.val x).toNat *
      unitPhase R Adata p x ^ (2 * (ThetaBranch.order p.val x).toNat)

def activeValue (p : P) (j : Fin 6) (x : Fˣ) : ℂ :=
  if ThetaBranch.order p.val x + 2 < 0 then 0 else
    localWeylScalar F Sf Adata (skeletonPrime R p) j
      (ThetaBranch.order p.val x + 2).toNat *
      unitPhase R Adata p x ^ localWeylExponent j (ThetaBranch.order p.val x + 2).toNat

def markedActive (p : P) (x : Fˣ) : ℂ :=
  if ThetaBranch.order p.val x = -2 then
    (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
      thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2 *
      unitPhase R Adata p x ^ 2
  else 0
```

字段中使用的 `localDigit` 定义位于 `ThetaGlobal.GlobalProjectDigitProduct`。它直接评价实际 source 的 exterior slot，矩阵参数是 `A(x) W N(-t/gₚ)`：

```lean
def localDigit (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (t : 𝓞 F) : ℂ :=
  exteriorSlotValue R D p.val
    (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (-algebraMap (𝓞 F) (p.val.adicCompletion F) t /
          algebraMap F (p.val.adicCompletion F)
            (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)))
```

`Input : Prop` 的字段完整逐字如下：

```lean
structure Input : Prop where
  diagonal : ∀ (p : P) (x : Fˣ), D.exteriorValue R p x = sphericalValue R Adata p x
  nonzero_digits : ∀ (p : P) (j : Fin 6) (x : Fˣ)
      (L : ThetaDigitAverage.Residue p.val → 𝓞 F),
      (∀ t, Ideal.Quotient.mk p.val.asIdeal (L t) = t) →
      (∑ t ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val),
        digitMask F Sf Adata (skeletonPrime R p) j t * localDigit R D p x (L t)) =
        activeValue R Adata p j x
  zeroth_weyl : ∀ (p : P),
      -localWeylScalar F Sf Adata (skeletonPrime R p) 0 0 =
        (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
          thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2
  forward_mask : ∀ (p : P) (j : Fin 6) (t : ThetaDigitAverage.Residue p.val),
      (∑ v : ThetaDigitAverage.Residue p.val,
        digitMask F Sf Adata (skeletonPrime R p) j v * Characters.psi R p (t * v)) =
        if t = 0 then 0 else thetaPrimeCharacter F Sf Adata (skeletonPrime R p) t ^ j.val
```

这里 `Characters.psi` 指 `DedekindZetaZeroFree.MomentSources.Characters.psi`，源自实际 `PrincipalMellinSource.exists_primitive_source_characters R`；其原定义为：

```lean
def psi (p : ThetaBranch.ExteriorPrime R.A) : AddChar (DHCubic.Residue F p.val) ℂ :=
  (PrincipalMellinSource.exists_primitive_source_characters R).choose p
```

`nonzero_digits` 中名为 `L` 的量是一个任意满足 residue-lift 条件的函数，和第 4 节的高 K-型数据 `L` 是不同的局部绑定变量。每条字段只涉及一个 exterior prime。零 residue 由 compact invariance 推出；marked average 由 `q⁻¹ = δ₀ - digitMask₀` 推出；有限乘积、active-set 展开和最终频率重排均在输入之外证明。

## 6. 实际有限表的归一化与壳层积分规格

`HeckeSkeleton.FiniteSkeletonSource.data K c L` 就是 `HeckeSkeleton.finiteMellinData K c L` 的实现。其 `C₀`、`A₀` 来自同一 source 的 cutoff volume 和 `L` 的局部常数，而不是额外任选的参数。以下原文在 `HeckeSkeleton.FiniteSkeletonSource` 内，继承 `K`、`c`、`L`：

```lean
local notation "R" => thetaRecipe K c
local notation "C" => thetaFiniteSource K c
local notation "D" => C.projected.base.factorization
local notation "θ" => thetaPeriod K (places K c) (probeData K c) (targetCharacter K c)

theorem data_C₀ : (data K c L).C₀ =
    (ThetaGlobal.FiniteDirectMellin.cutoffVolume R C.transport C.projected.cutoffs : ℂ) *
      (∏ w : InfinitePlace K, L.directConstant w) /
      (∏ w : InfinitePlace K, L.reflectedConstant w) := rfl

theorem data_A₀ : (data K c L).A₀ = ∏ w : InfinitePlace K, L.scale w := rfl

def termClass (l : Fin (data K c L).terms) :
    ∀ p : R.A.Sf, ThetaGlobal.ProjectFiniteClass.LocalClass R.A p :=
  ThetaGlobal.ProjectedFiniteMellin.termClassEquiv R D C.transport
    (ThetaGlobal.FiniteLocalHighK.C₀ R θ C L)
    (ThetaGlobal.FiniteLocalHighK.C₀_ne_zero R θ C L)
    (ThetaGlobal.FiniteLocalHighK.A₀ R θ C L)
    (ThetaGlobal.FiniteLocalHighK.A₀_pos R θ C L) θ l
```

上文 `D` 在这个作用域中是 `C.projected.base.factorization`，不是 `arithmeticData`。以下规格保留实际 shell point、class mask、local period、Weyl vector 和 unit Haar：

```lean
theorem coefficient_shell_spec
    (u : SixthUnitClasses K (places K c))
    (κ : SixthLocalClasses K (places K c))
    (l : Fin (data K c L).terms) (p : R.A.Sf) (k : ℤ) :
    (data K c L).coefficient u κ l p k =
      ∫ z,
        (if p = D.scalarSlot then
          ThetaGlobal.ProjectFiniteClass.reflectedClassMask R.A R.probe.correction.B R.σ κ
            (ThetaGlobal.ProjectFiniteClass.assemble R.A (termClass K c L l)) else 1) *
        (if (QuotientGroup.mk (ThetaGlobal.ProjectLocalShell.shellPoint K p.val k z) :
          ThetaGlobal.ProjectFiniteClass.LocalClass R.A p) = termClass K c L l p
          then 1 else 0) *
        (ThetaGlobal.TargetFinitePeriod.localPeriod R θ u p
          (ThetaGlobal.ProjectLocalShell.shellPoint K p.val k z) : ℂ) *
        ThetaGlobal.FiniteCanonicalVectors.weylValue R D p
          (ThetaGlobal.ProjectedFiniteMellin.normalizedSelectedVector R D u p)
          (ThetaGlobal.ProjectLocalShell.shellPoint K p.val k z)
        ∂ThetaGlobal.ProjectedFiniteMellin.unitHaar R C.transport p :=
  ThetaGlobal.ProjectedFiniteMellin.targetCoefficient_enumerated_spec R D C.transport
    (ThetaGlobal.FiniteLocalHighK.C₀ R θ C L)
    (ThetaGlobal.FiniteLocalHighK.C₀_ne_zero R θ C L)
    (ThetaGlobal.FiniteLocalHighK.A₀ R θ C L)
    (ThetaGlobal.FiniteLocalHighK.A₀_pos R θ C L) θ u κ l p k
```

这是原 TASK 要求的“有限系数等于局部壳层积分”规格，后续反射始终使用这一张表。前面只有 `p : R.A.Sf` 的 local Borel instances 被用于读取该积分；没有额外的系数实现假设。

## 7. 七个下游消费者的新参数映射

这一节记录接线兼容性。它保留仓库其他任务的原有 obligations，不把整条 seven-eighths endpoint 的源码装配当作已无 admission 的数学证明。

下表的全部名称都在 `HeckeSkeleton` 命名空间。`K`、`c` 参数按源文件 section 自动纳入；最终全域 endpoint 不额外带外层 `K` 参数，因为它的签名直接量化 `F`。

| 消费者 | 本次局部输入及依赖类型变化 | 实际调用/传递 |
| --- | --- | --- |
| `completedMarkedEnergy` | 新增 `L`；已有 `hreflection` 改用同一 `finiteMellinData K c L` | `completedMarkedEnergy K c L (markedReflection K c L H)` |
| `principalSource` | 新增 `L`、`H` | 将上述 reflection package 传给 completed-energy 接口 |
| `canonical_inverse_models` | 新增 `L`；保留 `hcal`、`hrows`、`hprofiles`、`hquadratic`、`hcubic`；已有 `hreflection` 改用同一 `finiteMellinData K c L` | `canonical_inverse_models K c L hcal hrows hprofiles (moment_quadratic_sieve K c) (moment_cubic_sieve K c) (markedReflection K c L H)` |
| `inverseSource` | 新增 `L`、`H` | 用上述 canonical inverse-model 调用构造 `ISource` |
| `sourceT` | 新增 `L`、`H` | `principal := principalSource K c L H` |
| `familyInputs` | 新增逐 `TargetContext K` 的 `localData` 和 `localDigits` | 对每个 `c` 同时传给 `sourceT`、`inverseSource` |
| `generalHeckeSevenEighths_skeleton` | 新增对每个数域和每个 `c` 的 `Nonempty (LocalHighKMellinInput F c)` 与 `LocalExteriorDigitInput F c` | 在 descent extension 上用 `Classical.choice` 取得局部数据，传给 `familyInputs` |

前六项的完整声明头如下；证明体不重印。Principal 的源文件局部记号是：

```lean
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)
local notation "S" => places K c
local notation "P" => probeData K c
local notation "ψ" => targetCharacter K c
local notation "g" => c.geometry
local notation "T" => rayFilter K c
local instance : MeasurableSpace (sLocalNormOneGroup K S) := (probeMeasures K c).normOneSpace
local instance : BorelSpace (sLocalNormOneGroup K S) := (probeMeasures K c).normOneBorel
local instance (p : S) : MeasurableSpace (p.val.adicCompletion K) := (probeMeasures K c).localSpace p
local instance (p : S) : BorelSpace (p.val.adicCompletion K) := (probeMeasures K c).localBorel p
local notation "μ" => (probeMeasures K c).haar
local instance (p : S) : (μ p).IsAddHaarMeasure := (probeMeasures K c).haar_isAddHaar p
```

```lean
theorem completedMarkedEnergy (L : LocalHighKMellinInput K c)
    (hreflection : MarkedCoefficientReflectionInput K S (probeData K c).arithmetic
      (finiteMellinData K c L) (thetaPeriod K S P ψ)) : CompletedMarkedEnergy K c
```

```lean
theorem principalSource (L : LocalHighKMellinInput K c)
    (H : LocalExteriorDigitInput K c) :
    (probeMeasures K c).principalInput P ψ g T
```

```lean
theorem canonical_inverse_models (L : LocalHighKMellinInput K c)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c) (hcubic : CubicSieveBound K c)
    (hreflection : MarkedCoefficientReflectionInput K (places K c)
      (probeData K c).arithmetic (finiteMellinData K c L)
      (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))) :
    CanonicalInverseModelBounds (momentModels K c)
```

```lean
theorem inverseSource (L : LocalHighKMellinInput K c)
    (H : LocalExteriorDigitInput K c) :
    ISource c.geometry (targetData K c) c.family.lamA
```

```lean
theorem sourceT (c : TargetContext K) (L : LocalHighKMellinInput K c)
    (H : LocalExteriorDigitInput K c) :
    TSource c.geometry (targetCharacter K c) (targetData K c)
      c.family.B c.family.lamA c.lamB
```

```lean
theorem familyInputs (zeta : K) (hzeta : IsPrimitiveRoot zeta 12)
    (ω : HeckeCharacter K)
    (localData : ∀ c : TargetContext K, LocalHighKMellinInput K c)
    (localDigits : ∀ c : TargetContext K, LocalExteriorDigitInput K c) : TIPInput K ω
```

`canonical_inverse_models` 与 `inverseSource` 继承 `variable (K c)`；`sourceT` 与 `familyInputs` 继承 Main 的 `variable (K : Type) [Field K] [NumberField K]`。对应完整参数顺序和返回类型还由 `verification/theta_global/ConsumerSignatures.lean` 的 typed examples 检查；该文件的消费者公理报告允许原有 `sorryAx`，所以其意义是接口兼容性。

### 7.1 最终 Main 条件 endpoint 的完整声明

源码：[HeckeSkeleton/Main.lean](../HeckeSkeleton/Main.lean)。以下包括完整签名及实际装配证明：

```lean
theorem generalHeckeSevenEighths_skeleton
    (localData : ∀ (F : Type) [Field F] [NumberField F] (c : TargetContext F),
      Nonempty (LocalHighKMellinInput F c))
    (localDigits : ∀ (F : Type) [Field F] [NumberField F] (c : TargetContext F),
      LocalExteriorDigitInput F c) : GeneralHeckeSevenEighths := by
  intro F _ _
  apply Descent.descend F
  intro ω
  exact familyInputs (Descent.Extension F) (Descent.root12 F)
    (Descent.primitive_root12 F) ω (fun c => Classical.choice (localData _ c))
    (fun c => localDigits _ c)
```

结论名 `GeneralHeckeSevenEighths` 的准确展开位于 `HeckeGeneral.Analysis`：

```lean
def HeckeSevenEighths : Prop :=
  ∀ χ : HeckeCharacter K,
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (7 / 8))
```

```lean
def GeneralHeckeSevenEighths : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], HeckeSevenEighths F
```

`GeneralHeckeSevenEighths` 的含义是所有数域、所有实际连续酉 Hecke 字符的 `heckeContinuation` 在 `Re(s) > 7/8` 无 meromorphic zero；其定义仍允许纯 norm 字符导致的极点。Main 的 theorem 当前仍通过其他任务的既有 admissions 依赖 `sorryAx`。本次 THETA_GLOBAL 交付只清除五个指定 theta 目标的对应缺口，并显式传播允许的局部输入。

## 8. 本任务的完成边界与验证记录的解释

原 TASK 允许上述单处假设。因此，完整的 THETA_GLOBAL 任务验收是：五个指定目标在实际项目中完成接线；有限表保有壳层积分规格；全局 seed、测度/积分装配、实际系数识别、支持集重排和 annular transfer 在这条局部边界内推出；固定版本 native 编译与五目标递归公理门实际成功。

`verification/theta_global/EntryAudit.lean` 对五目标拒绝 `sorryAx` 及任何非标准公理。允许的公理仅为 `propext`、`Classical.choice`、`Quot.sound`。新的方向桥若纳入同一门，也应受相同白名单约束。

`verification/theta_global/ConsumerSignatures.lean` 具有不同的核查目的：检查七个下游调用的精确类型，记录包括原有 `sorryAx` 在内的依赖。它不能替代五目标的严格门，也不构成整个 seven-eighths endpoint 的无 admission 证明。

具体通过/失败结果、源码提交与日志链接由最终验证记录补充。本文件不将排队、运行中、旧提交的成功结果或 transformed combined-body 检查转记为本轮 native 成功。

## 9. 声明摘录的源码指纹

下列 SHA-256 标识本报告抽取时读取的源码。它们用于核查逐字声明的来源，不是编译证书。报告若随之后的源文件变动更新，应同步重新核对受影响的声明。

| 源文件 | SHA-256 |
| --- | --- |
| `DedekindZetaZeroFree/Arithmetic/ResidueSymbols/SixthRootAlignment.lean` | `8c04cacf75ff71f02a41d190cea7b3b33d6e04e525a6a5f528d7508ce80e576f` |
| `HeckeGeneral/Analysis/HeckeEndpointTarget.lean` | `df13b15c2eadef1564e7270174f11e435a0dd0f2dac4d8f52c58faa3fa5a19c7` |
| `HeckeGeneral/Analysis/PhysicalProbeData.lean` | `eed80b7917e82014bc94ca60fa34a9eef12bd162ae91adfbe5fe60bacebe13d9` |
| `HeckeSkeleton/Base.lean` | `f39648a385520d311a2f7dc38d396920dd1d68a6fdf8eb92cd80204acccc7150` |
| `HeckeSkeleton/Main.lean` | `d4c8400b3f6d897ac95c2481ebf8206b84ef811ef9a22137dea0d9d842ab5b12` |
| `HeckeSkeleton/Moments.lean` | `0ba968c92f96713eb42fcd6fd5eedba348cc9db1520d11caa3cf99c7ef2f346d` |
| `HeckeSkeleton/Principal.lean` | `7e18f6240a662f5e91629f9802621586b2d402f922a9352c487b6d2595472854` |
| `HeckeSkeleton/Theta.lean` | `499f65b078e1b83373c961b4dd31691f6ff04bf8c76fe67a06cecdbf29772497` |
| `ThetaGlobal/FiniteFixedSource.lean` | `f263975dca7807d0dfdec7bcc76f7a19e53c172d57c371e2a73663e763fc6add` |
| `ThetaGlobal/FiniteLocalHighK.lean` | `136457582ad8ee7cf005e36e8954b5ebc5a2917ef06a11d674c362ade713e16a` |
| `ThetaGlobal/FiniteSkeletonSource.lean` | `a375fb500f836b4245ba992f3e57d00d184f2f9cfee34234416cecbaa6334929` |
| `ThetaGlobal/GlobalEmbedding.lean` | `42d71b175d8208d4e4c072f5d6b3d098a16259ca5e932e0bcbb206ee091b246f` |
| `ThetaGlobal/GlobalProjectDigitProduct.lean` | `811cae13cd2f93d3bf02ed4ccfc79c1ae1d0f789cfaad0f7ef134c8e4fd680b4` |
| `ThetaGlobal/GlobalProjectLocalDigitTables.lean` | `a471c2a5df2cd066fd9d1bc92b2dc72543f369930b612a4a6bedcb377948db17` |
| `ThetaGlobal/GlobalProjectMarkedReflection.lean` | `f5b710c7578f6715bef090f1aba88f29e44a06a292f36f0560c1911dc128f160` |

AI-assisted：OpenAI ChatGPT / GPT-6 Astra Pro，2026-10-31。
