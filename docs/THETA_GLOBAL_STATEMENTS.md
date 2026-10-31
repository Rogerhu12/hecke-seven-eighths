# THETA_GLOBAL：精确声明、规范局部构造与下游接口

**本修订的源码实现已接线，完整原生验证尚未完成。** 五个原始目标使用同一固定 source 的规范阿基米德输入 `L` 和有限位数字证书 `H`；本修订的公开 Theta／Principal／Moments／Main 接口不再要求调用者提供 `L/localData` 或 `H/localDigits`。通用 helper 仍保留相应局部参数，原 `marked_reflection` 的显式 `hkernel` 也保留。

本报告对照仓库实际定义，记录五个原始目标、同一次算术选择、完整的规范局部构造及七个消费者。代码块中的声明与字段取自本修订源码；“声明头”只省略证明体，不改动参数。原 TASK 允许单处高 K-型、Mellin 对、乘子恒等式及外部数字表作为显式输入；本修订进一步用实际局部定理填满这些接口。Main 的其他任务 admissions 仍保留。

目标环境：Lean `4.35.0-rc3`，Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。历史提交 `b45484e24f3d4e28cc8092ff6b296f38f4a0f94f` 的 standalone 检查通过 45 个 transformed source bodies 与 56 条严格公理记录；该检查的 45 个源文件哈希仍与本修订匹配，但其范围不含规范 L 构造，也不能认证完整 native Theta/H 依赖链。证据已归档为 [核查记录](../verification/theta_global/ci_41166970094_standalone.json) 和 [编译日志](../verification/theta_global/ci_41166970094_standalone.log)。`LocalArchHaar` 的独立原生尝试已在 20 分钟预算处停止，结果为 `resource-inconclusive`，没有产生诊断或公理记录；这不是原生通过记录，也未确定 Lean 证明错误。详见 [运行记录](../verification/theta_global/native_local_arch_haar_20261031.json)。`LocalArchBounds` 的独立检查仍在运行。

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
local notation "F" => finiteMellinData K c
```

## 2. 五个原始目标的完整源码声明

本节逐字取自 [HeckeSkeleton/Theta.lean](../HeckeSkeleton/Theta.lean)，保留完整证明体；与上一节的 `K`、`c` 和局部记号共同阅读。`finiteMellinData` 内部选择 `localHighKMellinInput K c`，五项均不再继承 `L`。

### 2.1 TH-KP-DATA

```lean
def finiteMellinData : FiniteMellinData K S :=
  FiniteSkeletonSource.data K c (localHighKMellinInput K c)
```

### 2.2 TH-FINITE-VALUATION-CUTOFF

```lean
theorem finite_valuation_cutoff : ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ → (finiteMellinData K c).coefficient u κ l p k = 0 :=
  (FiniteSkeletonSource.admissible K c (localHighKMellinInput K c)).valuation_cutoff
```

### 2.3 TH-FINITE-VALUATION-DECAY

```lean
theorem finite_valuation_decay : ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ u κ l p k, 0 ≤ k →
      ‖(finiteMellinData K c).coefficient u κ l p k‖ ≤ C * (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ) :=
  (FiniteSkeletonSource.admissible K c (localHighKMellinInput K c)).valuation_decay
```

### 2.4 TH-MARKED-REFLECTED-ABSOLUTE

```lean
theorem marked_reflected_absolute : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    Summable (fun i : ReflectionIndex K S d => reflectedTerm K S D d i F θ V.toFun X) := by
  intro d V X hX
  exact ThetaGlobal.ReflectedAbsoluteProject.marked_reflected_absolute K S D d F θ
    (mellinKernel K c) V hX
```

### 2.5 TH-MARKED-REFLECTION

```lean
theorem marked_reflection (hkernel : MellinKernelInput K S F θ) : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X =
      ∑' i : ReflectionIndex K S d, reflectedTerm K S D d i F θ V.toFun X := by
  intro d V X hX
  obtain ⟨w, hw, hk⟩ := marked_angular_nonzero K c
  exact thetaFiniteSource_marked_reflection K c (localHighKMellinInput K c) (allowedGenerators K c)
    (marked_conductor_subset K c) w hk d V hX
```

截断与衰减中隐式推断的索引类型为：`u : SixthUnitClasses K S`，`κ : SixthLocalClasses K S`，`l : Fin F.terms`，`p : S`，`k : ℤ`；衰减指数 `δ` 与常数 `C` 为实数。两条级数声明中的 `X` 是正实数，测试 `V` 是原 `SmoothAnnularTest`，反向求和索引保持原 `ReflectionIndex K S d`。

`marked_reflection` 保留原显式参数 `hkernel : MellinKernelInput K S F θ`。证明体仍未使用传入的 `hkernel`，而是把同一规范 `localHighKMellinInput K c` 传入原固定源 helper；公共打包入口用 `mellinKernel K c` 填充该参数。有限位证书由已有 `localExteriorDigitInput K c` 构造。`markedReflection K c` 不再接收局部包：

```lean
theorem markedReflection :
    MarkedCoefficientReflectionInput K S D F θ where
  allowed_generators := allowedGenerators K c
  exterior_unramified := marked_exterior_unramified K c
  angular_nonzero := marked_angular_nonzero K c
  kernel := mellinKernel K c
  completed_absolute := marked_completed_absolute K c
  reflected_absolute := marked_reflected_absolute K c
  reflection := marked_reflection K c (mellinKernel K c)
```

## 3. 同一次 source 与 RootAligned 的嵌入调整

原附件 `HeckeSkeleton/Base.lean` 中的 `HeckeSkeleton.complexEmbedding` 由 `Classical.arbitrary` 选择。任意复嵌入并不保证把给定的十二次单位根送到 KP 的固定复根。本实现把顺序写成：**先对齐 `c.family.root12` 的复嵌入，再对该嵌入选择一次算术上下文；后续 recipe、source、有限表和系数识别均使用这一次选择。**

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

`thetaFiniteSource` 的选择先于任何高 K-型向量； `localHighKMellinInput K c` 只在该选择完成后构造 `L`。其中 `Source` 确实记录全局 source 的 factorization/transport 性质，但它由 `source_nonempty` 构造，固定入口没有把任意 `Source` 当作用户输入。以下声明位于 `ThetaGlobal.FiniteFixedSource`，继承的泛型参数完整为：

```lean
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
```

以下 `Source` 结构取自 [ThetaGlobal/FiniteFixedSource.lean](../ThetaGlobal/FiniteFixedSource.lean)，新增的最后一个字段保存已在实际球形构造中得到的连续 Whittaker 限制证书。`source_nonempty` 与 `source` 的参数没有新增假设；后者仍只进行同一次选择：

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
  localWhittakerForms : FiniteFullProduct.LocalWhittakerForms R projected.base.factorization
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

## 4. 已构造的规范 L：全部 17 个单处字段

准确类型是 `ThetaGlobal.FiniteLocalHighK.Input R θ C`，skeleton 别名是 `HeckeSkeleton.LocalHighKMellinInput K c`。它是携带向量、functional、尺度、常数及性质的既有数据结构，字段定义保持不变；本修订为同一固定 source 构造它，而不是给公开入口添加该结构的存在性假设。

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

### 4.1 实际采用的字符方向

由真实定义，正向 `localProfile` 乘 `θ`，反向乘 `θ⁻¹`；`archRadial = -heckeComplexParameter`。正向 Gamma product 因而是 `archGammaProduct θ⁻¹`，反向是 `archGammaProduct θ`。已有 `ThetaGlobal.LocalGammaOrientation` 给出无额外 Mellin 假设的正式恒等式。

本修订实际把 THETA_LOCAL 的逆字符 direct 接口实例化于 `θ⁻¹`。`LocalArchProfile.vector` 的权是该逆字符的 `heckeComplexWeight`；因此原正字符因子消去其 angular weight。以下是定义及两个实际 profile 等式的完整声明头；这里继承 `LocalArchProfile` 的 `R`、`θ`、数域与 recipe 上下文：

```lean
def vector (w : InfinitePlace F) : KPGlobalResidualConstruction.complexCore :=
  traceRootCore (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)
```

```lean
theorem direct_profile (w : InfinitePlace F) (z : w.Completionˣ) :
    FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
      (vector R θ w) w false z =
      HeckeSkeleton.ThetaLocal.Project.directProfile F θ⁻¹
        ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (‖z.val‖ ^ 2) /
          (besselKThird (4 * Real.pi) : ℂ)
```

```lean
theorem reflected_profile (w : InfinitePlace F) (z : w.Completionˣ) :
    FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
      (vector R θ w) w true z =
      HeckeSkeleton.ThetaLocal.Project.reflectedProfile F θ⁻¹
        ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (‖z.val‖ ^ 2) /
          (besselKThird (4 * Real.pi) : ℂ)
```

两侧使用同一 completion-to-complex 等距同构，实际 diagonal/Weyl 的 projective 作用，以及原连续 `thetaJacquetFunctional traceFrequency`。分母是该 functional 在实际向量上的值 `besselKThird (4 * Real.pi)`，不是人为另选的归一化。`GlobalThetaData.reflectionMultiplier` 的定义不变。

### 4.2 七个新增模块的实质证明链

| 新增模块 | 实际证明及接线 |
| --- | --- |
| `ThetaGlobal.LocalArchRootCore` | 用 `harmonicSection_harmonic` 将实际最高权向量放入 `complexCore`，用 Weyl 不变性构造最低权分支，再证明 `harmonicInclusion_traceRootCore` 等于 THETA_LOCAL 的 `archRootVector`。实际 Jacquet 值由 Whittaker 公式计算为正 Bessel 值。 |
| `ThetaGlobal.LocalArchProfile` | 对 `θ⁻¹` 的权选上述 core 向量，沿实际 completion 等距同构和 image action 接到 direct/reflected profile；保留同一非零分母。 |
| `ThetaGlobal.LocalArchHaar` | 推送真实 `archHaar` 的平方范数到 positive-axis Haar，证明它正好乘角向总质量，并用 `dt/t` 密度把原 Mellin 积分运输到 completion units。 |
| `ThetaGlobal.LocalArchMellin` | 将局部 `HasMellin`、profile 恒等式及 Haar 运输组合，得到现有 `Input` 需要的两个可积性和 Mellin 等式，保留角向质量和正确的 Gamma 方向。 |
| `ThetaGlobal.LocalArchBounds` | 从实际 Schlafli 表达式证明 Bessel 反单调性；用已证 Mellin 可积性及区间幂积分给出整个正半轴的逐点幂界。 |
| `ThetaGlobal.LocalArchInput` | 将 profile 界除以实际 Bessel 归一化值，结合 source 保存的连续 Whittaker 证书，填满现有 `Input` 的 17 个字段。 |
| `ThetaGlobal.LocalArchSource` | 在 `thetaFiniteSource K c` 选择完成后，定义 `HeckeSkeleton.localHighKMellinInput K c`；不重新选 source、字符、嵌入或 Haar。 |

前三个 source-record 替换文件是 `FiniteFullProduct`、`FiniteProjectedFullSource`、`FiniteFixedSource`，不计入上述七个新模块。它们保留 `normalized_spherical_factorization_full` 已有的 `SphericalTransportData.localForm`／`restriction`／`whittaker` 信息，经实际坐标运输得到 trace-character functional，并在只改变所选 tensor 的有限位 projector 后保持该信息。证书的完整定义如下；它位于 `ThetaGlobal.FiniteFullProduct`，继承实际 recipe `R` 与实际 factorization `D`：

```lean
def LocalWhittakerForms : Prop :=
  ∀ w : InfinitePlace F,
    ∃ M : KPCplxActualImage.Theta traceFrequency →L[ℂ] ℂ,
      M ∈ KPCplxWhittakerUnique.whittakerSpace traceFrequency traceCharacter ∧
      ∀ v : KPGlobalResidualConstruction.complexCore,
        M (harmonicInclusion v) = D.ell (Sum.inl w) v
```

`FiniteFullProduct.local_value_nonzero_of_whittaker` 先由 `ExteriorWhittakerValues.StoredWhittaker.exists_nonzero_value` 知道存储的 functional 非零，再用 `KPWildComplexWhittakerDictionary.continuousWhittaker_comparison` 把任一实际 Whittaker functional 在指定向量上的非零值传给它。证明不使用 `LocalArchRatio` 来反推自身的非零前提，也不要求所选高 K-型向量已给出一个全局非零 period。固定源的实际调用完整为：

```lean
theorem Source.archimedean_nonzero (R : PrincipalMellin.ActualRecipe S η)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) (C : Source R θ)
    (w : InfinitePlace F)
    (M : KPCplxActualImage.Theta FourierContinuation.ComplexLines.traceFrequency →L[ℂ] ℂ)
    (hM : M ∈ KPCplxWhittakerUnique.whittakerSpace
      FourierContinuation.ComplexLines.traceFrequency FourierContinuation.ComplexLines.traceCharacter)
    (v : KPGlobalResidualConstruction.complexCore)
    (hv : M (FourierContinuation.ComplexLines.harmonicInclusion v) ≠ 0) :
    C.projected.base.factorization.ell (Sum.inl w) v ≠ 0 :=
  FiniteFullProduct.local_value_nonzero_of_whittaker R C.projected.base.factorization
    C.localWhittakerForms w M hM v hv
```

### 4.3 Haar、Mellin 常数和逐点界

设 `ν = C.transport.angularHaar w`。此构造不把其总质量假定为 `1` 或 `2π`；紧群 Haar 的已有性质给出 `(ν Set.univ).toReal > 0`。`LocalArchHaar.radial_hasMellin` 的完整声明头为：

```lean
theorem radial_hasMellin (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) [IsFiniteMeasure ν] (f : ℝ → ℂ) (s m : ℂ)
    (hf : HasMellin f s m) :
    Integrable (fun z : w.Completionˣ =>
      f (normSq w z) * (normSq w z : ℂ) ^ s) (archHaar A w ν) ∧
      (∫ z : w.Completionˣ, f (normSq w z) * (normSq w z : ℂ) ^ s
        ∂archHaar A w ν) = ((ν Set.univ).toReal : ℂ) * m
```

以下两项是 `LocalArchMellin` 的实际定义，继承 `R`、`θ` 与 `N : TraceHaarTransport R`：

```lean
def directConstant (w : InfinitePlace F) : ℂ :=
  ((N.angularHaar w Set.univ).toReal : ℂ) *
    archDirectConstant (4 * Real.pi)
      (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)
      (heckeComplexParameter F w (R.A.complex_place w) θ⁻¹) /
    (besselKThird (4 * Real.pi) : ℂ)
```

```lean
def reflectedConstant (w : InfinitePlace F) : ℂ :=
  ((N.angularHaar w Set.univ).toReal : ℂ) *
    archReflectedConstant (4 * Real.pi)
      (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)
      (heckeComplexParameter F w (R.A.complex_place w) θ⁻¹) /
    (besselKThird (4 * Real.pi) : ℂ)
```

每处尺度取 `archScale (4 * Real.pi)`，原 `archScale c = 4 / c ^ 2`。`direct_mellin` 在 `s.re > -1/3` 返回实际 Haar 可积性与正向等式，Gamma factor 是 `directGammaPair R θ w s`；`reflected_mellin` 返回反向等式，Gamma factor 是 `gammaPair R θ w s`。同一 `ν` 的质量、同一 Bessel 分母都进入常数。

逐点界不是新增局部假设。令 `a = archWeight m + σ`，`σ > -1/3` 与 `archWeight m ≥ 1/2` 给出 `a > 0`。实际 profile 的范数是 `t ^ archWeight m * KThird (c * sqrt t)`；径向酉扭曲的范数为一。已证 Mellin 可积性给出有限积分 `M = ∫₀∞ u^(a-1) KThird(c√u) du`。Schlafli 积分给出 K 的反单调性，故对 `0 < u ≤ t` 可用 `KThird(c√t)` 作下界，再结合 `∫₀ᵗ u^(a-1) du = t^a/a`，推出 `t^a KThird(c√t) ≤ a*M`。此证明以 `B = a*M ≥ 0` 得到完整正半轴幂界；反向只是把径向参数换成负值。其声明头逐字为：

```lean
theorem archDirectProfile_bound (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ σ : ℝ) (hσ : -(1 / 3 : ℝ) < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t →
      ‖archDirectProfile c m τ t‖ ≤ B * t ^ (-σ)
```

```lean
theorem archReflectedProfile_bound (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ σ : ℝ) (hσ : -(1 / 3 : ℝ) < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t →
      ‖archReflectedProfile c m τ t‖ ≤ B * t ^ (-σ)
```

### 4.4 全部 17 个字段的来源及规范构造

下表中的 `C` 总是同一个 `FiniteFixedSource.Source R θ`。`LocalArch` 均指上述完整 `ThetaGlobal.LocalArch…` 命名空间。

| `FiniteLocalHighK.Input` 字段 | 来源 |
| --- | --- |
| `vector` | `LocalArchProfile.vector R θ`；`traceRootCore` 的权为 `heckeComplexWeight … θ⁻¹`。 |
| `functional` | 每处使用实际连续映射 `thetaJacquetFunctional traceFrequency`。 |
| `whittaker` | `LocalArchRootCore.traceJacquet_whittaker`。 |
| `functional_nonzero` | `LocalArchProfile.functional_nonzero`，由实际值 `besselKThird (4 * Real.pi) > 0`。 |
| `source_nonzero` | `FiniteFixedSource.Source.archimedean_nonzero`；使用构造时保留的 `localWhittakerForms` 和真正的 Whittaker 唯一性。 |
| `scale` | 每处 `archScale (4 * Real.pi)`，原定义是 `4 / c ^ 2`。 |
| `scale_pos` | `archScale_pos (4 * Real.pi) (by positivity)`。 |
| `directConstant` | `LocalArchMellin.directConstant R θ C.transport`，保留角向总质量并除以 Bessel 归一化值。 |
| `directConstant_nonzero` | `LocalArchMellin.directConstant_nonzero`，来自正角向质量、原局部常数非零和正 Bessel 值。 |
| `reflectedConstant` | `LocalArchMellin.reflectedConstant R θ C.transport`，使用相同 Haar 与 Bessel 归一化。 |
| `reflectedConstant_nonzero` | `LocalArchMellin.reflectedConstant_nonzero`。 |
| `direct_integrable` | `LocalArchMellin.direct_mellin … .1`，在原 completion-unit `archHaar` 上。 |
| `reflected_integrable` | `LocalArchMellin.reflected_mellin … .1`。 |
| `direct_bound` | `LocalArchInput.direct_bound`，把 `LocalArchBounds.archDirectProfile_bound` 除以固定 Bessel 值的范数。 |
| `reflected_bound` | `LocalArchInput.reflected_bound`，使用 `archReflectedProfile_bound`。 |
| `direct_mellin` | `LocalArchMellin.direct_mellin … .2`，Gamma pair 为 `FiniteLocalHighK.directGammaPair R θ w s`。 |
| `reflected_mellin` | `LocalArchMellin.reflected_mellin … .2`，Gamma pair 为 `FiniteLocalHighK.gammaPair R θ w s`。 |

填充结构的定义完整逐字为，继承 `LocalArchInput` 的 `R`、`θ` 上下文：

```lean
def input (C : FiniteFixedSource.Source R θ) : FiniteLocalHighK.Input R θ C where
  vector := LocalArchProfile.vector R θ
  functional := fun _ => thetaJacquetFunctional traceFrequency
  whittaker := fun _ => LocalArchRootCore.traceJacquet_whittaker
  functional_nonzero := LocalArchProfile.functional_nonzero R θ
  source_nonzero := fun w =>
    FiniteFixedSource.Source.archimedean_nonzero R θ C w
      (thetaJacquetFunctional traceFrequency) LocalArchRootCore.traceJacquet_whittaker
      (LocalArchProfile.vector R θ w) (LocalArchProfile.functional_nonzero R θ w)
  scale := fun _ => archScale (4 * Real.pi)
  scale_pos := fun _ => archScale_pos (4 * Real.pi) (by positivity)
  directConstant := LocalArchMellin.directConstant R θ C.transport
  directConstant_nonzero := LocalArchMellin.directConstant_nonzero R θ C.transport
  reflectedConstant := LocalArchMellin.reflectedConstant R θ C.transport
  reflectedConstant_nonzero := LocalArchMellin.reflectedConstant_nonzero R θ C.transport
  direct_integrable := fun w s hs =>
    (LocalArchMellin.direct_mellin R θ C.transport w s hs).1
  reflected_integrable := fun w s hs =>
    (LocalArchMellin.reflected_mellin R θ C.transport w s hs).1
  direct_bound := direct_bound R θ
  reflected_bound := reflected_bound R θ
  direct_mellin := fun w s hs =>
    (LocalArchMellin.direct_mellin R θ C.transport w s hs).2
  reflected_mellin := fun w s hs =>
    (LocalArchMellin.reflected_mellin R θ C.transport w s hs).2
```

最后的 skeleton 适配位于 `ThetaGlobal/LocalArchSource.lean`，命名空间是 `HeckeSkeleton`，继承 `variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)`：

```lean
def localHighKMellinInput : LocalHighKMellinInput K c :=
  ThetaGlobal.LocalArchInput.input (thetaRecipe K c)
    (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))
    (thetaFiniteSource K c)
```

右端三个实参逐字就是现有 `LocalHighKMellinInput K c` 别名中的 recipe、period 字符和固定 source，因此此适配只需定义展开，不加 type-equality 假设或另一次 `Classical.choice`。全局种子、sheet 积分、系数识别、支持集双射、反射级数收敛和任意 annular test 的反射恒等式都不在这 17 个字段中。

## 5. 已构造的 H：实际有限位数字证书

准确类型是 `ThetaGlobal.GlobalProjectLocalDigitTables.Input R D Adata`；这里 `D` 是 **实际 source factorization**，不是第 1 节中 theta arithmetic datum 的记号。该四字段命题仍作为通用证明接口存在，固定入口已经给出它的构造，不再要求调用者提供 `H`。保留的类型别名及其固定源对应关系如下，命名空间为 `HeckeSkeleton`：

```lean
local notation "R" => thetaRecipe K c
local notation "Sf" => places K c
local notation "Adata" => arithmeticData K c

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

`nonzero_digits` 中名为 `L` 的量是一个任意满足 residue-lift 条件的函数，和第 4 节的高 K-型数据 `L` 是不同的局部绑定变量。每条字段只涉及一个 exterior prime。下面的构造填充这四个字段。零 residue 由 compact invariance 推出；marked average 由 `q⁻¹ = δ₀ - digitMask₀` 推出；有限乘积、active-set 展开和最终频率重排再由这些局部事实推出。

### 5.1 五个局部桥模块与四字段来源

这条链复用同一 recipe 的生成元、复嵌入、实际参考向量、表示作用与 Whittaker functional。`LocalDigitEvaluation` 的参数是 `JointExteriorCoefficientSources`：它只使用已有 factorization、exterior spherical values 和 `RootAligned`，没有要求 `JointUpperVanishingSources` 所附带的 packet、全局 Mellin、全局求和性或反射恒等式。

| 新模块 | 实际连接 |
| --- | --- |
| [`ThetaGlobal.LocalDigitArithmetic`](../ThetaGlobal/LocalDigitArithmetic.lean) | 将 recipe 的 `ThetaBranch.residueCharacter`、`Characters.psi` 识别为同一 `thetaArithmeticData` 的 `thetaPrimeCharacter`、`primePhase`；连接球面数字表、`zeroth_weyl` 与 `forward_mask`。 |
| [`ThetaGlobal.LocalDigitEvaluation`](../ThetaGlobal/LocalDigitEvaluation.lean) | 对实际 `A(x) W N(-s/g_p)` 作用于同一参考向量的局部系数，复用 Bruhat、compact invariance 与局部 Whittaker 协变性计算非零数字值。 |
| [`ThetaGlobal.LocalDigitAverage`](../ThetaGlobal/LocalDigitAverage.lean) | 对任意合法 residue lifts 求和；负的 `order + 2` 给零，非负部分转成有限域单位群之和并应用已实现的 `localWeyl_phase_separation`。 |
| [`ThetaGlobal.LocalDigitInput`](../ThetaGlobal/LocalDigitInput.lean) | 证明两处实际局部系数定义相等，填充现有 `Input` 的全部四字段。 |
| [`ThetaGlobal.LocalDigitSource`](../ThetaGlobal/LocalDigitSource.lean) | 对齐同一 `axiomChoice` 的 arithmetic datum，并在已经选定的 `thetaFiniteSource` 上构造 `localExteriorDigitInput`。 |

`diagonal` 来自 `C.exterior.rational_exact` 与 `LocalDigitArithmetic.sphericalFactor_eq`；`nonzero_digits` 来自上述实际表示计算与有限域相位分离；`zeroth_weyl` 和 `forward_mask` 连接已合并局部交付的 `HeckeSkeleton.ThetaLocal.ProjectFinite`。数字表的平方根/Gauss 归一化和 residue-zero 分支按原定义保留，没有另设可自由选择的数字函数。

### 5.2 泛型实际 source 的完整构造

以下为 `LocalDigitInput.lean` 中的实际上下文、定义识别和四字段构造。`hdiff` 是明确的有限位算术条件；在固定入口它由已有 `axiomChoice.different` 填充，不成为新的外部假设。各代码块的 namespace/局部绑定作用域分别读取。

```lean
namespace ThetaGlobal.LocalDigitInput

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectDigitProduct
open ThetaGlobal.GlobalProjectLocalDigitTables
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointExteriorCoefficientSources R N)

/-- Both definitions evaluate the same actual reference vector at the
same canonical local representation of `A(x) W N(-s/g_p)`. -/
theorem localDigit_eq (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (s : 𝓞 F) :
    localDigit R C.factorization p x s =
      LocalDigitEvaluation.localDigitValue R C p x s := by
  simp only [GlobalProjectDigitProduct.localDigit, OrbitExpansion.exteriorSlotValue,
    LocalDigitEvaluation.localDigitValue, map_mul]

variable (hdiff : ∀ p : HeightOneSpectrum (𝓞 F),
  p ∉ (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) → localDifferentExponent F p = 0)

local notation "Adata" => HeckeAxiom.thetaArithmeticData R.A R.probe.allowed R.σ hdiff

/-- The local digit package of the same actual exterior source, with no
remaining local-table hypothesis. -/
theorem input : GlobalProjectLocalDigitTables.Input R C.factorization Adata where
  diagonal p x := by
    rw [C.exterior.rational_exact]
    exact LocalDigitArithmetic.sphericalFactor_eq R hdiff p x
  nonzero_digits p j x L hL := by
    simp_rw [localDigit_eq R C]
    exact LocalDigitAverage.nonzero_digits R C hdiff p j x L hL
  zeroth_weyl p := LocalDigitArithmetic.zeroth_weyl R hdiff p
  forward_mask p j t := LocalDigitArithmetic.forward_mask R hdiff p j t

end ThetaGlobal.LocalDigitInput
```

### 5.3 同一固定选择上的 canonical H

以下是 `LocalDigitSource.lean` 的完整接口及构造体。`thetaRecipe_arithmeticData` 只改写同一选择已经保留的 allowed-generator 等式，没有重新选择 source、素位集、生成元或字符。

```lean
namespace HeckeSkeleton

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

theorem thetaRecipe_arithmeticData :
    HeckeAxiom.thetaArithmeticData (thetaRecipe K c).A
      (thetaRecipe K c).probe.allowed (thetaRecipe K c).σ
      (axiomChoice K c).different = arithmeticData K c := by
  change HeckeAxiom.thetaArithmeticData (axiomChoice K c).A
    (ThetaGlobal.GlobalSameChoice.recipe (axiomChoice K c)
      (axiomChoice_modulus_top K c)).probe.allowed
    (complexEmbedding K c) (axiomChoice K c).different = (axiomChoice K c).thetaData
  rw [ThetaGlobal.GlobalSameChoice.recipe_allowed]
  rfl

/-- The actual fixed source supplies its exterior digit table without an
additional local-table hypothesis. -/
theorem localExteriorDigitInput :
    ThetaGlobal.GlobalProjectLocalDigitTables.Input (thetaRecipe K c)
      (thetaFiniteSource K c).projected.base.factorization (arithmeticData K c) := by
  have h := ThetaGlobal.LocalDigitInput.input (thetaRecipe K c)
    (thetaFiniteSource K c).projected.base (axiomChoice K c).different
  rw [thetaRecipe_arithmeticData K c] at h
  exact h

end HeckeSkeleton
```

通用中间定理 `HeckeSkeleton.thetaRecipe_marked_reflection` 仍显式接收 `H : GlobalProjectLocalDigitTables.Input R C.projected.base.factorization Adata`。固定源适配器完整地把上述构造传入该参数；这一层不再接收 `H`：

```lean
theorem thetaFiniteSource_marked_reflection
    (L : LocalHighKMellinInput K c)
    (hA : AllowedGeneratorInput K Sf Adata)
    (hS : conductorPlaces K
      (thetaPeriod K Sf (probeData K c) (targetCharacter K c)) ⊆ R.A.Sf)
    (w : InfinitePlace K)
    (hk : heckeComplexWeight K w (R.A.complex_place w)
      (thetaPeriod K Sf (probeData K c) (targetCharacter K c)) ≠ 0)
    (d : MarkedDatum K Sf) (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) :
    completedThetaSum K Sf Adata
      (thetaPeriod K Sf (probeData K c) (targetCharacter K c))
      (rowElement K Sf Adata d) d.puncture d.marks V.toFun X =
      ∑' i : ReflectionIndex K Sf d,
        reflectedTerm K Sf Adata d i (FiniteSkeletonSource.data K c L)
          (thetaPeriod K Sf (probeData K c) (targetCharacter K c)) V.toFun X :=
  thetaRecipe_marked_reflection K c
    (thetaPeriod K Sf (probeData K c) (targetCharacter K c))
    (thetaFiniteSource K c) L (localExteriorDigitInput K c) hA hS w hk d V hX
```

这五个新模块的原生编译及 `LocalDigitAudit` 尚未完成。这里记录的是已经接入公开声明的真实源码证明链；不把静态核对、原任务允许该输入，或其他模块的历史成功记录当作新链的原生成功。

## 6. 实际有限表的归一化与壳层积分规格

通用 `HeckeSkeleton.FiniteSkeletonSource.data K c L` 保持原接口。公开表 `HeckeSkeleton.finiteMellinData K c` 精确取该构造在 `L := localHighKMellinInput K c` 的值。`C₀`、`A₀` 来自同一 source 的 cutoff volume 和这个规范输入的局部常数；其具体 Haar 总质量和 Bessel 因子见第 4.3 节。下面保留通用构造的真实源码，位于 `HeckeSkeleton.FiniteSkeletonSource`，继承 `K`、`c`、`L`：

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

这一节记录本修订实际接线后的完整参数变化。它保留仓库其他任务的原有 obligations，不把整条 seven-eighths endpoint 的源码装配当作已无 admission 的数学证明。

下表的全部名称都在 `HeckeSkeleton` 命名空间。`K`、`c` 参数按源文件 section 自动纳入；最终全域 endpoint 不额外带外层 `K` 参数，因为它的签名直接量化 `F`。

| 消费者 | 接入规范 L 前的显式前缀 | 本修订显式前缀 | 前缀参数个数 |
| --- | --- | --- | --- |
| `completedMarkedEnergy` | `K c L hreflection` | `K c hreflection` | 4 → 3 |
| `principalSource` | `K c L` | `K c` | 3 → 2 |
| `canonical_inverse_models` | `K c L hcal hrows hprofiles hquadratic hcubic hreflection` | `K c hcal hrows hprofiles hquadratic hcubic hreflection` | 9 → 8 |
| `inverseSource` | `K c L` | `K c` | 3 → 2 |
| `sourceT` | `K c L` | `K c` | 3 → 2 |
| `familyInputs` | `K zeta hzeta omega localData` | `K zeta hzeta omega` | 5 → 4 |
| `generalHeckeSevenEighths_skeleton` | `localData` | 无新增局部参数 | 1 → 0 |

计数不含 typeclass 实参和结论内部保持不变的量词。两个 `hreflection` 仍保留，其有限表改为规范 `finiteMellinData K c`。此前已移除 `H/localDigits`；本修订进一步移除 `L/localData`。

通用接口保持原显式调用顺序：`FiniteSkeletonSource.data K c L`、`FiniteSkeletonSource.admissible K c L`、`thetaFiniteSource_marked_reflection K c L hA hS w hk d V hX`，以及 `thetaRecipe_marked_reflection K c θ C L H hA hS w hk d V hX`。最后两个 helper 的 `{X : ℝ}` 仍为隐式；公共 `marked_reflection K c hkernel d V X hX` 的 `X` 则在结论中显式量化。

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
theorem completedMarkedEnergy
    (hreflection : MarkedCoefficientReflectionInput K S (probeData K c).arithmetic
      (finiteMellinData K c) (thetaPeriod K S P ψ)) : CompletedMarkedEnergy K c
```

```lean
theorem principalSource :
    (probeMeasures K c).principalInput P ψ g T
```

```lean
theorem canonical_inverse_models
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c) (hcubic : CubicSieveBound K c)
    (hreflection : MarkedCoefficientReflectionInput K (places K c)
      (probeData K c).arithmetic (finiteMellinData K c)
      (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))) :
    CanonicalInverseModelBounds (momentModels K c)
```

```lean
theorem inverseSource :
    ISource c.geometry (targetData K c) c.family.lamA
```

```lean
theorem sourceT (c : TargetContext K) :
    TSource c.geometry (targetCharacter K c) (targetData K c)
      c.family.B c.family.lamA c.lamB
```

```lean
theorem familyInputs (zeta : K) (hzeta : IsPrimitiveRoot zeta 12)
    (ω : HeckeCharacter K) : TIPInput K ω
```

`canonical_inverse_models` 与 `inverseSource` 继承 `variable (K c)`；`sourceT` 与 `familyInputs` 继承 Main 的 `variable (K : Type) [Field K] [NumberField K]`。对应完整参数顺序和返回类型还由 `verification/theta_global/ConsumerSignatures.lean` 的 typed examples 检查；该文件的消费者公理报告允许原有 `sorryAx`，所以其意义是接口兼容性。

### 7.1  Main endpoint 的完整声明：无新增局部参数，仍有其他 admissions

以下逐字取自 [HeckeSkeleton/Main.lean](../HeckeSkeleton/Main.lean)，包括完整签名和装配证明：

```lean
theorem generalHeckeSevenEighths_skeleton : GeneralHeckeSevenEighths := by
  intro F _ _
  apply Descent.descend F
  intro ω
  exact familyInputs (Descent.Extension F) (Descent.root12 F)
    (Descent.primitive_root12 F) ω
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

`GeneralHeckeSevenEighths` 的含义是所有数域、所有实际连续酉 Hecke 字符的 `heckeContinuation` 在 `Re(s) > 7/8` 无 meromorphic zero；其定义仍允许纯 norm 字符导致的极点。Main 的 theorem 当前仍通过其他任务的既有 admissions 依赖 `sorryAx`。本修订为五个 theta 目标接入规范 `L`，使 Main 不再添加局部包前提，但没有消除 Principal／Moments 及其他既有上游 admissions。五个 theta 目标、规范局部构造及其完整依赖的原生验证仍待完成。

## 8. 源码完成边界与验证记录的解释

原 TASK 允许单处输入；本修订已经接线完整 `L` 和 `H` 的源码构造及其公开接口。完整 native 验收仍未完成：五目标、规范局部构造及实际依赖闭包必须通过固定版本编译和递归公理门，有限表必须保有原局部壳层积分规格。源码实现和静态接口核对不能代替这些原生检查。

[EntryAudit.lean](../verification/theta_global/EntryAudit.lean) 在原 21 项检查上新增 28 项，共 **49 = 5 个目标 + 44 个接口**。新增部分分别是 RootCore 5、Profile 4、Haar 6、Mellin 4、Bounds 2、Input 3、规范 skeleton constructor 1，以及保留 source certificate 的接口 3。允许的公理仅为 `propext`、`Classical.choice`、`Quot.sound`；检查必须成功退出并实际产生 5 条 `THETA_GLOBAL_AXIOMS` 与 44 条 `THETA_GLOBAL_INTERFACE_AXIOMS`，才构成该门的成功结果。

[LocalDigitAudit.lean](../verification/theta_global/LocalDigitAudit.lean) 保留 12 条 `THETA_GLOBAL_LOCAL_DIGIT_AXIOMS` 检查。[LocalArchAnalyticAudit.lean](../verification/theta_global/LocalArchAnalyticAudit.lean) 新增 8 条严格检查（6 Haar + 2 Bessel bounds），产生 `THETA_GLOBAL_LOCAL_ARCH_AXIOMS`；完整 input 和固定 source 仍由上述 49 条 EntryAudit 递归检查。

实际入口 [workflow](../.github/workflows/theta-global.yml) 的 job 总上限为 **330 分钟**，各显式 step timeout 合计 **309 分钟**。算术 foundation/cache checkpoint 后，原 35 分钟早期 build 用一个不带 `--fail-fast` 的 `lake build` 同时构建 `LocalDigitAverage`、`LocalArchHaar`、`LocalArchBounds`，然后运行原 4 分钟数字审计与新增 4 分钟解析审计。其后 Theta／方向模块、Main 与七个消费者检查的 build 顺序保持。此处记录验证配置，不将配置或运行中状态当作成功结果。

[ConsumerSignatures.lean](../verification/theta_global/ConsumerSignatures.lean) 的七项类型检查已接到第 7 节签名，但仍允许既有 `sorryAx`。它检查下游接口兼容性，不能用于宣称整个 seven-eighths endpoint 已无 admission。

历史提交 `b45484e24f3d4e28cc8092ff6b296f38f4a0f94f` 的 [standalone job](https://github.com/Rogerhu12/hecke-seven-eighths/actions/runs/41166970094/job/124436512226) 于 `2026-10-31T04:05:38Z` 成功，检查 45 个 transformed source bodies 和全部 56 条严格记录；artifact SHA-256 为 `7f3d0592a8f2ec9ea13582f711f061a4c614f2f439892733e1b7f8cd5c265f6e`。该检查的 45 个源文件哈希仍全部匹配本修订。仓库中的 [核查记录](../verification/theta_global/ci_41166970094_standalone.json) 和 [原始编译日志](../verification/theta_global/ci_41166970094_standalone.log) 保留其提交、变换与验证范围。它没有检查规范 L 构造，也未认证 H 或完整 native entry closure。实际 `LocalArchHaar` 源码（指纹见第 9 节）的独立原生尝试于 `2026-10-31T04:42:03Z` 在 20 分钟预算处停止：耗时 `1201.156` 秒，退出码 `-15`，日志为 0 字节，没有公理输出，归类为 `resource-inconclusive`。该结果既不认证通过，也不确定 Lean 证明错误；[运行记录](../verification/theta_global/native_local_arch_haar_20261031.json)、[原始日志](../verification/theta_global/native_local_arch_haar_20261031.log) 与 [映射采样](../verification/theta_global/native_local_arch_haar_20261031.maps.jsonl) 已归档。`LocalArchBounds` 的实际源码检查仍在运行，不预填结果。

历史事实保持其原范围：`FiniteLocalShellProject` 与 `GlobalEmbedding` 独立原生通过；`GlobalProjectEmbedding` 本地尝试在导入时达到映射数量上限而失败；CI `41159434388` 在算术 foundation 的时间上限停止并保存两个缓存，Theta/Main 门未运行。旧 standalone／188-module／9-module／54-module 等 transformed 验证仍只认证其记录的源码、变换和选项。详见 [`THETA_GLOBAL.md`](THETA_GLOBAL.md) 原有历史段落；历史 QA 和 manifests 保持原样。

## 9. 声明来源与源码指纹

下列 SHA-256 标识本报告核对时读取的实际仓库原文，用于核查逐字声明和验证配置的来源，不是编译证书。若源文件的证明、注释或 import header 后续改变，应同步重算受影响指纹并核对摘录；历史验证 manifests 保留各自当时的源哈希，不应被本表替换。

| 源文件 | SHA-256 |
| --- | --- |
| `.github/workflows/theta-global.yml` | `f491763b377dded54aa51ef63f4e99d9e513dca61e291966d9d045e1a2118477` |
| `DedekindZetaZeroFree/Arithmetic/ResidueSymbols/SixthRootAlignment.lean` | `8c04cacf75ff71f02a41d190cea7b3b33d6e04e525a6a5f528d7508ce80e576f` |
| `HeckeGeneral/Analysis/HeckeEndpointTarget.lean` | `df13b15c2eadef1564e7270174f11e435a0dd0f2dac4d8f52c58faa3fa5a19c7` |
| `HeckeGeneral/Analysis/PhysicalProbeData.lean` | `eed80b7917e82014bc94ca60fa34a9eef12bd162ae91adfbe5fe60bacebe13d9` |
| `HeckeSkeleton/Base.lean` | `f39648a385520d311a2f7dc38d396920dd1d68a6fdf8eb92cd80204acccc7150` |
| `HeckeSkeleton/Main.lean` | `87bde25e9460f096079f9f46b7e9e12305ac25769189ffbb9e83189cd28a087f` |
| `HeckeSkeleton/Moments.lean` | `5257b528ead4bfbc85947715010ad37eeb1a06fce8c8fb41ef7c24fb3e262455` |
| `HeckeSkeleton/Principal.lean` | `adc012766fb5fa2a5da257019d5660aae1e745fe7e8b40311a4a6c3fb91a81f9` |
| `HeckeSkeleton/Theta.lean` | `30c54c50ec99568ff48f469e7b1d16019abaf61211897a5e020c07ca0ae99684` |
| `HeckeSkeleton/ThetaLocal/ArchimedeanMellin.lean` | `fc82ad1ce42ba9ac98e50b267c71d20d38612a62f961265c9c2215716a125030` |
| `HeckeSkeleton/ThetaLocal/ProjectArchimedeanWhittaker.lean` | `5dd1b809f18c2bce1ae3c0143392e542fa8675de0b78a37b96311a5962a4fd15` |
| `HeckeSkeleton/ThetaLocal/ProjectFinite.lean` | `e46a90f9bfa13f9dc19f9dd28f9b5254f79166394eaa646a9f9e67a13f333e95` |
| `ThetaGlobal/FiniteFixedSource.lean` | `091f49b430564ae0c29c82eb01c6807767ed9a1379cd458ea11082c115bd316b` |
| `ThetaGlobal/FiniteFullProduct.lean` | `d66a9041f8cd20c363d8ba95f8da13024865f1e7f1a450d7df1f7b31efabd353` |
| `ThetaGlobal/FiniteLocalHighK.lean` | `1aacf87b81d21bddac6aa99b4af1bf9d7c184d3ce9ed1cde4727cf15b5f14463` |
| `ThetaGlobal/FiniteProjectedFullSource.lean` | `a722083034a213afd941ef9622840efc624415706b733a18dcd8655269d15c28` |
| `ThetaGlobal/FiniteSkeletonSource.lean` | `d0856effdcec8ff51e3aaf8caa5359fd67570c01bdc45b3d06bce4066c7c756f` |
| `ThetaGlobal/GlobalEmbedding.lean` | `42d71b175d8208d4e4c072f5d6b3d098a16259ca5e932e0bcbb206ee091b246f` |
| `ThetaGlobal/GlobalProjectDigitProduct.lean` | `811cae13cd2f93d3bf02ed4ccfc79c1ae1d0f789cfaad0f7ef134c8e4fd680b4` |
| `ThetaGlobal/GlobalProjectLocalDigitTables.lean` | `9527446ae4f7acd4d5af4bfd5d0d1f3ddb5a812788401dd2dabc8a0b5cc5d1db` |
| `ThetaGlobal/GlobalProjectMarkedReflection.lean` | `a091fab6852b6d060a6311f5b0df9607029d516c2d8076f8adc6347674199277` |
| `ThetaGlobal/GlobalSameChoice.lean` | `d699611e1c5357e866ad0a722f5b7083b69e2bc2b17a8fadba3447c43022aad5` |
| `ThetaGlobal/LocalArchBounds.lean` | `1a0ebeb15576956ca65f09cc6526a1b9d0522081cd61820cd14761c67f43dd8f` |
| `ThetaGlobal/LocalArchHaar.lean` | `04fcd6397486b8309beb1b0c7c18fd9551df6c795c17cc46b6e9e5e4edea5e3b` |
| `ThetaGlobal/LocalArchInput.lean` | `5def37212adc79c9a9d181efd7b982de38101e663e8d64583782c3176fcbc04d` |
| `ThetaGlobal/LocalArchMellin.lean` | `193a8c9b06d7daedd8dd7997a4bfcb77161ad1a57d752121681e53c66f64e965` |
| `ThetaGlobal/LocalArchProfile.lean` | `002d162e1001e9927ca95cc0f29093eb7811df8e71be3a9a22174a744d438f84` |
| `ThetaGlobal/LocalArchRootCore.lean` | `487dd632507ea032c3f832e53c94f3756e8db66335844263fad0b1f8a069e11a` |
| `ThetaGlobal/LocalArchSource.lean` | `553c96489c7b1bcc31925da658ef2b256229e4192b3e46210f4885ab65f9fad2` |
| `ThetaGlobal/LocalDigitArithmetic.lean` | `1464df23e54d81fa75155d54c29905c7b00ee7307570ec6d32a76ac3b5e7fef9` |
| `ThetaGlobal/LocalDigitAverage.lean` | `c6ea37aba5300c9f3017f946f37130fa95ab773c3969c390d9b87ccbee4b7bed` |
| `ThetaGlobal/LocalDigitEvaluation.lean` | `e2745823d85284461f96ee1c874084d098057119c1f3859a9e54530f912f0d93` |
| `ThetaGlobal/LocalDigitInput.lean` | `c99f638c29b7d9dff6eb12b406f6b3032dbe646130edf6f7d0e6fe8f28981fa6` |
| `ThetaGlobal/LocalDigitSource.lean` | `219ff4ea7eaf32cd12fd74370a4bcce4923c8f37cd81bfded988fc29f8ea3a83` |
| `ThetaGlobal/LocalGammaOrientation.lean` | `ad9306b508904ca4a27d29065b4d55b476c123e19f9c5f379b7240b6f21813f0` |
| `verification/theta_global/ConsumerSignatures.lean` | `6c4c89e6d5370ddad6a4c7462935b91154b894cf329ed5e5161abaa7875dbf00` |
| `verification/theta_global/EntryAudit.lean` | `94f3f850adffedfdceebf828f1519c2f53c17a26f42d571220ee28267837d250` |
| `verification/theta_global/LocalArchAnalyticAudit.lean` | `25f3fbd667b7bb58e3e7c093d5cab015f6a9d9e9d1433312a471ec41fa09c6e2` |
| `verification/theta_global/LocalDigitAudit.lean` | `970991b499c597961ed1669490e9f0781c79ab76de7352514be266a08f5e21c6` |

AI-assisted：OpenAI ChatGPT / GPT-6 Astra Pro，2026-10-31。
