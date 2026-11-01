import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionChildGeometry

/-!
# Genuine universal reflection labels on the common kernel support

The common numerical parameter space contains every dyadic index. Only
indices at most the actual cutoff carry mass. The child label therefore
uses the genuine normalized reflected model on that support and the
original parent outside it. No geometric assertion is imposed on unused
large indices. The numerical energy agrees almost everywhere with the
actual reflected energy, so both integrability and the integral transfer
without a measurable structure or a measurable map on the model family.

The two geometric constructors use only the actual invariant node,
supported dyadic bounds and primitive child admissibility. Their full
slot capacity is proved by `ReflectionChildGeometry`; no child moment
estimate or label-existence premise is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ThetaKernel HeckeSkeleton.HeckeConductorNorm
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckePort.Moments HeckePort.Moments.ReflectionMass
open scoped Classical BigOperators

universe u v

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- The fixed common kernel is supported on the actual retained indices.
The predicate itself needs no measurability hypothesis. -/
theorem ae_reflectionCommonKernel_cutoff {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) (weight : Ω → ℝ) (cutoff : ℕ) :
    ∀ᵐ x ∂reflectionCommonKernel μ weight cutoff, x.1.1 ≤ cutoff := by
  apply ae_reflectionCommonKernel
  intro b hb
  exact Filter.Eventually.of_forall fun _ => (mem_reflectionBranches cutoff b).mp hb

variable {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
variable {W padding : ℝ} {cap : ℕ}

/-- A genuine child on the common kernel support, and the existing
parent label outside it. The supported invariant contains only actual
geometric and primitive source facts. -/
def cutoffReflectionChild
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hvalid : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      UniversalNodeInvariant primitive W padding cap
        (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x))
    (x : (ℕ × Bool) × ℝ) : ULift.{u} (UniversalNode primitive W padding cap) :=
  if hx : x.1.1 ≤ cutoff then
    ⟨⟨parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x, hvalid x hx⟩⟩
  else parent

theorem cutoffReflectionChild_node
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hvalid : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      UniversalNodeInvariant primitive W padding cap
        (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x))
    (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) :
    (cutoffReflectionChild parent first U E0 hE0 childOrder cutoff hvalid x).down.val =
      parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x := by
  simp only [cutoffReflectionChild, dif_pos hx]

theorem cutoffReflectionChild_outside
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hvalid : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      UniversalNodeInvariant primitive W padding cap
        (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x))
    (x : (ℕ × Bool) × ℝ) (hx : ¬x.1.1 ≤ cutoff) :
    cutoffReflectionChild parent first U E0 hE0 childOrder cutoff hvalid x = parent := by
  simp only [cutoffReflectionChild, dif_neg hx]

theorem cutoffReflectionChild_ae
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hvalid : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      UniversalNodeInvariant primitive W padding cap
        (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x))
    (weight : ℝ → ℝ) :
    ∀ᵐ x ∂reflectionCommonKernel volume weight cutoff,
      (cutoffReflectionChild parent first U E0 hE0 childOrder cutoff hvalid x).down.val =
        parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x := by
  filter_upwards [ae_reflectionCommonKernel_cutoff volume weight cutoff] with x hx
  exact cutoffReflectionChild_node parent first U E0 hE0 childOrder cutoff hvalid x hx

/-- This is equality of the original numerical normalized energies,
not an assumption that the model-valued map is measurable. -/
theorem cutoffReflectionChild_energy_ae
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hvalid : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      UniversalNodeInvariant primitive W padding cap
        (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x))
    (weight : ℝ → ℝ) :
    (fun x => (cutoffReflectionChild parent first U E0 hE0 childOrder cutoff hvalid x).down.val.normalizedEnergy
      U 0) =ᵐ[reflectionCommonKernel volume weight cutoff]
      (fun x => (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x).normalizedEnergy
        U 0) := by
  filter_upwards [cutoffReflectionChild_ae parent first U E0 hE0 childOrder cutoff
    hvalid weight] with x hx
  exact congrArg (fun n : Node K ω ψ => n.normalizedEnergy U 0) hx

theorem cutoffReflectionChild_integrable
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (U E0 : ℝ) (hU : 0 < U) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hvalid : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      UniversalNodeInvariant primitive W padding cap
        (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x))
    (weight : ℝ → ℝ) (hw : ∀ t, 0 ≤ weight t) (hi : Integrable weight) :
    Integrable (fun x =>
      (cutoffReflectionChild parent first U E0 hE0 childOrder cutoff hvalid x).down.val.normalizedEnergy
        U 0) (reflectionCommonKernel volume weight cutoff) :=
  (parent.down.val.fixedLineReflectionChild_integrable first U E0 hU hE0 childOrder
    cutoff weight hw hi).congr
    (cutoffReflectionChild_energy_ae parent first U E0 hE0 childOrder cutoff hvalid weight).symm

theorem cutoffReflectionChild_integral
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hvalid : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      UniversalNodeInvariant primitive W padding cap
        (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x))
    (weight : ℝ → ℝ) :
    (∫ x, (cutoffReflectionChild parent first U E0 hE0 childOrder cutoff hvalid x).down.val.normalizedEnergy
      U 0 ∂reflectionCommonKernel volume weight cutoff) =
      ∫ x, (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x).normalizedEnergy
        U 0 ∂reflectionCommonKernel volume weight cutoff :=
  integral_congr_ae
    (cutoffReflectionChild_energy_ae parent first U E0 hE0 childOrder cutoff hvalid weight)

/-- The genuine zero-slot reflected model is a label from primitive
admissibility alone; a core bound is supplied separately on the support. -/
def outerCutoffReflectionChild
    (parent : ULift.{u} (UniversalNode primitive W padding cap))
    (U E0 : ℝ) (hU : 1 < U) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hzero : parent.down.val.parameters.z = 0)
    (hadmissible : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      let child := parent.down.val.fixedLineReflectionChild
        (reflectionLongFirst parent.down.val.parameters) U E0 hE0 childOrder x
      admissibleOfInvariant primitive child.data child.parameters) :
    (ℕ × Bool) × ℝ → ULift.{u} (UniversalNode primitive W padding cap) :=
  cutoffReflectionChild parent (reflectionLongFirst parent.down.val.parameters)
    U E0 hE0 childOrder cutoff (fun x hx =>
      parent.down.val.fixedLongReflectionChild_outer_invariant parent.down.property
        U E0 hU hE0 childOrder x hzero (hadmissible x hx))

theorem outerCutoffReflectionChild_geometry
    (parent : ULift.{u} (UniversalNode primitive W padding cap))
    (U E0 : ℝ) (hU : 1 < U) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ)
    (hzero : parent.down.val.parameters.z = 0)
    (hadmissible : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      let child := parent.down.val.fixedLineReflectionChild
        (reflectionLongFirst parent.down.val.parameters) U E0 hE0 childOrder x
      admissibleOfInvariant primitive child.data child.parameters)
    (weight : ℝ → ℝ) (gap boundary : ℝ) (hgap : 0 ≤ gap)
    (hlong : max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂ ≤
      parent.down.val.width + gap)
    (hnext : ∀ j ≤ cutoff, reflectionDyadicExponent U j ≤
      max (parent.down.val.width -
        max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂) 0 + boundary)
    (hbudget : gap + boundary ≤ padding) :
    ∀ᵐ x ∂reflectionCommonKernel volume weight cutoff,
      let child := (outerCutoffReflectionChild parent U E0 hU hE0 childOrder cutoff
        hzero hadmissible x).down.val
      child.parameters.z = parent.down.val.parameters.z ∧
        child.width = parent.down.val.width ∧ child.totalLength ≤ child.width + padding := by
  filter_upwards [ae_reflectionCommonKernel_cutoff volume weight cutoff] with x hx
  dsimp only
  have heq := cutoffReflectionChild_node parent
    (reflectionLongFirst parent.down.val.parameters) U E0 hE0 childOrder cutoff
    (fun y hy => parent.down.val.fixedLongReflectionChild_outer_invariant parent.down.property
      U E0 hU hE0 childOrder y hzero (hadmissible y hy)) x hx
  change (outerCutoffReflectionChild parent U E0 hU hE0 childOrder cutoff hzero
    hadmissible x).down.val = _ at heq
  rw [heq]
  exact ⟨rfl, rfl, parent.down.val.fixedLongReflectionChild_outer_core U E0 hE0
    childOrder x gap boundary padding hzero hgap hlong (hnext x.1.1 hx) hbudget⟩

/-- Positive capacity and nonnegative plain lengths of every retained
comparison child are proved, rather than included in the admissible input. -/
def comparisonCutoffReflectionChild
    (parent : ULift.{u} (UniversalNode primitive W padding cap))
    (U E0 : ℝ) (hU : 1 < U) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ) (boundary : ℝ)
    (hshort : parent.down.val.parameters.n₁ ≤ parent.down.val.width / 4 ∨
      parent.down.val.parameters.n₂ ≤ parent.down.val.width / 4)
    (hcore : parent.down.val.totalLength ≤ parent.down.val.width + padding)
    (hpadding : padding ≤ parent.down.val.width / 4)
    (hlarge : 5 * parent.down.val.width / 6 < parent.down.val.totalLength)
    (hboundary : boundary ≤ parent.down.val.width / 15)
    (hnext : ∀ j ≤ cutoff, reflectionDyadicExponent U j ≤
      max (parent.down.val.width -
        max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂) 0 + boundary)
    (hadmissible : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      let child := parent.down.val.fixedLineReflectionChild
        (reflectionLongFirst parent.down.val.parameters) U E0 hE0 childOrder x
      admissibleOfInvariant primitive child.data child.parameters) :
    (ℕ × Bool) × ℝ → ULift.{u} (UniversalNode primitive W padding cap) :=
  cutoffReflectionChild parent (reflectionLongFirst parent.down.val.parameters)
    U E0 hE0 childOrder cutoff (fun x hx =>
      parent.down.val.fixedLongReflectionChild_comparison_invariant parent.down.property
        U E0 hU hE0 childOrder x boundary hshort hcore hpadding hlarge hboundary
        (hnext x.1.1 hx) (hadmissible x hx))

theorem comparisonCutoffReflectionChild_geometry
    (parent : ULift.{u} (UniversalNode primitive W padding cap))
    (U E0 : ℝ) (hU : 1 < U) (hE0 : 1 ≤ E0) (childOrder cutoff : ℕ) (boundary : ℝ)
    (hshort : parent.down.val.parameters.n₁ ≤ parent.down.val.width / 4 ∨
      parent.down.val.parameters.n₂ ≤ parent.down.val.width / 4)
    (hcore : parent.down.val.totalLength ≤ parent.down.val.width + padding)
    (hpadding : padding ≤ parent.down.val.width / 4)
    (hlarge : 5 * parent.down.val.width / 6 < parent.down.val.totalLength)
    (hboundary : boundary ≤ parent.down.val.width / 15)
    (hnext : ∀ j ≤ cutoff, reflectionDyadicExponent U j ≤
      max (parent.down.val.width -
        max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂) 0 + boundary)
    (hadmissible : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      let child := parent.down.val.fixedLineReflectionChild
        (reflectionLongFirst parent.down.val.parameters) U E0 hE0 childOrder x
      admissibleOfInvariant primitive child.data child.parameters)
    (weight : ℝ → ℝ) :
    ∀ᵐ x ∂reflectionCommonKernel volume weight cutoff,
      let child := (comparisonCutoffReflectionChild parent U E0 hU hE0 childOrder cutoff
        boundary hshort hcore hpadding hlarge hboundary hnext hadmissible x).down.val
      child.parameters.z = parent.down.val.parameters.z ∧
        child.width = parent.down.val.width ∧ child.totalLength ≤
          3 * parent.down.val.width / 2 - parent.down.val.totalLength +
            2 * parent.down.val.parameters.z + boundary := by
  filter_upwards [ae_reflectionCommonKernel_cutoff volume weight cutoff] with x hx
  dsimp only
  have heq := cutoffReflectionChild_node parent
    (reflectionLongFirst parent.down.val.parameters) U E0 hE0 childOrder cutoff
    (fun y hy => parent.down.val.fixedLongReflectionChild_comparison_invariant
      parent.down.property U E0 hU hE0 childOrder y boundary hshort hcore hpadding
      hlarge hboundary (hnext y.1.1 hy) (hadmissible y hy)) x hx
  change (comparisonCutoffReflectionChild parent U E0 hU hE0 childOrder cutoff boundary
    hshort hcore hpadding hlarge hboundary hnext hadmissible x).down.val = _ at heq
  rw [heq]
  exact ⟨rfl, rfl, parent.down.val.fixedLongReflectionChild_comparison_length U E0 hE0
    childOrder x padding boundary parent.down.property.length hshort hcore hpadding
    (hnext x.1.1 hx)⟩

private theorem normalizedEnergy_eq_ordinary (node : Node K ω ψ)
    (hordinary : node.centered = false) (U t : ℝ) :
    node.normalizedEnergy U t = (Node.ordinary node.data node.parameters).normalizedEnergy U t := by
  have he : node.energy U t = pairedEnergy node.data node.parameters U t := by
    simp only [Node.energy, Node.plainPair, hordinary, Bool.false_eq_true, if_false,
      sub_zero, pairedEnergy]
  change node.energy U t / U ^ node.width =
    (Node.ordinary node.data node.parameters).energy U t / U ^ node.width
  rw [he, Node.ordinary_energy]

private theorem rowRestorationEnergy_nonneg (tail : Bool)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (node : Node K ω ψ) (extra : NonzeroIdeal K → NonzeroIdeal K)
    (V : NonzeroIdeal K → SmoothAnnularTest) (Wshort : IdealTest K)
    (δ U long short : ℝ) (cutoff : ℕ) (hU : 0 < U) :
    0 ≤ rowRestorationEnergy tail S node extra V Wshort δ U long short cutoff := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Real.rpow_nonneg hU.le node.width)

/-- The original functional-equation output transfers to the supported
universal labels. All hypotheses are primitive row/profile/scale facts
and the scalar Mellin-density majorant; the parent energy inequality is
proved by the actual common-kernel theorem. -/
theorem cutoffReflectionChild_estimate
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (hordinary : parent.down.val.centered = false)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
    {δ U E0 Ymax : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4)
    (hU : 1 < U) (hE0 : 1 ≤ E0) (hYmax : 0 < Ymax) (childOrder cutoff : ℕ)
    (hvalid : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      UniversalNodeInvariant primitive W padding cap
        (parent.down.val.fixedLineReflectionChild first U E0 hE0 childOrder x))
    (hmask : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ I,
      parent.down.val.data.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      ∀ t : ℝ, parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u ≠
        heckeNormTwist K t)
    (hprofile : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      (V u).toFun =
        (if first then parent.down.val.data.plainTest₁ else parent.down.val.data.plainTest₂).profile
          u 0)
    (hscale : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      ∀ D ∈ (rowRestorationDeletion S parent.down.val.data extra u).powerset,
      ∀ H : SmoothIdeal (rowRestorationDeletion S parent.down.val.data extra u),
        heckeConductorScale K
            (parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u) *
          (Ideal.absNorm (∏ P ∈ D, P) : ℝ) /
            (U ^ (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂) *
              inorm H.val) ≤ Ymax)
    (weight : ℝ → ℝ) (hm : Measurable weight) (hw : ∀ t, 0 ≤ weight t)
    (hi : Integrable weight)
    (hdensity : ∀ j ∈ Finset.range (cutoff + 1),
      ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ t,
        ‖actualReflectionDensity S parent.down.val.data parent.down.val.parameters first extra V
          U E0 childOrder u j
          (actualReflectionSelectedLine parent.down.val.data parent.down.val.parameters first U u j)
          t‖ ≤ weight t) :
    parent.down.val.normalizedEnergy U 0 ≤
      2 * rowRestorationEnergy true S parent.down.val extra V
        (if first then parent.down.val.data.plainTest₂ else parent.down.val.data.plainTest₁) δ U
        (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂)
        (if first then parent.down.val.parameters.n₂ else parent.down.val.parameters.n₁) cutoff +
      ∫ x, (cutoffReflectionChild parent first U E0 hE0 childOrder cutoff hvalid x).down.val.normalizedEnergy
        U 0 ∂reflectionCommonKernel volume weight cutoff := by
  have he := pairedEnergy_reflection_commonKernel hcomplex S parent.down.val.data
    parent.down.val.parameters first extra V hδ hδsmall hU hE0 hYmax childOrder cutoff
    hmask hcharacter hprofile hscale weight hm hw hi hdensity
  rw [cutoffReflectionChild_integral]
  rw [normalizedEnergy_eq_ordinary parent.down.val hordinary U 0]
  exact he

/-- A complete outer reflection datum produced from the genuine
functional equation and its primitive scalar-density inputs. The common
kernel and literal restoration tail are retained without alteration. -/
def outerCutoffReflectionData
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (σ : ℝ) (hσ : 0 < σ)
    (parent : ULift.{u} (UniversalNode primitive W padding cap))
    (hordinary : parent.down.val.centered = false)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
    {δ U E0 Ymax : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4)
    (hU : 1 < U) (hE0 : 1 ≤ E0) (hYmax : 0 < Ymax) (childOrder cutoff : ℕ)
    (hzero : parent.down.val.parameters.z = 0)
    (hadmissible : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      let child := parent.down.val.fixedLineReflectionChild
        (reflectionLongFirst parent.down.val.parameters) U E0 hE0 childOrder x
      admissibleOfInvariant primitive child.data child.parameters)
    (gap boundary : ℝ) (hgap : 0 ≤ gap)
    (hlong : max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂ ≤
      parent.down.val.width + gap)
    (hnext : ∀ j ≤ cutoff, reflectionDyadicExponent U j ≤
      max (parent.down.val.width -
        max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂) 0 + boundary)
    (hbudget : gap + boundary ≤ padding)
    (hmask : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ I,
      parent.down.val.data.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      ∀ t : ℝ, parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u ≠
        heckeNormTwist K t)
    (hprofile : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      (V u).toFun = (if reflectionLongFirst parent.down.val.parameters then
        parent.down.val.data.plainTest₁ else parent.down.val.data.plainTest₂).profile u 0)
    (hscale : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      ∀ D ∈ (rowRestorationDeletion S parent.down.val.data extra u).powerset,
      ∀ H : SmoothIdeal (rowRestorationDeletion S parent.down.val.data extra u),
        heckeConductorScale K
            (parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u) *
          (Ideal.absNorm (∏ P ∈ D, P) : ℝ) /
            (U ^ (if reflectionLongFirst parent.down.val.parameters then
              parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂) * inorm H.val) ≤ Ymax)
    (weight : ℝ → ℝ) (hm : Measurable weight) (hw : ∀ t, 0 ≤ weight t)
    (hi : Integrable weight)
    (hdensity : ∀ j ∈ Finset.range (cutoff + 1),
      ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ t,
        ‖actualReflectionDensity S parent.down.val.data parent.down.val.parameters
          (reflectionLongFirst parent.down.val.parameters) extra V U E0 childOrder u j
          (actualReflectionSelectedLine parent.down.val.data parent.down.val.parameters
            (reflectionLongFirst parent.down.val.parameters) U u j) t‖ ≤ weight t) :
    CoreReflectionData (Ω := (ℕ × Bool) × ℝ)
      (universalPolynomialSystem.{u} primitive σ W padding cap hσ) parent U 0 padding := by
  let first := reflectionLongFirst parent.down.val.parameters
  let valid := fun (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) =>
    parent.down.val.fixedLongReflectionChild_outer_invariant parent.down.property
      U E0 hU hE0 childOrder x hzero (hadmissible x hx)
  refine {
    kernel := reflectionCommonKernel volume weight cutoff
    finite_kernel := reflectionCommonKernel_finite volume weight cutoff hw hi
    child := outerCutoffReflectionChild parent U E0 hU hE0 childOrder cutoff hzero hadmissible
    remainder := 2 * rowRestorationEnergy true S parent.down.val extra V
      (if first then parent.down.val.data.plainTest₂ else parent.down.val.data.plainTest₁) δ U
      (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂)
      (if first then parent.down.val.parameters.n₂ else parent.down.val.parameters.n₁) cutoff
    remainder_nonneg := mul_nonneg (by norm_num)
      (rowRestorationEnergy_nonneg true S parent.down.val extra V _ δ U _ _ cutoff
        (zero_lt_one.trans hU))
    child_integrable := ?_
    child_geometry := outerCutoffReflectionChild_geometry parent U E0 hU hE0 childOrder
      cutoff hzero hadmissible weight gap boundary hgap hlong hnext hbudget
    estimate := ?_ }
  · exact cutoffReflectionChild_integrable parent first U E0 (zero_lt_one.trans hU) hE0
      childOrder cutoff valid weight hw hi
  · exact cutoffReflectionChild_estimate hcomplex S parent first hordinary extra V hδ hδsmall
      hU hE0 hYmax childOrder cutoff valid hmask hcharacter hprofile hscale weight hm hw hi hdensity

/-- The genuine short-factor or raw-quarter comparison reflection.
Its parent and source are the same ordinary universal label; the local
centering assembly already transports the resulting step to its original
same-schedule parent. -/
def comparisonCutoffReflectionData
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (σ : ℝ) (hσ : 0 < σ)
    (parent : ULift.{u} (UniversalNode primitive W padding cap))
    (hordinary : parent.down.val.centered = false)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
    {δ U E0 Ymax : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4)
    (hU : 1 < U) (hE0 : 1 ≤ E0) (hYmax : 0 < Ymax) (childOrder cutoff : ℕ) (boundary : ℝ)
    (hshort : parent.down.val.parameters.n₁ ≤ parent.down.val.width / 4 ∨
      parent.down.val.parameters.n₂ ≤ parent.down.val.width / 4)
    (hcore : parent.down.val.totalLength ≤ parent.down.val.width + padding)
    (hpadding : padding ≤ parent.down.val.width / 4)
    (hlarge : 5 * parent.down.val.width / 6 < parent.down.val.totalLength)
    (hboundary : boundary ≤ parent.down.val.width / 15)
    (hnext : ∀ j ≤ cutoff, reflectionDyadicExponent U j ≤
      max (parent.down.val.width -
        max parent.down.val.parameters.n₁ parent.down.val.parameters.n₂) 0 + boundary)
    (hadmissible : ∀ x : (ℕ × Bool) × ℝ, x.1.1 ≤ cutoff →
      let child := parent.down.val.fixedLineReflectionChild
        (reflectionLongFirst parent.down.val.parameters) U E0 hE0 childOrder x
      admissibleOfInvariant primitive child.data child.parameters)
    (hmask : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ I,
      parent.down.val.data.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      ∀ t : ℝ, parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u ≠
        heckeNormTwist K t)
    (hprofile : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      (V u).toFun = (if reflectionLongFirst parent.down.val.parameters then
        parent.down.val.data.plainTest₁ else parent.down.val.data.plainTest₂).profile u 0)
    (hscale : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      ∀ D ∈ (rowRestorationDeletion S parent.down.val.data extra u).powerset,
      ∀ H : SmoothIdeal (rowRestorationDeletion S parent.down.val.data extra u),
        heckeConductorScale K
            (parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u) *
          (Ideal.absNorm (∏ P ∈ D, P) : ℝ) /
            (U ^ (if reflectionLongFirst parent.down.val.parameters then
              parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂) * inorm H.val) ≤ Ymax)
    (weight : ℝ → ℝ) (hm : Measurable weight) (hw : ∀ t, 0 ≤ weight t)
    (hi : Integrable weight)
    (hdensity : ∀ j ∈ Finset.range (cutoff + 1),
      ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ t,
        ‖actualReflectionDensity S parent.down.val.data parent.down.val.parameters
          (reflectionLongFirst parent.down.val.parameters) extra V U E0 childOrder u j
          (actualReflectionSelectedLine parent.down.val.data parent.down.val.parameters
            (reflectionLongFirst parent.down.val.parameters) U u j) t‖ ≤ weight t) :
    ReflectedComparisonData (Ω := (ℕ × Bool) × ℝ)
      (universalPolynomialSystem.{u} primitive σ W padding cap hσ) parent parent U 0 boundary := by
  let first := reflectionLongFirst parent.down.val.parameters
  let valid := fun (x : (ℕ × Bool) × ℝ) (hx : x.1.1 ≤ cutoff) =>
    parent.down.val.fixedLongReflectionChild_comparison_invariant parent.down.property
      U E0 hU hE0 childOrder x boundary hshort hcore hpadding hlarge hboundary
      (hnext x.1.1 hx) (hadmissible x hx)
  refine {
    kernel := reflectionCommonKernel volume weight cutoff
    finite_kernel := reflectionCommonKernel_finite volume weight cutoff hw hi
    child := comparisonCutoffReflectionChild parent U E0 hU hE0 childOrder cutoff boundary
      hshort hcore hpadding hlarge hboundary hnext hadmissible
    remainder := 2 * rowRestorationEnergy true S parent.down.val extra V
      (if first then parent.down.val.data.plainTest₂ else parent.down.val.data.plainTest₁) δ U
      (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂)
      (if first then parent.down.val.parameters.n₂ else parent.down.val.parameters.n₁) cutoff
    remainder_nonneg := mul_nonneg (by norm_num)
      (rowRestorationEnergy_nonneg true S parent.down.val extra V _ δ U _ _ cutoff
        (zero_lt_one.trans hU))
    child_integrable := ?_
    child_geometry := comparisonCutoffReflectionChild_geometry parent U E0 hU hE0 childOrder
      cutoff boundary hshort hcore hpadding hlarge hboundary hnext hadmissible weight
    estimate := ?_ }
  · exact cutoffReflectionChild_integrable parent first U E0 (zero_lt_one.trans hU) hE0
      childOrder cutoff valid weight hw hi
  · exact cutoffReflectionChild_estimate hcomplex S parent first hordinary extra V hδ hδsmall
      hU hE0 hYmax childOrder cutoff valid hmask hcharacter hprofile hscale weight hm hw hi hdensity

/-- When the complete reflected series is a terminal, there are no
retained children. The zero kernel has vacuous child geometry, while the
remainder is the literal whole restoration energy proved equal to the
actual parent by the functional equation. A subsequent terminal estimate
uses the real long-length condition; none is assumed here. -/
def wholeReflectionCoreData
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (σ : ℝ) (hσ : 0 < σ)
    (parent : ULift.{u} (UniversalNode primitive W padding cap)) (first : Bool)
    (hordinary : parent.down.val.centered = false)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
    {δ U : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hU : 0 < U) (cutoff : ℕ)
    (hmask : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U, ∀ I,
      parent.down.val.data.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)))
    (hcharacter : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      ∀ t : ℝ, parent.down.val.data.plainBackground * parent.down.val.data.rowCharacter u ≠
        heckeNormTwist K t)
    (hprofile : ∀ u ∈ pairedRows parent.down.val.data parent.down.val.parameters U,
      (V u).toFun =
        (if first then parent.down.val.data.plainTest₁ else parent.down.val.data.plainTest₂).profile
          u 0) :
    CoreReflectionData (Ω := (ℕ × Bool) × ℝ)
      (universalPolynomialSystem.{u} primitive σ W padding cap hσ) parent U 0 padding := by
  refine {
    kernel := 0
    finite_kernel := inferInstance
    child := fun _ => parent
    remainder := rowRestorationEnergy false S parent.down.val extra V
      (if first then parent.down.val.data.plainTest₂ else parent.down.val.data.plainTest₁) δ U
      (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂)
      (if first then parent.down.val.parameters.n₂ else parent.down.val.parameters.n₁) cutoff
    remainder_nonneg := rowRestorationEnergy_nonneg false S parent.down.val extra V _
      δ U _ _ cutoff hU
    child_integrable := by simp
    child_geometry := by simp
    estimate := ?_ }
  have h := pairedEnergy_wholeRestoration_eq hcomplex S parent.down.val.data
    parent.down.val.parameters first extra V hδ hδsmall hU cutoff hmask hcharacter hprofile
  have he : parent.down.val.normalizedEnergy U 0 =
      rowRestorationEnergy false S parent.down.val extra V
        (if first then parent.down.val.data.plainTest₂ else parent.down.val.data.plainTest₁) δ U
        (if first then parent.down.val.parameters.n₁ else parent.down.val.parameters.n₂)
        (if first then parent.down.val.parameters.n₂ else parent.down.val.parameters.n₁) cutoff :=
    (normalizedEnergy_eq_ordinary parent.down.val hordinary U 0).trans h
  change parent.down.val.normalizedEnergy U 0 ≤ _
  simpa only [integral_zero_measure, add_zero] using he.le

end HeckeSkeleton.Moments.EngineInduction
