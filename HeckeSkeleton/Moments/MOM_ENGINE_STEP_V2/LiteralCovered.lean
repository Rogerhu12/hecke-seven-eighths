import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralTransforms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondLogChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondChartAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CoveredStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PatternRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonScalarReweight
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridZeroRowSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalOrbitFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralCalibration

set_option linter.unusedSectionVars false

/-!
# Literal coefficients of the two canonical logarithmic charts

These identities read the actual chart fields. The first source keeps
its inverse original residual norm and its true fixed divisor phase.
The second source keeps the full post-pool ideal norm and the inverse
of the chosen empty-mask unit. No equality of complete polynomials is
an input.

The common-support identities at the end remove the earlier internal
divisor test on an actual active common block. The required common
divisibility is provided by `activeCommon_old_mask`; it is a statement
about original ideals, before the second Cauchy estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (left : Finset ι) (right : Finset κ)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (c : ι → ℂ) (e : κ → ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r})
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)

namespace FirstBlockProfileChart

variable (D : Finset (HeightOneSpectrum A.R))

/-- The first original left coefficient, with its actual divisor
factor, in the inverse-norm form used by the one prime pool. -/
theorem canonicalLog_leftSourceCoefficient
    (i : ι) (hi : A.IsAllowed C.correction.B
      (Units.mk0 (b.leftGenerator i : K)
        (by exact_mod_cast (b.left_generates i).1))) :
    (canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδhalf).leftCoefficient i *
      firstLeftDivisorFactor
        (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i)
          (b.leftGenerator i) (b.left_generates i))
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val =
      (c i * ((A.exteriorNorm (b.leftResidual i) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.leftResidual i).val
          (CanonicalLiteralFirstPhase.leftElement C b.primes
            b.leftMultiplicity b.rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)) /
        (A.exteriorNorm (b.leftResidual i) : ℂ) := by
  sorry

/-- The right coefficient uses the positive complementary sextic
exponents. Its inverse norm is the same original right residual norm. -/
theorem canonicalLog_rightSourceCoefficient
    (j : κ) (hj : A.IsAllowed C.correction.B
      (Units.mk0 (b.rightGenerator j : K)
        (by exact_mod_cast (b.right_generates j).1))) :
    (canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδhalf).rightCoefficient j *
      firstRightDivisorFactor
        (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j)
          (b.rightGenerator j) (b.right_generates j))
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val =
      (e j * ((A.exteriorNorm (b.rightResidual j) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.rightResidual j).val
          (CanonicalLiteralFirstPhase.rightElement C b.primes
            b.leftMultiplicity b.rightMultiplicity
            (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)) /
        (A.exteriorNorm (b.rightResidual j) : ℂ) := by
  sorry

end FirstBlockProfileChart

namespace SecondBlockProfileChart

variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (rowLabelCount : ℕ)
variable (rowLabel : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
  Fin (rowLabelCount + 1))
variable (hleft : ∀ i ∈ b.leftColumns left,
  IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅).val)
variable (hright : ∀ j ∈ b.rightColumns right,
  IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅).val)

/-- The empty row mask leaves its genuine chosen unit phase. The full
post-pool ideal, before second common extraction, supplies the norm tilt. -/
theorem canonicalLog_empty_leftSourceCoefficient (i : ι) :
    (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e finiteTest hlc hcs
        radius ∅ rowLabelCount rowLabel hleft hright δ hδ hδhalf).sourceLeftCoefficient i =
      c i * ((A.exteriorNorm (b.secondLeftIdeal i) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.secondLeftIdeal i).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  sorry

theorem canonicalLog_empty_rightSourceCoefficient (j : κ) :
    (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e finiteTest hlc hcs
        radius ∅ rowLabelCount rowLabel hleft hright δ hδ hδhalf).sourceRightCoefficient j =
      e j * ((A.exteriorNorm (b.secondRightIdeal j) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.secondRightIdeal j).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  sorry

theorem canonicalLog_empty_leftSourceCoefficient_on_columns
    (i : ι) (hi : i ∈ b.leftColumns left) :
    (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e finiteTest hlc hcs
        radius ∅ rowLabelCount rowLabel hleft hright δ hδ hδhalf).sourceLeftCoefficient i =
      c i * ((A.exteriorNorm (fullI i) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (fullI i).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  sorry

theorem canonicalLog_empty_rightSourceCoefficient_on_columns
    (j : κ) (hj : j ∈ b.rightColumns right) :
    (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e finiteTest hlc hcs
        radius ∅ rowLabelCount rowLabel hleft hright δ hδ hδhalf).sourceRightCoefficient j =
      e j * ((A.exteriorNorm (fullJ j) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (fullJ j).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  sorry

end SecondBlockProfileChart

namespace FirstCommonCharacterBlock

/-- On an active common block the earlier squarefree divisor is
already a factor of every actual complete left column. -/
theorem left_divisor_of_common (S : Ideal (𝓞 K)) (hS : S ∣ DE.1)
    (i : ι) (hi : i ∈ b.leftColumns left) : S ∣ (fullI i).val := by
  sorry

theorem right_divisor_of_common (S : Ideal (𝓞 K)) (hS : S ∣ DE.2)
    (j : κ) (hj : j ∈ b.rightColumns right) : S ∣ (fullJ j).val := by
  sorry

theorem left_divisor_filter_eq (S : Ideal (𝓞 K)) (hS : S ∣ DE.1)
    (f : ι → ℂ) (i : ι) (hi : i ∈ b.leftColumns left) :
    (if S ∣ (fullI i).val then f i else 0) = f i := by
  sorry

theorem right_divisor_filter_eq (S : Ideal (𝓞 K)) (hS : S ∣ DE.2)
    (f : κ → ℂ) (j : κ) (hj : j ∈ b.rightColumns right) :
    (if S ∣ (fullJ j).val then f j else 0) = f j := by
  sorry

end FirstCommonCharacterBlock
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Computed common-atom extraction of the literal two-stage leaf

The inputs are the individual original atom tables and the actual two
support-extraction branches. The complete coefficients, both ordinary
rectangles, the common scalars and their row reweighting are computed.
The source is the existing `fullCorrelationHybridLeaf`, on the original
allocation label and both unchanged Fourier kernels.

The two original logarithmic coordinates keep the pool prime power and
the second common ideal. Their constant row translations disappear
only inside the proved column norms. Neither Fourier variable changes.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralCommonLeaf

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k l : ℕ}
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (left : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (right : CanonicalLiteralRectangles.Atoms (K := K) l)
variable {support : Finset (Ideal (𝓞 K))}
variable (bL : SupportCartesianBranch (left).plain₁ (left).plain₂ (left).slots support)
variable (bR : SupportCartesianBranch (right).plain₁ (right).plain₂ (right).slots support)
variable (IL : AllocationColumn K bL.keep.card → A.Exterior)
variable (IR : AllocationColumn K bR.keep.card → A.Exterior)
variable (b : liveSecondAllocationBranches (Ray := PUnit.{1})
  ((left).extract bL).plain₁ ((left).extract bL).plain₂ ((left).extract bL).slots
  ((right).extract bR).plain₁ ((right).extract bR).plain₂ ((right).extract bR).slots IR)
variable (exceptional : H → Prop)
variable (F₁ F₂ : SchwartzMap ℝ ℂ)
variable (power : A.Exterior) (firstSign : ℝ) (rowLog : H → ℝ)

local instance canonicalLiteralCommonLeafCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

/-- This is the existing finite hybrid source with its computed whole
coefficients. Both fixed common atoms are still inside the columns. -/
def sourceLeaf : ActualHybridLeaf K H ℝ ℝ :=
  fullCorrelationHybridLeaf F₁ F₂ R.rows
    ((left).extract bL).plain₁ ((left).extract bL).plain₂ ((left).extract bL).slots
    ((right).extract bR).plain₁ ((right).extract bR).plain₂ ((right).extract bR).slots
    (fun j => (IR j).val) (fun h => R.weight h * R.correlation h)
    (fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)))
    (fun χ h i => (left).whole (bL.reconstruct i) *
      (fixedLeftPhase PUnit.{1} χ PUnit.unit : ℂ) *
        σ (A.sexticResidue (IL i) (R.frequency h)))
    (fun χ h j => (right).whole (bR.reconstruct j) *
      (fixedRightPhase PUnit.{1} χ PUnit.unit : ℂ) *
        σ (A.sexticResidue (IR j) (-R.frequency h)))
    (fun _ i => -firstSign * Real.log
      (Ideal.absNorm (power.val * allocationColumnIdeal (bL.reconstruct i)) : ℝ))
    (fun h i => rowLog h - Real.log
      (Ideal.absNorm (allocationColumnIdeal (bL.reconstruct i)) : ℝ))
    (fun _ j => -firstSign * Real.log
      (Ideal.absNorm (power.val * allocationColumnIdeal (bR.reconstruct j)) : ℝ))
    (fun _ j => -Real.log
      (Ideal.absNorm (allocationColumnIdeal (bR.reconstruct j)) : ℝ))
    (fun _ _ _ _ => exceptional) b.val

private theorem left_mem_residual
    (i : AllocationColumn K bL.keep.card)
    (hi : i ∈ b.val.leftColumns
      ((left).extract bL).plain₁ ((left).extract bL).plain₂ ((left).extract bL).slots) :
    i ∈ bL.residualColumns := by
  sorry

private theorem right_mem_residual
    (j : AllocationColumn K bR.keep.card) (hj : j ∈ b.val.rightColumns) :
    j ∈ bR.residualColumns := by
  sorry

/-- The same second common scalar is extracted from both centered
rectangles, by the individual occurrence product proved earlier. -/
def extraction :
    (sourceLeaf R left right bL bR IL IR b exceptional F₁ F₂ power firstSign rowLog).ConstantAtomExtraction where
  leftScalar := (left).commonScalar bL
  rightScalar := (right).commonScalar bR
  leftResidual := secondAllocatedLeftCoefficient (σ := σ) PUnit.{1} IL R.frequency
    (fun _ => PUnit.unit) b.val.2.1 ((left).extract bL).whole
  rightResidual := fun h j => star (secondAllocatedRightCoefficient (σ := σ) PUnit.{1}
    IR R.frequency (fun _ => PUnit.unit) b.val.2.1 ((right).extract bR).whole h j)
  left h _ i hi := by
    change (left).whole (bL.reconstruct i) * _ * _ = _
    rw [(left).extract_whole bL i (left_mem_residual left right bL bR IR b i hi)]
    dsimp only [secondAllocatedLeftCoefficient]
    ring
  right h _ j hj := by
    change (right).whole (bR.reconstruct j) * _ * _ = _
    rw [(right).extract_whole bR j (right_mem_residual left right bL bR IR b j hj)]
    simp only [secondAllocatedRightCoefficient, star_star]
    ring

/-- The two constants are moved into the original row weight. Every
frequency, generator, classification and original ideal is unchanged. -/
def commonRows : ActualSecondCorrelationRows A σ H ι :=
  { R with weight := fun h =>
      R.weight h * (left).commonScalar bL * star ((right).commonScalar bR) }

variable (hIL : ∀ i ∈ childCartesianColumns
    ((left).extract bL).plain₁ ((left).extract bL).plain₂ ((left).extract bL).slots,
  (IL i).val = allocationColumnIdeal i)
variable (hIR : ∀ j ∈ childCartesianColumns
    ((right).extract bR).plain₁ ((right).extract bR).plain₂ ((right).extract bR).slots,
  (IR j).val = allocationColumnIdeal j)

/-- Actual two-rectangle factors of the reweighted source. The right
first coordinate has the sign imposed by its stored conjugate column. -/
def rectangles :=
  CanonicalLiteralRectangles.rectangles (commonRows R left right bL bR)
    ((left).extract bL) ((right).extract bR) IL IR hIL hIR b exceptional firstSign (-firstSign)

/-- Exact binding to the same source leaf. The translations are
calculated from the original pool power and common occurrence ideals. -/
def ordinaryBinding :
    (extraction R left right bL bR IL IR b exceptional F₁ F₂ power firstSign rowLog).leaf.OrdinaryBinding (rectangles R left right bL bR IL IR b exceptional firstSign hIL hIR) where
  rows := Finset.Subset.refl _
  rows_zero h hh hn := False.elim (hn hh)
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight h _ := by
    change (R.weight h * R.correlation h) * (left).commonScalar bL *
        star ((right).commonScalar bR) =
      (R.weight h * (left).commonScalar bL * star ((right).commonScalar bR)) * R.correlation h
    ring
  leftCoefficient _ _ _ _ := rfl
  rightCoefficient h _ j _ := by
    change star (star (secondAllocatedRightCoefficient (A := A) (σ := σ) PUnit.{1}
        IR R.frequency (fun _ => PUnit.unit) b.val.2.1 ((right).extract bR).whole h j)) =
      secondAllocatedRightCoefficient (A := A) (σ := σ) PUnit.{1}
        IR R.frequency (fun _ => PUnit.unit) b.val.2.1 ((right).extract bR).whole h j
    exact star_star _
  leftPoint h _ := by
    refine ⟨WithLp.toLp 2
      (-firstSign * Real.log (Ideal.absNorm (power.val * bL.literalExtractedIdeal) : ℝ),
        rowLog h - Real.log (Ideal.absNorm bL.literalExtractedIdeal : ℝ)), ?_⟩
    intro i hi
    have hm := left_mem_residual left right bL bR IR b i hi
    have hp := Finset.mem_product.mp (Finset.mem_product.mp hm).1
    have h₁ := ((left).extract bL).plain₁_nonzero i.1.1 hp.1
    have h₂ := ((left).extract bL).plain₂_nonzero i.1.2 hp.2
    apply CanonicalLiteralLocations.actual_product_locations firstSign (rowLog h)
      i h₁ h₂
      (power.val * allocationColumnIdeal (bL.reconstruct i))
      (allocationColumnIdeal (bL.reconstruct i))
      (power.val * bL.literalExtractedIdeal) bL.literalExtractedIdeal
      (mul_ne_zero power.property.1 bL.literalExtractedIdeal_ne_zero)
      bL.literalExtractedIdeal_ne_zero
    · exact (congrArg (fun I : Ideal (𝓞 K) => power.val * I)
        (bL.reconstruct_literalIdeal i hm)).trans
          (mul_assoc power.val bL.literalExtractedIdeal (allocationColumnIdeal i)).symm
    · exact bL.reconstruct_literalIdeal i hm
  rightPoint h _ := by
    refine ⟨WithLp.toLp 2
      (firstSign * Real.log (Ideal.absNorm (power.val * bR.literalExtractedIdeal) : ℝ),
        -Real.log (Ideal.absNorm bR.literalExtractedIdeal : ℝ)), ?_⟩
    intro j hj
    have hm := right_mem_residual left right bL bR IR b j hj
    have hp := Finset.mem_product.mp (Finset.mem_product.mp hm).1
    have h₁ := ((right).extract bR).plain₁_nonzero j.1.1 hp.1
    have h₂ := ((right).extract bR).plain₂_nonzero j.1.2 hp.2
    have he := CanonicalLiteralLocations.actual_product_locations (-firstSign) 0
      j h₁ h₂
      (power.val * allocationColumnIdeal (bR.reconstruct j))
      (allocationColumnIdeal (bR.reconstruct j))
      (power.val * bR.literalExtractedIdeal) bR.literalExtractedIdeal
      (mul_ne_zero power.property.1 bR.literalExtractedIdeal_ne_zero)
      bR.literalExtractedIdeal_ne_zero
      ((congrArg (fun I : Ideal (𝓞 K) => power.val * I)
        (bR.reconstruct_literalIdeal j hm)).trans
          (mul_assoc power.val bR.literalExtractedIdeal (allocationColumnIdeal j)).symm)
      (bR.reconstruct_literalIdeal j hm)
    change WithLp.toLp 2
        (-(-firstSign * Real.log
          (Ideal.absNorm (power.val * allocationColumnIdeal (bR.reconstruct j)) : ℝ)),
          -Real.log (Ideal.absNorm (allocationColumnIdeal (bR.reconstruct j)) : ℝ)) =
      WithLp.toLp 2
          (firstSign * Real.log (Ideal.absNorm (power.val * bR.literalExtractedIdeal) : ℝ),
            -Real.log (Ideal.absNorm bR.literalExtractedIdeal : ℝ)) +
        rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.prime (-firstSign)) j
    simp only [neg_neg, zero_sub, neg_mul] at he ⊢
    exact he

/-- Only genuinely nonzero complete correlations enter the arithmetic
row calibration. The literal finite source itself is not filtered. -/
def supportedRows : ActualSecondCorrelationRows A σ H ι :=
  (commonRows R left right bL bR).restrictRows (fun h => R.correlation h ≠ 0)

def supportedRectangles :=
  CanonicalLiteralRectangles.rectangles (supportedRows R left right bL bR)
    ((left).extract bL) ((right).extract bR) IL IR hIL hIR b exceptional firstSign (-firstSign)

/-- Correlation-zero rows are omitted by an exact zero-summand identity,
while both computed logarithmic translations remain unchanged. This is
the binding used by the same canonical row-mass and capacity records. -/
def supportedOrdinaryBinding :
    (extraction R left right bL bR IL IR b exceptional F₁ F₂ power firstSign rowLog).leaf.OrdinaryBinding (supportedRectangles R left right bL bR IL IR b exceptional
        firstSign hIL hIR) where
  rows h hh := by
    letI : DecidablePred (fun a : H => R.correlation a ≠ 0) :=
      fun a => Classical.propDecidable (R.correlation a ≠ 0)
    exact ((Finset.mem_filter (p := fun a : H => R.correlation a ≠ 0)
      (s := R.rows) (a := h)).mp hh).1
  rows_zero h hh hn := by
    letI : DecidablePred (fun a : H => R.correlation a ≠ 0) :=
      fun a => Classical.propDecidable (R.correlation a ≠ 0)
    have hc : R.correlation h = 0 := by
      by_contra hc
      exact hn ((Finset.mem_filter (p := fun a : H => R.correlation a ≠ 0)
        (s := R.rows) (a := h)).mpr ⟨hh, hc⟩)
    change (R.weight h * R.correlation h) * (left).commonScalar bL *
      star ((right).commonScalar bR) = 0
    simp only [hc, mul_zero, zero_mul]
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).rowWeight
  leftCoefficient := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).leftCoefficient
  rightCoefficient := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).rightCoefficient
  leftPoint := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).leftPoint
  rightPoint := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).rightPoint

/-- The row record above is exactly the record consumed by the genuine
common-atom mass budget when its primitive single-atom windows are given. -/
theorem commonRows_eq_withCommonAtoms
    (BL : bL.CommonAtomBounds (left).characters (left).base (left).length (left).slotWeight)
    (BR : bR.CommonAtomBounds (right).characters (right).base (right).length (right).slotWeight)
    (CL CR : A.Exterior)
    (hCL : bL.literalExtractedIdeal = CL.val)
    (hCR : bR.literalExtractedIdeal = CR.val) :
    commonRows R left right bL bR =
      R.withCommonAtoms (BL.atoms R.rows) (BR.atoms R.rows) := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralCommonLeaf

end

set_option profiler true
set_option profiler.threshold 1000

/-!
# Literal common extraction on the stored covered leaf

This module acts on `CoveredClassKey.leaf` itself.  It reads the two
existing atlas branches, transports only their support proofs and
extracts their actual common occurrences.  The finite allocation is
the stored leaf's original allocation.  The two kernels, its outer
weight and its complete original physical row set are retained.

The local coefficient arguments below are the individual chart-field
identities supplied by the canonical original-atom calculations. They
are used before any polynomial sum, norm or positive estimate. This
module is their structural adapter, not a replacement raw-source
assumption or a second choice of source/children.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}

local instance canonicalLiteralCoveredLeafCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

private theorem literalCommonFibre_nonempty
    {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal)
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (d : T.labels P D) :
    (T.commonFibre P D d).Nonempty := by
  sorry

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey s) LC RC)

abbrev literalLeftParent := LC.branch v.2.2.1
abbrev literalRightParent := RC.branch v.2.2.2.1

abbrev literalLeftBranch :=
  (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftParent v).branch (primeSupport v.1.val.1) v.1.val.1 v.2.2.2.2.2.1

abbrev literalRightBranch :=
  (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightParent v).branch (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2

/-- These atlas objects reuse the stored residual index, including all
its original support transports. Only nonemptiness is proved here. -/
def literalLeftResidualAtlas : SourceCartesianAtlas
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftParent v).commonFibre (primeSupport v.1.val.1) v.1.val.1 v.2.2.2.2.2.1)
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftResidual :=
  SourceCartesianAtlas.ofReindex (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v)
    (literalCommonFibre_nonempty (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftParent v)
      (primeSupport v.1.val.1) v.1.val.1 v.2.2.2.2.2.1)

def literalRightResidualAtlas : SourceCartesianAtlas
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightParent v).commonFibre (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2)
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightResidual :=
  SourceCartesianAtlas.ofReindex (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v)
    (literalCommonFibre_nonempty (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightParent v)
      (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2)

variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)

abbrev literalLeftOriginal := leftAtoms.onAtlas (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftParent v) rfl
abbrev literalRightOriginal := rightAtoms.onAtlas (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightParent v) rfl

/-- The complete original Gauss product stays in the actual residual
atom table. The common scalar is extracted separately exactly once. -/
def literalLeftAtoms : CanonicalLiteralRectangles.Atoms (K := K) (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftSlots v) :=
  (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftOriginal v) leftAtoms).extract (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftBranch v)).onAtlas
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftResidualAtlas v) rfl

def literalRightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v).keep.card :=
  (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightOriginal v) rightAtoms).extract (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v)).onAtlas
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightResidualAtlas v) rfl

@[simp] theorem literalLeftAtoms_whole (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftSlots v)) :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).whole i =
      (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftOriginal v) leftAtoms).extract (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftBranch v)).whole i := by
  sorry

@[simp] theorem literalRightAtoms_whole
    (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v).keep.card) :
    (no_index ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms)).whole i =
      (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightOriginal v) rightAtoms).extract (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v)).whole i := by
  sorry

theorem literalLeft_cartesian (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftSlots v)) :
    i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).cartesian ↔ i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftBranch v).residualColumns := by
  sorry

theorem literalRight_cartesian (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v).keep.card) :
    i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).cartesian ↔ i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v).residualColumns := by
  sorry

theorem literalLeft_index_common (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftSlots v))
    (hi : i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).cartesian) :
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).index i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftColumns G.columns := by
  sorry

theorem literalRight_index_common (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v).keep.card)
    (hi : i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).cartesian) :
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightColumns G.columns := by
  sorry

variable (exceptional : s.CoverHybridPredicates LC RC)
variable (F : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.AllocationKey v))

private theorem literal_left_mem (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftSlots v))
    (hi : i ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).left) : i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).cartesian := by
  sorry

private theorem literal_right_mem (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v).keep.card)
    (hi : i ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).right) : i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).cartesian := by
  sorry

variable (leftCoefficient : ∀ i ∈ (LC.branch v.2.2.1).reindex.cartesian,
  (LC.branch v.2.2.1).reindex.index i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftColumns G.columns →
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).sourceLeftCoefficient ((LC.branch v.2.2.1).reindex.index i) = leftAtoms.whole i)
variable (rightCoefficient : ∀ i ∈ (RC.branch v.2.2.2.1).reindex.cartesian,
  (RC.branch v.2.2.2.1).reindex.index i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightColumns G.columns →
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).sourceRightCoefficient ((RC.branch v.2.2.2.1).reindex.index i) = rightAtoms.whole i)

include leftCoefficient in
private theorem literal_left_coefficient
    (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftSlots v)) (hi : i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).cartesian) :
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).sourceLeftCoefficient ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).index i) =
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftOriginal v) leftAtoms).commonScalar (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftBranch v) *
        ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).whole i := by
  sorry

include rightCoefficient in
private theorem literal_right_coefficient
    (i : AllocationColumn K (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v).keep.card)
    (hi : i ∈ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).cartesian) :
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).sourceRightCoefficient ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i) =
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightOriginal v) rightAtoms).commonScalar (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v) *
        ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).whole i := by
  sorry

/-- The extraction is attached to the original stored finite leaf.
All coefficient equalities are proved at its actual allocated columns. -/
def literalExtraction : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).ConstantAtomExtraction where
  leftScalar := ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftOriginal v) leftAtoms).commonScalar (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftBranch v)
  rightScalar := ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightOriginal v) rightAtoms).commonScalar (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v)
  leftResidual := secondAllocatedLeftCoefficient (σ := σ) PUnit.{1}
    (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).index i))
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).frequency
    (fun _ => PUnit.unit) j.2.1 ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms).whole
  rightResidual := fun h i => star (secondAllocatedRightCoefficient (σ := σ) PUnit.{1}
    (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i))
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).frequency
    (fun _ => PUnit.unit) j.2.1 ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).whole h i)
  left h _ i hi := by
    change (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).sourceLeftCoefficient ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).index i) * _ * _ = _
    rw [(HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literal_left_coefficient v) leftAtoms leftCoefficient i
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literal_left_mem v) exceptional F x j i hi)]
    dsimp only [secondAllocatedLeftCoefficient]
    ring
  right h _ i hi := by
    change (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).sourceRightCoefficient ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i) * _ * _ = _
    rw [(HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literal_right_coefficient v) rightAtoms rightCoefficient i
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literal_right_mem v) exceptional F x j i hi)]
    simp only [secondAllocatedRightCoefficient, star_star]
    ring

/-- This reweighting is the one forced by the two constants just
extracted from the stored whole coefficients. -/
def literalRows : ActualSecondCorrelationRows A σ
    (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) (Fin (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primeCount) :=
  { (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v) with
    weight := fun h =>
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).weight h *
        ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftOriginal v) leftAtoms).commonScalar (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftBranch v) *
        star (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightOriginal v) rightAtoms).commonScalar (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v)) }

def literalSupportedRows : ActualSecondCorrelationRows A σ
    (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) (Fin (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primeCount) :=
  ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRows v) leftAtoms rightAtoms).restrictRows (fun h =>
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).correlation h ≠ 0)

/-- Nonempty original allocated columns and squarefreeness come from
the stored live leaf. No fresh allocation or nonempty-source premise
is chosen for its child. -/
def literalAllocation (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).Live) :
    liveSecondAllocationBranches (Ray := PUnit.{1})
      (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).plain₁ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).plain₂ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).slots
      (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).plain₁ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).plain₂ (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).slots
      (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i)) := by
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩⟩
  · by_contra hn
    apply hlive.1
    change ‖(moebius j.1.val : ℂ)‖ * _ = 0
    simp only [moebius_of_not_squarefree hn, Int.cast_zero, norm_zero, zero_mul]
  · obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.1
    exact ⟨i, hi⟩
  · obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.2
    exact ⟨i, hi⟩

/-- Both rectangles now belong to the exact same stored allocation and
the exact original correlation support. -/
def literalRectangles (firstSign : ℝ) (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).Live) :=
  CanonicalLiteralRectangles.rectangles ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRows v) leftAtoms rightAtoms)
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftAtoms v) leftAtoms) ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms)
    (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).index i))
    (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i))
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leftReindex v).ideal_product (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).ideal_product
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalAllocation v) exceptional F x j hlive)
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).exceptional firstSign (-firstSign)

variable (firstSign : ℝ) (hlive : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).Live)
variable (leftPoint : ∀ h ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).left,
    WithLp.toLp 2 (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).leftFirst h i,
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).leftSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.prime firstSign) i)
variable (rightPoint : ∀ h ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).right,
    WithLp.toLp 2 (-((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).rightFirst h i,
      ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).rightSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.prime (-firstSign)) i)

/-- The ordinary binding is attached to the extracted original leaf,
not to a separately manufactured finite polynomial. The only omitted
rows have their original full correlation equal to zero. -/
def literalOrdinaryBinding :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalExtraction v) leftAtoms rightAtoms exceptional F x j
      leftCoefficient rightCoefficient).leaf.OrdinaryBinding
        ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRectangles v) leftAtoms rightAtoms exceptional F x j firstSign hlive) where
  rows h hh := (Finset.mem_filter.mp hh).1
  rows_zero h hh hn := by
    have hc : ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).correlation h = 0 := by
      by_contra hc
      exact hn (Finset.mem_filter.mpr ⟨hh, hc⟩)
    change ((_ * ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).correlation h) *
      _ * _) = 0
    simp only [hc, mul_zero, zero_mul]
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight h _ := by
    change ((_ * _) * _ * _) = ((_ * _ * _) * _)
    ring
  leftCoefficient _ _ _ _ := rfl
  rightCoefficient h _ i _ := by
    change star (star (secondAllocatedRightCoefficient (A := A) (σ := σ) PUnit.{1}
        (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i))
        ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).frequency
        (fun _ => PUnit.unit) j.2.1 ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).whole h i)) =
      secondAllocatedRightCoefficient (A := A) (σ := σ) PUnit.{1}
        (fun i => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightResidual ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rightReindex v).index i))
        ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).frequency
        (fun _ => PUnit.unit) j.2.1 ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightAtoms v) rightAtoms).whole h i
    exact star_star _
  leftPoint := leftPoint
  rightPoint := rightPoint

@[simp] theorem literalExtraction_firstKernel :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalExtraction v) leftAtoms rightAtoms exceptional F x j
      leftCoefficient rightCoefficient).leaf.firstKernel = F := rfl

@[simp] theorem literalExtraction_secondKernel :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalExtraction v) leftAtoms rightAtoms exceptional F x j
      leftCoefficient rightCoefficient).leaf.secondKernel = (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).kernel := rfl

@[simp] theorem literalExtraction_outerWeight :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalExtraction v) leftAtoms rightAtoms exceptional F x j
      leftCoefficient rightCoefficient).leaf.weight = ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.leaf v) exceptional F x j).weight := rfl

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Actual row mass on the original nonzero correlation support

The original row classifier fixes the divided nonunit pattern. The unit
radical is its complement only on nonzero correlations; zero correlations
must therefore be removed before populating `ActualSecondRowMass`.

The row restriction here is exactly the zero-removal identity proved in
`HybridZeroRowSupport`. No row bound or aggregate source identity is a
premise. The canonical constructor uses the original chart, its original
common atoms and its individual profile window, computes both radical
ideals from the already fixed pattern, and proves the original fibre
bound with `Γ.index`. Neither a live nor an ordinary row is required.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]

namespace ActualSecondRowMass

/-- Build the original mass dictionary after deleting only genuine
correlation-zero rows. The unit/nonunit fields follow from the original
local classification; the caller supplies neither radical identity. -/
def ofCorrelationSupportedPattern
    {H ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ActualSecondCorrelationRows A σ H ι)
    (C : A.GeneralArithmeticContext σ η hS) {kLeft kRight : ℕ}
    (left : FrozenSourceAtoms A σ H R.rows kLeft)
    (right : FrozenSourceAtoms A σ H R.rows kRight)
    (hleft : (left).ideal = (primePowerProduct R.primes R.leftMultiplicity).val)
    (hright : (right).ideal = (primePowerProduct R.primes R.rightMultiplicity).val)
    (pattern : ι → Bool)
    (hpattern : ∀ h ∈ R.rows, actualNonunitPattern C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h) = pattern)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (profile : H → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hprofile : ∀ h ∈ R.rows, ‖profile h‖ ≤ B)
    (hweight : ∀ h ∈ R.rows,
      R.weight h = secondOrbitalScalar (K := K) (S := A.Sf) radius mask * profile h)
    (hpositive : ∀ i, 0 < R.leftMultiplicity i)
    (fiber : ℕ) (hfiber : ∀ I : Ideal (𝓞 K),
      (R.rows.filter (fun h => (R.originalIdeal h).val = I)).card ≤ fiber) :
    ActualSecondRowMass
      ((R.withCommonAtoms left right).restrictRows (fun h => R.correlation h ≠ 0))
      C kLeft kRight := by
  let left' := (left).onRows R.live (Finset.filter_subset _ _)
  let right' := (right).onRows R.live (Finset.filter_subset _ _)
  refine ofCommonAtoms (R.restrictRows (fun h => R.correlation h ≠ 0)) C
    left' right' hleft hright radius mask profile B hB
    (fun h hh => hprofile h (Finset.mem_filter.mp hh).1)
    (fun h hh => hweight h (Finset.mem_filter.mp hh).1)
    (secondPatternUnitIdeal R.primes R.leftMultiplicity R.rightMultiplicity pattern)
    (secondPatternNonunitIdeal R.primes pattern) ?_ ?_ hpositive fiber ?_
  · intro h hh
    exact (R.secondPatternUnitIdeal_eq_live C pattern ⟨h, hh⟩
      (hpattern h (Finset.mem_filter.mp hh).1)).symm
  · intro h hh
    exact (R.secondPatternNonunitIdeal_eq C pattern h
      (hpattern h (Finset.mem_filter.mp hh).1)).symm
  · intro I
    apply le_trans (Finset.card_le_card ?_) (hfiber I)
    intro h hh
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1,
        (Finset.mem_filter.mp hh).2⟩

end ActualSecondRowMass

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)
variable (hclass : (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.NonunitLabelStable chart))
variable (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
variable (label : Fin (chart.rowLabelCount + 1))
variable {kLeft kRight : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kLeft)
variable (rightAtoms : FrozenSourceAtoms A σ
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
  (chart.actualRows M X hX label).rows kRight)
variable (hleft : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hright : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ q ∈ (chart.actualRows M X hX label).rows, ‖chart.weight q‖ ≤ bound)

/-- This is the actual chart calibration, including empty original or
ordinary classes. Both ideal radicals and the fibre bound are proved
from the original classifier and original orbit map, before children
are normalized or selected. -/
def actualRowsSupportedMass :
    ActualSecondRowMass
      (((chart.actualRows M X hX label).withCommonAtoms leftAtoms rightAtoms).restrictRows
        (fun q => (chart.actualRows M X hX label).correlation q ≠ 0))
      C kLeft kRight :=
  ActualSecondRowMass.ofCorrelationSupportedPattern
    (chart.actualRows M X hX label) C leftAtoms rightAtoms hleft hright
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) M X hX label)
    (fun q hq => (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRows_originalNonunitPattern chart) hclass M X hX label ⟨q, hq⟩)
    radius D chart.weight bound hbound hprofile (fun _ _ => rfl)
    b.left_positive Γ.index (chart.actualRows_original_fibers M X hX label)

@[simp] theorem actualRowsSupportedMass_unitIdeal :
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRowsSupportedMass chart) hclass M X hX label leftAtoms rightAtoms hleft hright
      bound hbound hprofile).unitIdeal =
      secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity
        ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) M X hX label) := rfl

@[simp] theorem actualRowsSupportedMass_nonunitIdeal :
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRowsSupportedMass chart) hclass M X hX label leftAtoms rightAtoms hleft hright
      bound hbound hprofile).nonunitIdeal =
      secondPatternNonunitIdeal b.primes ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) M X hX label) := rfl

@[simp] theorem actualRowsSupportedMass_originalFiber :
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRowsSupportedMass chart) hclass M X hX label leftAtoms rightAtoms hleft hright
      bound hbound hprofile).originalFiber = Γ.index := rfl

@[simp] theorem actualRowsSupportedMass_commonEnvelope :
    ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRowsSupportedMass chart) hclass M X hX label leftAtoms rightAtoms hleft hright
      bound hbound hprofile).commonEnvelope =
      bound * Real.sqrt leftAtoms.envelope * Real.sqrt rightAtoms.envelope := rfl

/-- The later ordinary predicate changes only the original finite row
proofs. Its computed pattern ideals and fixed orbit fibre are retained. -/
theorem actualRowsSupportedMass_ordinary_fields
    (exceptional : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop) :
    let W := ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRowsSupportedMass chart) hclass M X hX label leftAtoms rightAtoms
      hleft hright bound hbound hprofile).restrictRows (fun q => ¬exceptional q)
    W.unitIdeal = secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity
        ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) M X hX label) ∧
      W.nonunitIdeal = secondPatternNonunitIdeal b.primes
        ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern chart) M X hX label) ∧
      W.originalFiber = Γ.index := by
  sorry

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Canonical arithmetic mass of the same literal common rows

Both common atom dictionaries are computed from the actual occurrence
branches. Their values are exactly the two constants extracted from the
original whole columns. Reweighting the rows by those constants is
therefore the same reweighting used by the original row-mass theorem.

The original nonunit classifier fixes both radicals on nonzero
correlations, and the original orbit map proves the fibre Γ.index.
Only the individual original row-profile window is supplied. No bound
on a whole row weight, a fibre cardinality, a child or a source is input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey s) LC RC)

variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (leftMask : (HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.MaskIndicator leftAtoms.characters))
variable (rightMask : (HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.MaskIndicator rightAtoms.characters))

local notation "R₀" => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)
local notation "left" => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftOriginal v) leftAtoms
local notation "right" => (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightOriginal v) rightAtoms

def literalLeftCommonAtoms : FrozenSourceAtoms A σ
    (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).rows
    (LC.branch v.2.2.1).slotCount :=
  ((left).commonAtomBounds (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftBranch v) leftMask).atoms (R₀).rows

def literalRightCommonAtoms : FrozenSourceAtoms A σ
    (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).rows
    (RC.branch v.2.2.2.1).slotCount :=
  ((right).commonAtomBounds (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v) rightMask).atoms (R₀).rows

theorem literalLeftCommonAtoms_ideal :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftCommonAtoms v) leftAtoms leftMask).ideal =
      (primePowerProduct (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity).val := by
  sorry

theorem literalRightCommonAtoms_ideal :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightCommonAtoms v) rightAtoms rightMask).ideal =
      (primePowerProduct (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity).val := by
  sorry

theorem literalLeftCommonAtoms_value
    (h : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftCommonAtoms v) leftAtoms leftMask).value h =
      (left).commonScalar (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftBranch v) := by
  sorry

theorem literalRightCommonAtoms_value
    (h : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightCommonAtoms v) rightAtoms rightMask).value h =
      (right).commonScalar (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightBranch v) := by
  sorry

theorem literalRows_eq_withCommonAtoms :
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRows v) leftAtoms rightAtoms =
      (R₀).withCommonAtoms ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftCommonAtoms v) leftAtoms leftMask)
        ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightCommonAtoms v) rightAtoms rightMask) := by
  sorry

variable (hclass : (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.NonunitLabelStable (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)))
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ h ∈ ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)).rows,
  ‖(HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v).weight h‖ ≤ bound)

/-- This record has exactly the actual literal row carrier. Rebuilding
its fields keeps the calculated numerical costs transparent rather than
hiding them behind a transport of the whole dependent record. -/
def literalSupportedRowMass :
    ActualSecondRowMass ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRows v) leftAtoms rightAtoms) C
      (LC.branch v.2.2.1).slotCount (RC.branch v.2.2.2.1).slotCount := by
  let W := (HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.actualRowsSupportedMass (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) hclass s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftCommonAtoms v) leftAtoms leftMask) ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightCommonAtoms v) rightAtoms rightMask)
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftCommonAtoms_ideal v) leftAtoms leftMask)
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightCommonAtoms_ideal v) rightAtoms rightMask) bound hbound hprofile
  refine {
    leftAtoms := W.leftAtoms
    rightAtoms := W.rightAtoms
    left_ideal := W.left_ideal
    right_ideal := W.right_ideal
    radius := W.radius
    mask := W.mask
    rowProfile := W.rowProfile
    profileBound := W.profileBound
    profileBound_nonneg := W.profileBound_nonneg
    profile_bound := W.profile_bound
    weight_eq := ?_
    unitIdeal := W.unitIdeal
    unit_ideal := W.unit_ideal
    nonunitIdeal := W.nonunitIdeal
    nonunit_ideal := W.nonunit_ideal
    left_positive := W.left_positive
    originalFiber := W.originalFiber
    original_fibers := W.original_fibers }
  intro h hh
  have hw := W.weight_eq h hh
  change (R₀).weight h * ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftCommonAtoms v) leftAtoms leftMask).value h *
    star (((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightCommonAtoms v) rightAtoms rightMask).value h) = _ at hw
  rw [(HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalLeftCommonAtoms_value v) leftAtoms leftMask h,
    (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalRightCommonAtoms_value v) rightAtoms rightMask h] at hw
  exact hw

@[simp] theorem literalSupportedRowMass_fiber :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRowMass v) leftAtoms rightAtoms leftMask rightMask
      hclass bound hbound hprofile).originalFiber = Γ.index := rfl

@[simp] theorem literalSupportedRowMass_unit :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRowMass v) leftAtoms rightAtoms leftMask rightMask
      hclass bound hbound hprofile).unitIdeal =
      secondPatternUnitIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).leftMultiplicity (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).rightMultiplicity
        ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)) := rfl

@[simp] theorem literalSupportedRowMass_nonunit :
    ((HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.literalSupportedRowMass v) leftAtoms rightAtoms leftMask rightMask
      hclass bound hbound hprofile).nonunitIdeal =
      secondPatternNonunitIdeal (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.block v).primes
        ((HeckeSkeleton.Moments.EngineStepV2.SecondBlockProfileChart.originalNonunitPattern (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.chart v)) s.mask s.cutoff s.cutoff_one (HeckeSkeleton.Moments.EngineStepV2.ActualGaussStage.CoveredClassKey.rowLabel v)) := rfl

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStepV2

end

