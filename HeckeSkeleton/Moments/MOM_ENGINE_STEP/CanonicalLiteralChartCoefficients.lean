import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTwoStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondLogChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondChartAllocation

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

namespace HeckeSkeleton.Moments.EngineStep

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
  rw [canonicalLogWithCoefficients_leftCoefficient_eq,
    CanonicalLiteralFirstPhase.leftDivisorFactor hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity (b.leftResidual i) (b.leftGenerator i)
      (b.left_generates i) hi]
  ring

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
  rw [canonicalLogWithCoefficients_rightCoefficient_eq,
    CanonicalLiteralFirstPhase.rightDivisorFactor hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity (b.rightResidual j) (b.rightGenerator j)
      (b.right_generates j) hj]
  ring

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
  change (c i * ((A.exteriorNorm (b.secondLeftIdeal i) ^ δ : ℝ) : ℂ)) * _ = _
  rw [CanonicalLiteralFixedPhases.generated_empty_divisorPhase]

theorem canonicalLog_empty_rightSourceCoefficient (j : κ) :
    (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e finiteTest hlc hcs
        radius ∅ rowLabelCount rowLabel hleft hright δ hδ hδhalf).sourceRightCoefficient j =
      e j * ((A.exteriorNorm (b.secondRightIdeal j) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (b.secondRightIdeal j).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  change (e j * ((A.exteriorNorm (b.secondRightIdeal j) ^ δ : ℝ) : ℂ)) * _ = _
  rw [CanonicalLiteralFixedPhases.generated_empty_divisorPhase]

theorem canonicalLog_empty_leftSourceCoefficient_on_columns
    (i : ι) (hi : i ∈ b.leftColumns left) :
    (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e finiteTest hlc hcs
        radius ∅ rowLabelCount rowLabel hleft hright δ hδ hδhalf).sourceLeftCoefficient i =
      c i * ((A.exteriorNorm (fullI i) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (fullI i).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  rw [canonicalLog_empty_leftSourceCoefficient, b.secondLeftIdeal_eq left i hi]

theorem canonicalLog_empty_rightSourceCoefficient_on_columns
    (j : κ) (hj : j ∈ b.rightColumns right) :
    (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e finiteTest hlc hcs
        radius ∅ rowLabelCount rowLabel hleft hright δ hδ hδhalf).sourceRightCoefficient j =
      e j * ((A.exteriorNorm (fullJ j) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (fullJ j).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  rw [canonicalLog_empty_rightSourceCoefficient, b.secondRightIdeal_eq right j hj]

end SecondBlockProfileChart

namespace FirstCommonCharacterBlock

/-- On an active common block the earlier squarefree divisor is
already a factor of every actual complete left column. -/
theorem left_divisor_of_common (S : Ideal (𝓞 K)) (hS : S ∣ DE.1)
    (i : ι) (hi : i ∈ b.leftColumns left) : S ∣ (fullI i).val := by
  rw [b.left_reconstruct left i hi, b.common_left]
  exact dvd_mul_of_dvd_left hS _

theorem right_divisor_of_common (S : Ideal (𝓞 K)) (hS : S ∣ DE.2)
    (j : κ) (hj : j ∈ b.rightColumns right) : S ∣ (fullJ j).val := by
  rw [b.right_reconstruct right j hj, b.common_right]
  exact dvd_mul_of_dvd_left hS _

theorem left_divisor_filter_eq (S : Ideal (𝓞 K)) (hS : S ∣ DE.1)
    (f : ι → ℂ) (i : ι) (hi : i ∈ b.leftColumns left) :
    (if S ∣ (fullI i).val then f i else 0) = f i :=
  if_pos (b.left_divisor_of_common left S hS i hi)

theorem right_divisor_filter_eq (S : Ideal (𝓞 K)) (hS : S ∣ DE.2)
    (f : κ → ℂ) (j : κ) (hj : j ∈ b.rightColumns right) :
    (if S ∣ (fullJ j).val then f j else 0) = f j :=
  if_pos (b.right_divisor_of_common right S hS j hj)

end FirstCommonCharacterBlock
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.canonicalLog_leftSourceCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalLog_empty_leftSourceCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.left_divisor_filter_eq
