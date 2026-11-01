import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedPoissonZero
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalRowBallChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GeneratedZeroGauss

/-!
# The original additive origin of the complete Gram source

The same original coefficients give a square at the additive origin.
Its actual tensor and Haar covolume remain present.  In particular the
fixed canonical row-ball tensor has the positive value `mass⁻¹`, so the
whole original-origin subtraction may be discarded on real parts.
The identity is proved before estimating individual common blocks.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}

theorem originalTensor_smul
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (c : ℂ) (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (a : K) :
    sIntegerTensorTerm K S (traceSchwartzToMixed K (c • φ)) h a =
      c * sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h a := by
  simp only [sIntegerTensorTerm, traceSchwartzToMixed_apply, SchwartzMap.smul_apply,
    smul_eq_mul, mul_assoc]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- The original zero tensor is positive, not zero. -/
theorem CanonicalRowBall.originalTensor_zero (B : ℝ) :
    sIntegerTensorTerm K S (traceSchwartzToMixed K (CanonicalRowBall.archTest K S B))
      (rowBallFiniteFamily K S B) 0 = ((CanonicalRowBall.mass K S)⁻¹ : ℝ) := by
  rw [CanonicalRowBall.archTest, originalTensor_smul]
  have hzero := compactShapeMajorant_tensor_zero K S (rowBallCompactShape K S B)
    (isCompact_rowBallCompactShape K S B)
  change sIntegerTensorTerm K S (traceSchwartzToMixed K (rowBallArchTest K S B))
    (rowBallFiniteFamily K S B) 0 = 1 at hzero
  rw [hzero, mul_one]

variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

theorem OrbitalGaussColumn.pair_residue_zero
    (c d : OrbitalGaussColumn K S Γ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) :
    (c.pair hDiff d φ).residue 0 = c.residue hDiff 0 * star (d.residue hDiff 0) := by
  simp only [OrbitalGaussColumn.pair]
  exact congrArg₂ (fun x y => c.residue hDiff x * star (d.residue hDiff y))
    (map_zero (completeFrequencyReduction c.modulus (c.modulus * d.modulus)
      (dvd_mul_right _ _)))
    (map_zero (completeFrequencyReduction d.modulus (c.modulus * d.modulus)
      (dvd_mul_left _ _)))

theorem OrbitalGaussColumn.pair_originZero_empty
    (c d : OrbitalGaussColumn K S Γ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (a b : ℂ) (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    (c.pair hDiff d ((a * star b) • φ)).originZero h ∅ =
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0 *
          ((a * c.residue hDiff 0) * star (b * d.residue hDiff 0)) := by
  rw [ParentPeriodicPair.originZero_empty, pair_residue_zero]
  change _ * (_ * sIntegerTensorTerm K S (traceSchwartzToMixed K ((a * star b) • φ)) h 0) = _
  rw [originalTensor_smul, star_mul]
  ring

/-- The original zero is a whole polynomial square with its genuine
tensor and covolume.  No individual block positivity is claimed. -/
theorem gauss_originZero_sum_eq_square
    {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
    (col : ι → OrbitalGaussColumn K S Γ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    (∑ i ∈ columns, ∑ j ∈ columns,
      ((col i).pair hDiff (col j) ((coefficient i * star (coefficient j)) • φ)).originZero h ∅) =
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0 *
          ((‖∑ i ∈ columns, coefficient i * (col i).residue hDiff 0‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
  simp only [OrbitalGaussColumn.pair_originZero_empty, star_sum]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]

theorem gauss_originZero_sum_nonneg
    {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
    (col : ι → OrbitalGaussColumn K S Γ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hpositive : 0 ≤ (sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0).re) :
    0 ≤ (∑ i ∈ columns, ∑ j ∈ columns,
      ((col i).pair hDiff (col j) ((coefficient i * star (coefficient j)) • φ)).originZero h ∅).re := by
  rw [gauss_originZero_sum_eq_square]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hpositive) (sq_nonneg _)

theorem canonical_rowBall_originZero_sum_nonneg
    {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
    (col : ι → OrbitalGaussColumn K S Γ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (B : ℝ) :
    0 ≤ (∑ i ∈ columns, ∑ j ∈ columns,
      ((col i).pair hDiff (col j)
        ((coefficient i * star (coefficient j)) • CanonicalRowBall.archTest K S B)).originZero
          (rowBallFiniteFamily K S B) ∅).re := by
  apply gauss_originZero_sum_nonneg
  rw [CanonicalRowBall.originalTensor_zero, Complex.ofReal_re]
  exact inv_nonneg.mpr (CanonicalRowBall.mass_pos K S).le

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalRowBall.originalTensor_zero
#print axioms HeckeSkeleton.Moments.EngineStep.gauss_originZero_sum_eq_square
#print axioms HeckeSkeleton.Moments.EngineStep.canonical_rowBall_originZero_sum_nonneg
