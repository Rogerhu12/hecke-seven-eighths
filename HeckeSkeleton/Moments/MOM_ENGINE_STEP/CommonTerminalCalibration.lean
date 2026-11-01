import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonTupleFibers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

/-!
# Raw terminal windows after actual common-support extraction

The source keeps its original whole column indices.  Its occurrence
ideals are genuinely support-extracted, and in an error branch they are
also divided by the actual amplifier prime powers.  These constructors
supply the resulting product identity and finite fibre count to the
existing zero/tail interface.  Injectivity is imposed only on the
original full occurrence tuple.  All remaining inputs are individual
profile, ideal-norm, radius and mask windows.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {ι : Type*} {k n : ℕ}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

namespace SecondTailWindows

/-- Main common-block source: the actual support quotient loses only
its tuple of divisors of the original common ideal. -/
def ofSupportResidual
    (C : A.GeneralArithmeticContext σ η hS)
    (columns : Finset ι) (originalIdeal : ι → A.Exterior)
    (common : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hcommon : ∀ i ∈ columns, supportExtract (originalIdeal i).val common = D)
    (originalFactors : ι × ι → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun ij t => (originalFactors ij t).val)
      (columns ×ˢ columns : Set (ι × ι)))
    (hproduct : ∀ ij ∈ columns ×ˢ columns,
      PowerfulDiagonal.tupleIdeal (fun t => (originalFactors ij t).val) =
        (originalIdeal ij.1).val * (originalIdeal ij.2).val)
    (blocks : ∀ DE : FirstZeroLabel columns columns
      (fun i => residualExterior (originalIdeal i) common)
      (fun i => residualExterior (originalIdeal i) common),
      FirstCommonCharacterBlock (fun i => residualExterior (originalIdeal i) common)
        (fun i => residualExterior (originalIdeal i) common) DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → ι → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (Z productExponent profileExponent maskExponent inverseRadiusExponent Amp : ℝ)
    (hZ : 1 ≤ Z) (hB : 0 ≤ productExponent) (hAmp : 0 ≤ Amp)
    (hnorm : ∀ ij ∈ columns ×ˢ columns,
      (Ideal.absNorm ((residualExterior (originalIdeal ij.1) common).val *
        (residualExterior (originalIdeal ij.2) common).val) : ℝ) ≤ Z ^ productExponent)
    (hprofile : ∀ v ∈ firstZeroPairs columns columns
      (fun i => residualExterior (originalIdeal i) common)
      (fun i => residualExterior (originalIdeal i) common),
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) ≤
        Amp * Z ^ profileExponent)
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) mask)).val ≤
        Z ^ maskExponent)
    (hradius : radius.val⁻¹ ≤ Z ^ inverseRadiusExponent) :
    SecondTailWindows C columns columns
      (fun i => residualExterior (originalIdeal i) common)
      (fun i => residualExterior (originalIdeal i) common)
      blocks seminorms profiles radius mask k Z productExponent profileExponent maskExponent
      inverseRadiusExponent Amp where
  base_ge_one := hZ
  productExponent_nonneg := hB
  amplitude_nonneg := hAmp
  factors ij t := (actualSupportResidualFactors common (originalFactors ij) t).val
  multiplicity := idealDivisorCount (D ^ 2) ^ k
  factors_fiber_card := (actual_support_residual_pair_data columns originalIdeal originalFactors
    hinj hproduct common D hD hcommon).2
  factor_product := (actual_support_residual_pair_data columns originalIdeal originalFactors
    hinj hproduct common D hD hcommon).1
  product_norm := hnorm
  profile_seminorm := hprofile
  mask_norm := hmask
  inverse_radius := hradius

/-- Actual error source: the finite loss is the original common-divisor
fingerprint together with the exact amplifier-valuation allocation.
The quotient ideals are the residual ideals of the actual arithmetic
presentations, with no residual-injectivity or generator-equality input. -/
def ofSupportAmplifier
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (columns : Finset ι) (originalIdeal : ι → A.Exterior)
    (common : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hcommon : ∀ i ∈ columns, supportExtract (originalIdeal i).val common = D)
    (Q : ∀ i, AmplifierResidualPresentation C p n (residualExterior (originalIdeal i) common))
    (originalFactors : ι × ι → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun ij t => (originalFactors ij t).val)
      (columns ×ˢ columns : Set (ι × ι)))
    (hproduct : ∀ ij ∈ columns ×ˢ columns,
      PowerfulDiagonal.tupleIdeal (fun t => (originalFactors ij t).val) =
        (originalIdeal ij.1).val * (originalIdeal ij.2).val)
    (blocks : ∀ DE : FirstZeroLabel columns columns
      (fun i => (Q i).residual) (fun i => (Q i).residual),
      FirstCommonCharacterBlock (fun i => (Q i).residual) (fun i => (Q i).residual) DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → ι → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (Z productExponent profileExponent maskExponent inverseRadiusExponent Amp : ℝ)
    (hZ : 1 ≤ Z) (hB : 0 ≤ productExponent) (hAmp : 0 ≤ Amp)
    (hnorm : ∀ ij ∈ columns ×ˢ columns,
      (Ideal.absNorm ((Q ij.1).residual.val * (Q ij.2).residual.val) : ℝ) ≤ Z ^ productExponent)
    (hprofile : ∀ v ∈ firstZeroPairs columns columns
      (fun i => (Q i).residual) (fun i => (Q i).residual),
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) ≤
        Amp * Z ^ profileExponent)
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) mask)).val ≤
        Z ^ maskExponent)
    (hradius : radius.val⁻¹ ≤ Z ^ inverseRadiusExponent) :
    SecondTailWindows C columns columns (fun i => (Q i).residual) (fun i => (Q i).residual)
      blocks seminorms profiles radius mask k Z productExponent profileExponent maskExponent
      inverseRadiusExponent Amp where
  base_ge_one := hZ
  productExponent_nonneg := hB
  amplitude_nonneg := hAmp
  factors ij := actualResidualFactorTuple C p
    (actualSupportResidualFactors common (originalFactors ij))
  multiplicity := idealDivisorCount (D ^ 2) ^ k * (n + n + 1) ^ k
  factors_fiber_card := (actual_support_amplifier_pair_data C p columns originalIdeal originalFactors
    hinj hproduct common D hD hcommon Q).2
  factor_product := (actual_support_amplifier_pair_data C p columns originalIdeal originalFactors
    hinj hproduct common D hD hcommon Q).1
  product_norm := hnorm
  profile_seminorm := hprofile
  mask_norm := hmask
  inverse_radius := hradius

end SecondTailWindows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondTailWindows.ofSupportResidual
#print axioms HeckeSkeleton.Moments.EngineStep.SecondTailWindows.ofSupportAmplifier

