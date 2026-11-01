import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledTerminalBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalTerminalPoolCharges

/-!
# The original geometry and norm charge of each actual pool tag

The first ideals and the selected physical divisor are unchanged across
the main and 1/6/7 sources. Only the original tag chooses its enlargement
and the main pool length. The matching norm charge is the charge already
used by the same one-pool summation.
-/

noncomputable section
open scoped Classical NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} [IsPrincipalIdealRing A.R]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z step eps : ℝ}

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (a : RealParameters) (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
variable (D : Finset (HeightOneSpectrum A.R)) (supportError : ℝ) (herr : 0 ≤ supportError)
variable (negative : Bool)

def pooledTerminalGeometry (tag : PoolSourceTag pool) :
    OriginalNominalGeometry (K := K) a Z step :=
  let coordinates := if negative then b.literalRightCoordinates D else b.literalLeftCoordinates D
  match tag with
  | .inl _ => OriginalNominalGeometry.canonicalMain coordinates supportError
      (zero_lt_one.trans pool.base_gt_one) herr
  | .inr (.inl p) => OriginalNominalGeometry.canonicalPoolError pool .one p coordinates supportError herr
  | .inr (.inr (.inl p)) => OriginalNominalGeometry.canonicalPoolError pool .six p coordinates supportError herr
  | .inr (.inr (.inr p)) => OriginalNominalGeometry.canonicalPoolError pool .seven p coordinates supportError herr

local notation "geometry" => b.pooledTerminalGeometry a pool D supportError herr negative

@[simp] theorem pooledTerminalGeometry_ideals (tag : PoolSourceTag pool) :
    (geometry tag).ideals =
      if negative then b.literalRightCoordinates D else b.literalLeftCoordinates D := by
  rcases tag with u | p | p | p <;> rfl

@[simp] theorem pooledTerminalGeometry_supportError (tag : PoolSourceTag pool) :
    (geometry tag).supportError = supportError := by
  rcases tag with u | p | p | p <;> rfl

@[simp] theorem pooledTerminalGeometry_valuation
    (valuation : AmplifierValuation) (prime : pool.primes) :
    geometry (valuation.sourceTag prime) =
      OriginalNominalGeometry.canonicalPoolError pool valuation prime
        (if negative then b.literalRightCoordinates D else b.literalLeftCoordinates D)
        supportError herr := by
  cases valuation <;> rfl

/-- The separated main length is exactly its actual pool charge;
the error tags require only their original charge at least one. -/
theorem pooledTerminalGeometry_charge (tag : PoolSourceTag pool) :
    Z ^ (geometry tag).tag.poolLength step ≤ poolTagNormCharge pool tag := by
  rcases tag with u | p | p | p
  · exact le_rfl
  all_goals
    change Z ^ (0 : ℝ) ≤ _
    rw [Real.rpow_zero]
    exact one_le_poolTagNormCharge pool _

end FirstCommonCharacterBlock
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.pooledTerminalGeometry_ideals
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.pooledTerminalGeometry_valuation
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.pooledTerminalGeometry_charge
