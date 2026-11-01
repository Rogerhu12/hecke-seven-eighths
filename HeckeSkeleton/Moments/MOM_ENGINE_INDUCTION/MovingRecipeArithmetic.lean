import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteMovingRowRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualAtomPhases

/-!
# Literal atoms of the canonical moving-row recipe

This consumes MOM_ENGINE_STEP's actual recipe at immutable revision
b73c02d482ea09c6c51eb8197414d9ee07775fc0. The fixed correction, original
S-integer factors and integer exponents remain in that recipe. Their
fixed character product belongs in the arithmetic atom, while the
variable row still uses its original complete-ideal orbit.

The extra coprimality support used below is exactly the radical of the
displayed moving support times the original remaining ideal. Coprimality
with this radical is proved equivalent to the two original masks. No
norm claim is inferred just from equality of masks; the canonical full
joint budget concerns this same radical explicitly.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- Replacing the two fixed coprimality tests by their literal full
radical changes no coefficient, including when the remaining ideal has
nontrivial prime multiplicities. -/
theorem movingFactors_fullMaskSupport_coprime
    {A : SArithmeticData K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    (moving : EngineStep.OriginalMovingFactors A P R)
    (remaining : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    IsCoprime I (moving.fullMaskSupport remaining).val ↔
      IsCoprime I moving.support.val ∧ IsCoprime I remaining.val := by
  have hfull : (moving.fullMaskSupport remaining).val ≠ ⊥ :=
    nonZeroDivisors.coe_ne_zero (moving.fullMaskSupport remaining)
  have hproduct : moving.support.val * remaining.val ≠ ⊥ :=
    mul_ne_zero moving.support.property.1 (nonZeroDivisors.coe_ne_zero remaining)
  have hs : primeSupport (moving.fullMaskSupport remaining).val =
      primeSupport (moving.support.val * remaining.val) := by
    simp only [EngineStep.OriginalMovingFactors.fullMaskSupport,
      EngineStep.CommonSupportMass.commonRadical_support, Finset.inter_self]
  calc
    _ ↔ ∀ p ∈ primeSupport (moving.fullMaskSupport remaining).val, IsCoprime I p :=
      coprime_support_iff I _ hfull
    _ ↔ ∀ p ∈ primeSupport (moving.support.val * remaining.val), IsCoprime I p := by rw [hs]
    _ ↔ IsCoprime I (moving.support.val * remaining.val) :=
      (coprime_support_iff I _ hproduct).symm
    _ ↔ _ := IsCoprime.mul_right_iff

/-- The canonical mask has the precise complete-row form used by the
ordinary reflection identities, with the very support named in its
full joint budget. -/
theorem completeMovingRowRecipe_mask
    {A : SArithmeticData K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    {X : Type*} {data : X → MomentData K omegaCharacter psiCharacter}
    (recipe : EngineStep.CompleteMovingRowRecipe A P R data)
    (ξ : X) (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    (data ξ).commonMask u I =
      (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
        decide (IsCoprime I (recipe.moving.fullMaskSupport recipe.remaining).val)) := by
  rw [recipe.mask ξ u I]
  simp only [movingFactors_fullMaskSupport_coprime, Bool.decide_and, Bool.and_assoc]

/-- The owner recipe itself constructs the exact arithmetic atoms. No
arbitrary phase, periodic dictionary, or final energy is supplied. -/
def completeMovingRowRecipe_arithmeticAtoms
    {A : SArithmeticData K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    {X : Type*} {data : X → MomentData K omegaCharacter psiCharacter}
    (recipe : EngineStep.CompleteMovingRowRecipe A P R data) (ξ : X) :
    EngineStep.ParentArithmeticAtoms
      (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ) :=
  completeIdealFixedTwistArithmeticAtoms (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R
    recipe.sector (data ξ) (recipe.moving.fullMaskSupport recipe.remaining)
    (recipe.correction * recipe.moving.character) (recipe.exterior ξ)
    (recipe.character ξ) (completeMovingRowRecipe_mask recipe ξ)

/-- Every original quotient point has its actual phase even after all
fixed moving factors have been retained in the arithmetic coefficient. -/
theorem completeMovingRowRecipe_actual_phase_dictionary
    (c : TargetContext K)
    {R : RowCharacterInput K (places K c) (probeData K c)}
    {X : Type*} {data : X → MomentData K omegaCharacter psiCharacter}
    (recipe : EngineStep.CompleteMovingRowRecipe (axiomChoice K c).A (probeData K c) R data)
    (ξ : X) (W : EngineStep.NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (U t Y₁ Y₂ : ℝ) :
    let raw := ((completeMovingRowRecipe_arithmeticAtoms recipe ξ).constantAtoms W a U t).raw Y₁ Y₂
    (∀ I ∈ raw.leftColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.leftPhase q I = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ I ∈ raw.rightColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.rightPhase q I = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.primePhase q i p = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) p.asIdeal q.out.val) :=
  completeIdealFixedTwistRawAtoms_actual_phase_dictionary c R recipe.sector (data ξ)
    (recipe.moving.fullMaskSupport recipe.remaining)
    (recipe.correction * recipe.moving.character) (recipe.exterior ξ)
    (recipe.character ξ) (completeMovingRowRecipe_mask recipe ξ) W a U t Y₁ Y₂

end HeckeSkeleton.Moments.EngineInduction
