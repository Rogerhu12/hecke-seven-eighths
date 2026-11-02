import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.GaussOrbitRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorPhysicalSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FullSupportParameters

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Sharp first frequencies on the actual divisor branch

The first modulus is the product of the two residual columns and the
active common radical. Its norm therefore divides out both complete
common ideals exactly. Only nonzero original profiles enter the maximum
which defines the physical cutoff. Each complementary mask divisor
uses its own common physical cutoff, keeping its actual norm in the
first frequency length. All original columns and coefficients remain.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- The actual original ideal of the selected complementary divisor.
Its generator is the literal generator already used by Poisson. -/
def firstPhysicalDivisorIdeal (D : Finset (HeightOneSpectrum A.R)) : A.Exterior :=
  originalFrequencyIdeal
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val

theorem firstPhysicalDivisorIdeal_norm (D : Finset (HeightOneSpectrum A.R)) :
    A.exteriorNorm (firstPhysicalDivisorIdeal D) =
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val :=
  originalFrequencyIdeal_norm _
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property

namespace OriginalNominalIdeals

/-- The upper endpoint is chosen from original ideal lengths before
the second source, its rows, or either capacity deletion. -/
def canonicalRetainedScale (I : OriginalNominalIdeals K)
    (a : RealParameters) (Z supportError : ℝ) : ℝ :=
  Z ^ (I.firstFrequency a Z + supportError)

theorem canonicalRetainedScale_pos (I : OriginalNominalIdeals K)
    (a : RealParameters) (Z supportError : ℝ) (hZ : 0 < Z) :
    0 < (OriginalNominalIdeals.canonicalRetainedScale (I := I)) a Z supportError := Real.rpow_pos_of_pos hZ _

theorem canonicalRetainedLength (I : OriginalNominalIdeals K)
    (a : RealParameters) (Z supportError : ℝ) (hZ : 1 < Z) :
    Real.log ((OriginalNominalIdeals.canonicalRetainedScale (I := I)) a Z supportError) / Real.log Z =
      I.firstFrequency a Z + supportError := by
  rw [canonicalRetainedScale, Real.log_rpow (zero_lt_one.trans hZ)]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos hZ))

end OriginalNominalIdeals

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}

def canonicalDirect (I : OriginalNominalIdeals K) (supportError : ℝ)
    (hZ : 0 < Z) (herr : 0 ≤ supportError) :
    OriginalNominalGeometry (K := K) a Z step :=
  forDirect I ((OriginalNominalIdeals.canonicalRetainedScale (I := I)) a Z supportError) supportError
    ((OriginalNominalIdeals.canonicalRetainedScale_pos (I := I)) a Z supportError hZ) herr le_rfl

def canonicalMain (I : OriginalNominalIdeals K) (supportError : ℝ)
    (hZ : 0 < Z) (herr : 0 ≤ supportError) :
    OriginalNominalGeometry (K := K) a Z step :=
  forMain I ((OriginalNominalIdeals.canonicalRetainedScale (I := I)) a Z supportError) supportError
    ((OriginalNominalIdeals.canonicalRetainedScale_pos (I := I)) a Z supportError hZ) herr le_rfl

def canonicalPoolError
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z (step / 3) eps)
    (e : AmplifierValuation) (p : P.primes)
    (I : OriginalNominalIdeals K) (supportError : ℝ) (herr : 0 ≤ supportError) :
    OriginalNominalGeometry (K := K) a Z step :=
  forPoolError P e p I ((OriginalNominalIdeals.canonicalRetainedScale (I := I)) a Z supportError) supportError
    ((OriginalNominalIdeals.canonicalRetainedScale_pos (I := I)) a Z supportError (zero_lt_one.trans P.base_gt_one))
    herr le_rfl

/-- This pays exactly the sixth-power insertion on the main branch;
the direct and valuation-error branches have no such insertion. -/
theorem enlargement_ge_pool (G : OriginalNominalGeometry (K := K) a Z step)
    (hstep : 0 ≤ step) : 6 * G.tag.poolLength step ≤ G.enlargement := by
  have hm : 0 ≤ max (G.shiftedCommon - idealLogLength Z G.ideals.first.val -
      2 * G.tag.removedLength Z + G.tag.movingLength Z) 0 := le_max_right _ _
  have hp : 6 * G.tag.poolLength step ≤ G.tag.padding step := by
    cases G.tag <;> simp only [OriginalNominalTag.poolLength,
      OriginalNominalTag.padding] <;> linarith
  exact hp.trans (le_add_of_nonneg_left hm)

theorem enlargement_nonneg (G : OriginalNominalGeometry (K := K) a Z step)
    (hstep : 0 ≤ step) : 0 ≤ G.enlargement :=
  (mul_nonneg (by norm_num) (G.tag.poolLength_nonneg step hstep)).trans
    ((OriginalNominalGeometry.enlargement_ge_pool (G := G)) hstep)

/-- The actual second common factors do not enter the first row
enlargement. This expression can be fixed before the second transform
and then reused with its subsequently computed frequency pattern. -/
theorem enlargement_eq_endpoint (G : OriginalNominalGeometry (K := K) a Z step)
    (hZ : 1 < Z)
    (hscale : G.retainedScale = (OriginalNominalIdeals.canonicalRetainedScale (I := G.ideals)) a Z G.supportError) :
    G.enlargement =
      max (idealLogLength Z G.ideals.opposite.val - idealLogLength Z G.ideals.first.val -
        G.supportError - 2 * G.tag.removedLength Z + G.tag.movingLength Z) 0 +
        G.tag.padding step := by
  unfold enlargement shiftedCommon retainedLength
  rw [hscale, (OriginalNominalIdeals.canonicalRetainedLength (I := G.ideals)) a Z G.supportError hZ]
  congr 2
  ring

theorem retainedScale_le_enlarged (G : OriginalNominalGeometry (K := K) a Z step)
    (hZ : 1 ≤ Z) (hstep : 0 ≤ step) :
    G.retainedScale ≤ G.retainedScale * Z ^ G.enlargement := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.one_le_rpow hZ ((OriginalNominalGeometry.enlargement_nonneg (G := G)) hstep)) G.retainedScale_pos.le

end OriginalNominalGeometry

end HeckeSkeleton.Moments.EngineStepV2

