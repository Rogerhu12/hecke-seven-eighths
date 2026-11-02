import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSharpFirstFrequencies
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalGaussOrbitRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry

set_option linter.unusedSectionVars false

/-!
# Original first rows and their canonical retained scale

The actual positive and negative Gauss rows use the same fixed-divisor
physical cutoff. The retained scale is the proved upper endpoint of
that cutoff. No lower window on an individual frequency is required:
the second transform majorizes every original row at this endpoint.

Prime amplification multiplies the literal original frequency by the
sixth power of its selected prime. Its row bound uses the sharp original
window, independently of the coarse exponent used for pool density.
The error rows remain subsets of the original rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace FirstFiniteSource

variable {ι κ : Type*} (s : FirstFiniteSource K A.Sf Γ ι κ)

theorem divisor_originalFrequency_norm_le
    (D : Finset (HeightOneSpectrum A.R)) (q : Q) (hq : q ∈ s.divisorRows D) :
    A.exteriorNorm (originalFrequencyIdeal q.out.val) ≤ s.divisorPhysicalCutoff D := by
  sorry

theorem divisor_originalNegativeFrequency_norm_le
    (D : Finset (HeightOneSpectrum A.R)) (q : Q) (hq : q ∈ s.divisorRows D) :
    A.exteriorNorm (originalFrequencyIdeal (-q.out.val)) ≤ s.divisorPhysicalCutoff D := by
  sorry

end FirstFiniteSource

section OriginalRows

variable {ι κ : Type*}

/-- Both signs are the literal representatives of the same actual
divisor rows. No additional finite row family is introduced. -/
theorem canonicalFirstGaussData_divisor_row_windows
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (s : FirstFiniteSource K A.Sf Γ ι κ) (D : Finset (HeightOneSpectrum A.R))
    (R : ℝ) (hcutoff : s.divisorPhysicalCutoff D ≤ R) :
    (∀ h ∈ (canonicalFirstLeftGaussData C left right fullI fullJ DE hDE
        (s.divisorRows D)).rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ R) ∧
    (∀ h ∈ (canonicalFirstRightGaussData C left right fullI fullJ DE hDE
        (s.divisorRows D)).rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ R) := by
  sorry

end OriginalRows

namespace OriginalNominalIdeals

/-- The upper endpoint is chosen from original ideal lengths before
the second source, its rows, or either capacity deletion. -/
def canonicalRetainedScale (I : OriginalNominalIdeals K)
    (a : RealParameters) (Z supportError : ℝ) : ℝ :=
  Z ^ (I.firstFrequency a Z + supportError)

theorem canonicalRetainedScale_pos (I : OriginalNominalIdeals K)
    (a : RealParameters) (Z supportError : ℝ) (hZ : 0 < Z) :
    0 < I.canonicalRetainedScale a Z supportError := by
  sorry

theorem canonicalRetainedLength (I : OriginalNominalIdeals K)
    (a : RealParameters) (Z supportError : ℝ) (hZ : 1 < Z) :
    Real.log (I.canonicalRetainedScale a Z supportError) / Real.log Z =
      I.firstFrequency a Z + supportError := by
  sorry

end OriginalNominalIdeals

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}

def canonicalDirect (I : OriginalNominalIdeals K) (supportError : ℝ)
    (hZ : 0 < Z) (herr : 0 ≤ supportError) :
    OriginalNominalGeometry (K := K) a Z step :=
  forDirect I (I.canonicalRetainedScale a Z supportError) supportError
    (I.canonicalRetainedScale_pos a Z supportError hZ) herr le_rfl

def canonicalMain (I : OriginalNominalIdeals K) (supportError : ℝ)
    (hZ : 0 < Z) (herr : 0 ≤ supportError) :
    OriginalNominalGeometry (K := K) a Z step :=
  forMain I (I.canonicalRetainedScale a Z supportError) supportError
    (I.canonicalRetainedScale_pos a Z supportError hZ) herr le_rfl

def canonicalPoolError
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z (step / 3) eps)
    (e : AmplifierValuation) (p : P.primes)
    (I : OriginalNominalIdeals K) (supportError : ℝ) (herr : 0 ≤ supportError) :
    OriginalNominalGeometry (K := K) a Z step :=
  forPoolError P e p I (I.canonicalRetainedScale a Z supportError) supportError
    (I.canonicalRetainedScale_pos a Z supportError (zero_lt_one.trans P.base_gt_one))
    herr le_rfl

/-- This pays exactly the sixth-power insertion on the main branch;
the direct and valuation-error branches have no such insertion. -/
theorem enlargement_ge_pool (G : OriginalNominalGeometry (K := K) a Z step)
    (hstep : 0 ≤ step) : 6 * G.tag.poolLength step ≤ G.enlargement := by
  sorry

theorem enlargement_nonneg (G : OriginalNominalGeometry (K := K) a Z step)
    (hstep : 0 ≤ step) : 0 ≤ G.enlargement := by
  sorry

/-- The actual second common factors do not enter the first row
enlargement. This expression can be fixed before the second transform
and then reused with its subsequently computed frequency pattern. -/
theorem enlargement_eq_endpoint (G : OriginalNominalGeometry (K := K) a Z step)
    (hZ : 1 < Z)
    (hscale : G.retainedScale = G.ideals.canonicalRetainedScale a Z G.supportError) :
    G.enlargement =
      max (idealLogLength Z G.ideals.opposite.val - idealLogLength Z G.ideals.first.val -
        G.supportError - 2 * G.tag.removedLength Z + G.tag.movingLength Z) 0 +
        G.tag.padding step := by
  sorry

theorem retainedScale_le_enlarged (G : OriginalNominalGeometry (K := K) a Z step)
    (hZ : 1 ≤ Z) (hstep : 0 ≤ step) :
    G.retainedScale ≤ G.retainedScale * Z ^ G.enlargement := by
  sorry

end OriginalNominalGeometry

namespace FirstGaussPoolData

variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- The sharp original row exponent is independent of the coarse
norm exponent chosen once for prime-pool density and multiplicity. -/
theorem main_originalFrequencyIdeal_norm_le_sharp
    (d : FirstGaussPoolData C P ι) (r : ℝ)
    (hrows : ∀ h ∈ d.rows, A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ r)
    (h : A.R) (hh : h ∈ d.mainRows) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ (r + 6 * ell) := by
  sorry

theorem error_originalFrequencyIdeal_norm_le_sharp
    (d : FirstGaussPoolData C P ι) (R : ℝ)
    (hrows : ∀ h ∈ d.rows, A.exteriorNorm (originalFrequencyIdeal h) ≤ R)
    (p : ExteriorPrime A) (h : A.R) (hh : h ∈ d.errorRows p) :
    A.exteriorNorm (originalFrequencyIdeal h) ≤ R := by
  sorry

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstGaussData_divisor_row_windows
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.canonicalDirect
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.canonicalPoolError
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.enlargement_ge_pool
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.main_originalFrequencyIdeal_norm_le_sharp
