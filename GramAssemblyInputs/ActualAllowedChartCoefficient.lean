import ActualAllowedGeneratorDivisionCore
import ActualThetaChartGcdMobius
import ActualOriginalChartProductReduction
import ActualOriginalChartSixthUnit

/-!
UNCOMPILED / native 0. The actual chart extension in the finite Mobius
sum equals the coefficient evaluated on the SAME witness's allowed
generators. The two independently constructed sixth-unit sectors are
removed by fixed-frequency invariance. No coprimality is imposed on the
residual ideal pair, and the original frequency quotient is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedChartCoefficientDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open ActualDivisibleChoiceDraft ActualProbeGaussFourierDraft
open ActualGramJointChartCoverDraft ActualOriginalChartProductDraft
open ActualOriginalChartSixthUnitDraft

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "gen" => probeGenerator K S w.D

/-- The exact arithmetic factor of each actual finite residual-ideal term.
The only divisibility premise selects the original nonzero branch; no
generator is silently replaced by an associated representative. -/
theorem thetaChartCorrelationExtension_eq_allowedColumns
    (C D M₁ M₂ : E) (j : NZ) (hj : w.D.generator C ∣ j.val) :
    thetaChartCorrelationExtension K S w.D C
        (exteriorMul K S D M₁, exteriorMul K S D M₂) j =
      originalChartCoefficient K S w.D.root6 w.D.primitive6 w.D.embedding
        (probeArithmetic_six_support K S w.D) (gen C)
        (thetaChartFrequencyQuotient K S w.D C j hj) (gen D) (gen M₁) (gen M₂) := by
  rw [thetaChartCorrelationExtension_eq_of_dvd K S w.D C _ j hj]
  rw [← nestedGeneratorDivision_factor K w C D M₁,
    ← nestedGeneratorDivision_factor K w C D M₂]
  rw [← originalChartCoefficient_eq_one_products K S w.D.root6 w.D.primitive6
    w.D.embedding (probeArithmetic_six_support K S w.D) (gen C)
    (thetaChartFrequencyQuotient K S w.D C j hj) (gen D)
    (nestedGeneratorResidualQuotient K w C D M₁)
    (nestedGeneratorResidualQuotient K w C D M₂)]
  exact originalChartCoefficient_sixthPower_columns K S w.D.root6 w.D.primitive6
    w.D.embedding (probeArithmetic_six_support K S w.D) (gen C)
    (thetaChartFrequencyQuotient K S w.D C j hj) (gen D) (gen M₁) (gen M₂)
    (nestedGeneratorDivisionSector K w C D M₁) (nestedGeneratorDivisionSector K w C D M₂)

end HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedChartCoefficientDraft
