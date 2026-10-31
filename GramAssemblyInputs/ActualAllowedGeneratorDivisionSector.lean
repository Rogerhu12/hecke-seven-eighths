import ActualDivisibleChoiceProductReindex
import ActualAllowedGeneratorDivisionCore

/-!
UNCOMPILED / native 0. The SAME witness's proved allowed-generator
multiplicativity places its literal generator quotient in the original
sixth-power-unit orbit of the residual generator. The subgroup multiplier
is constructed from the sixth power in that multiplicativity theorem;
the independently defined general generator-division unit is not declared
to lie in the subgroup.

For N = D*M the literal quotient by gen(C) is divisible by gen(D).
It therefore supplies an actual element of the divisible chosen-column
index, whose actual quotient is identified, not replaced by a generator.
No coprimality, profile identity, summability or Gram estimate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualDivisibleChoiceDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open ActualGeneratorChoiceDraft ActualProbeGaussFourierDraft
open ActualGramJointChartDraft ActualGramFamilyDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer S K
local notation "NZ" => NonzeroRingElements OS
local notation "E" => ExteriorIdeal K S
local notation "Γ" => sixthPowerUnits K S

@[simp] theorem choiceFiniteMask_thetaGeneratorDivision (C N I : E)
    (hI : I = exteriorMul K S C N) :
    choiceFiniteMask K w
      (sLocalNonzeroIntegerDiagonal K S
        (thetaGeneratorDivision K S w.D C N I hI)).2 = 1 := by
  rw [thetaGeneratorDivision_eq_allowedSector]
  exact choiceFiniteMask_generator_translate K w N (allowedGeneratorProductSector K w C N)

/-- An actual residual product column in the previous reindexing's
divisible chosen-column type. The ideal coordinate is D*M, not M. -/
def actualResidualDivisibleChosenColumn (C D M : E) :
    DivisibleChosenColumns K w (probeGenerator K S w.D D) :=
  ⟨(exteriorMul K S D M,
      allowedGeneratorProductSector K w C (exteriorMul K S D M)), by
    refine ⟨(nestedGeneratorResidualQuotient K w C D M).val, ?_⟩
    have h := (nestedGeneratorDivision_factor K w C D M).symm
    rw [thetaGeneratorDivision_eq_allowedSector] at h
    exact congrArg Subtype.val h⟩

/-- The quotient chosen by the actual divisibility reindexing is the
literal two-stage quotient, including its actual original-Gamma unit. -/
@[simp] theorem divisibleChosenQuotient_actualResidual (C D M : E) :
    divisibleChosenQuotient K w (probeGenerator K S w.D D)
      (actualResidualDivisibleChosenColumn K w C D M) =
      nestedGeneratorResidualQuotient K w C D M := by
  apply divisorColumn_injective K S (probeGenerator K S w.D D)
  rw [divisorColumn_divisibleChosenQuotient]
  change sIntegerOrbitTranslate K S Γ
    (allowedGeneratorProductSector K w C (exteriorMul K S D M))
    (probeGenerator K S w.D (exteriorMul K S D M)) = _
  exact (thetaGeneratorDivision_eq_allowedSector K w C (exteriorMul K S D M)
    (exteriorMul K S C (exteriorMul K S D M)) rfl).symm.trans
      (nestedGeneratorDivision_factor K w C D M).symm

/-- The representative product is EXACTLY the original quotient used by
the residual correlation extension, not merely an associated element. -/
theorem divisorColumn_actualResidual (C D M : E) :
    divisorColumn K S (probeGenerator K S w.D D)
      (divisibleChosenQuotient K w (probeGenerator K S w.D D)
        (actualResidualDivisibleChosenColumn K w C D M)) =
      thetaGeneratorDivision K S w.D C (exteriorMul K S D M)
        (exteriorMul K S C (exteriorMul K S D M)) rfl := by
  rw [divisibleChosenQuotient_actualResidual]
  exact nestedGeneratorDivision_factor K w C D M

@[simp] theorem choiceColumnIdeal_nestedGeneratorResidualQuotient (C D M : E) :
    choiceColumnIdeal K w (nestedGeneratorResidualQuotient K w C D M) = M := by
  unfold nestedGeneratorResidualQuotient
  rw [choiceColumnIdeal_translate, choiceColumnIdeal_probeGenerator]

end HeckeGeneral.ThetaSkeleton.Physical.ActualDivisibleChoiceDraft
