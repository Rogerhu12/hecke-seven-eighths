import GeneratorMaskWitness
import ActualThetaGeneratorDivision
import ActualProbeGaussOriginalFourier
import ActualSexticJointChartCRT
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration

/-!
UNCOMPILED / native 0. Pure arithmetic core extracted verbatim from
ActualAllowedGeneratorDivisionSector. The same witness supplies actual
sixth-unit corrections for literal generator division and nested products.
No generator-choice mask, divisible-column reindexing or analytic bound
is imported. All original namespaces, declarations and proofs are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualDivisibleChoiceDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open ActualProbeGaussFourierDraft ActualGramJointChartDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer S K
local notation "NZ" => NonzeroRingElements OS
local notation "E" => ExteriorIdeal K S
local notation "Γ" => sixthPowerUnits K S

/-- The actual sixth power supplied by THIS witness's multiplicativity. -/
def allowedGeneratorProductSector (C N : E) : Γ :=
  let u := Classical.choose (w.allowed.multiplicative C N)
  ⟨u ^ 6, ⟨u, rfl⟩⟩

theorem allowedGeneratorProductSector_spec (C N : E) :
    w.D.generator (exteriorMul K S C N) =
      ((S).unitEquivUnitsInteger K (allowedGeneratorProductSector K w C N).val).val *
        w.D.generator C * w.D.generator N := by
  let u := Classical.choose (w.allowed.multiplicative C N)
  change w.D.generator (exteriorMul K S C N) =
    ((S).unitEquivUnitsInteger K (u ^ 6)).val * w.D.generator C * w.D.generator N
  rw [map_pow, Units.val_pow_eq_pow_val]
  exact Classical.choose_spec (w.allowed.multiplicative C N)

/-- Uniqueness of the literal quotient identifies the original general-
unit construction with this particular original-Gamma translate. -/
theorem thetaGeneratorDivision_eq_allowedSector (C N I : E)
    (hI : I = exteriorMul K S C N) :
    thetaGeneratorDivision K S w.D C N I hI =
      sIntegerOrbitTranslate K S Γ (allowedGeneratorProductSector K w C N)
        (probeGenerator K S w.D N) := by
  apply Subtype.ext
  symm
  apply thetaGeneratorDivision_unique K S w.D C N I hI
  calc
    w.D.generator I =
        ((S).unitEquivUnitsInteger K (allowedGeneratorProductSector K w C N).val).val *
          w.D.generator C * w.D.generator N := by
      rw [hI]
      exact allowedGeneratorProductSector_spec K w C N
    _ = w.D.generator C *
        (sIntegerOrbitTranslate K S Γ (allowedGeneratorProductSector K w C N)
          (probeGenerator K S w.D N)).val := by
      change _ = w.D.generator C *
        (((S).unitEquivUnitsInteger K (allowedGeneratorProductSector K w C N).val).val *
          w.D.generator N)
      ring

theorem exists_thetaGeneratorDivision_eq_sixthTranslate (C N I : E)
    (hI : I = exteriorMul K S C N) :
    ∃ γ : Γ, thetaGeneratorDivision K S w.D C N I hI =
      sIntegerOrbitTranslate K S Γ γ (probeGenerator K S w.D N) :=
  ⟨allowedGeneratorProductSector K w C N,
    thetaGeneratorDivision_eq_allowedSector K w C N I hI⟩

/-- The SAME two concrete sixth-power unit corrections, in their actual
order, for gen(C*(D*M))/(gen(C)*gen(D)). -/
def nestedGeneratorDivisionSector (C D M : E) : Γ :=
  allowedGeneratorProductSector K w C (exteriorMul K S D M) *
    allowedGeneratorProductSector K w D M

def nestedGeneratorResidualQuotient (C D M : E) : NZ :=
  sIntegerOrbitTranslate K S Γ (nestedGeneratorDivisionSector K w C D M)
    (probeGenerator K S w.D M)

/-- The actual divisor product, with no replacement of either quotient
by an independently chosen generator. -/
theorem nestedGeneratorDivision_factor (C D M : E) :
    divisorColumn K S (probeGenerator K S w.D D)
      (nestedGeneratorResidualQuotient K w C D M) =
      thetaGeneratorDivision K S w.D C (exteriorMul K S D M)
        (exteriorMul K S C (exteriorMul K S D M)) rfl := by
  rw [thetaGeneratorDivision_eq_allowedSector]
  apply Subtype.ext
  change w.D.generator D *
    (((S).unitEquivUnitsInteger K (nestedGeneratorDivisionSector K w C D M).val).val *
      w.D.generator M) =
    ((S).unitEquivUnitsInteger K
      (allowedGeneratorProductSector K w C (exteriorMul K S D M)).val).val *
      w.D.generator (exteriorMul K S D M)
  rw [allowedGeneratorProductSector_spec K w D M]
  simp only [nestedGeneratorDivisionSector, Subgroup.coe_mul, map_mul, Units.val_mul]
  ring

theorem generator_dvd_nestedGeneratorDivision (C D M : E) :
    w.D.generator D ∣
      (thetaGeneratorDivision K S w.D C (exteriorMul K S D M)
        (exteriorMul K S C (exteriorMul K S D M)) rfl).val := by
  refine ⟨(nestedGeneratorResidualQuotient K w C D M).val, ?_⟩
  exact (congrArg Subtype.val (nestedGeneratorDivision_factor K w C D M)).symm

end HeckeGeneral.ThetaSkeleton.Physical.ActualDivisibleChoiceDraft
