import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFirstPhase
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyGaussMask
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierGaussExtraction

/-!
# The remaining literal fixed phases in the actual source

The amplifier residual column has a genuine reciprocity factor. It is
the residual ideal's sextic character at the original prime generator
to power `2 * n`. The empty second row mask likewise leaves the actual
chosen unit divisor phase. Its inverse unit is retained, rather than
identified with one. Both factors are fixed before the physical row
and the two Fourier variables and can enter the original moving list.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

namespace AmplifierResidualPresentation

variable {C : A.GeneralArithmeticContext σ η hS} {p : ExteriorPrime A} {n : ℕ}
variable {I : A.Exterior} (D : AmplifierResidualPresentation C p n I)

/-- The exact actual amplifier phase is an original single-element
residue. Its two factors agree by allowed-generator reciprocity. -/
theorem columnPhase_eq_residue :
    D.columnPhase = actualIdealResidue (A := A) (σ := σ) D.residual.val
      (generator C p ^ (2 * n)) := by
  sorry

end AmplifierResidualPresentation

namespace CanonicalLiteralFixedPhases

variable [IsPrincipalIdealRing A.R]

/-- This is the chosen empty-mask generator, as its actual unit. -/
def emptyDivisorUnit : A.Rˣ := (sIntegerMaskGenerator_empty_isUnit K A.Sf).unit

theorem emptyDivisorUnit_val :
    (emptyDivisorUnit (A := A) : A.R) =
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅).val :=
  (sIntegerMaskGenerator_empty_isUnit K A.Sf).unit_spec

def emptyDivisorInverse : A.R := ((emptyDivisorUnit (A := A))⁻¹ : A.Rˣ)

theorem emptyDivisorInverse_generates :
    A.Generates (unitExterior A) (emptyDivisorInverse (A := A)) := by
  sorry

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- The empty divisor's inverse character is the original character
at the inverse chosen unit. No equality of that unit with one is used. -/
theorem generated_empty_divisorPhase
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).divisorPhase
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅).val =
      actualIdealResidue (A := A) (σ := σ) I.val (emptyDivisorInverse (A := A)) := by
  rw [OrbitalGaussColumn.divisorPhase, MulChar.inv_apply_eq_inv',
    ← emptyDivisorUnit_val, actualIdealResidue_exterior,
    ← generatedOriginalColumn_character_mk hΓ I a ha]
  let f : A.R →* ℂ :=
    (generatedOriginalColumn (σ := σ) hΓ I a ha).character.toMonoidHom.comp
      (Ideal.Quotient.mk _).toMonoidHom
  exact (map_units_inv f (emptyDivisorUnit (A := A))).symm

theorem generated_empty_subset_divisorPhase
    (D : (∅ : Finset (HeightOneSpectrum A.R)).powerset)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).divisorPhase
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val =
      actualIdealResidue (A := A) (σ := σ) I.val (emptyDivisorInverse (A := A)) := by
  rw [emptyMask_divisor_eq D]
  exact generated_empty_divisorPhase hΓ I a ha

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

def emptyDivisorMoving : OriginalMovingFactors A P R :=
  OriginalMovingFactors.singleton
    ⟨emptyDivisorInverse (A := A), (emptyDivisorInverse_generates (A := A)).1⟩ 1

/-- Even when its character is nontrivial on the selected unit sector,
the empty-divisor factor has no finite prime support. -/
theorem emptyDivisorMoving_support : (emptyDivisorMoving P R).support.val = 1 := by
  rw [emptyDivisorMoving, OriginalMovingFactors.singleton_support _ _
    (emptyDivisorInverse_generates (A := A)) 1]
  simp [unitExterior, CommonSupportMass.commonRadical, primeSupport, ← Ideal.one_eq_top]

end CanonicalLiteralFixedPhases
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.AmplifierResidualPresentation.columnPhase_eq_residue
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFixedPhases.generated_empty_divisorPhase
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFixedPhases.emptyDivisorMoving_support
