import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSupport
import HeckePort.Moments.Descent.Quotients

set_option linter.unusedSectionVars false

/-!
# Residual occurrence carriers as filtered quotient carriers

The residual support of an actual extraction is the original quotient
support with its finite prime-avoidance condition. Both directions are
proved from multiplication by the same extracted divisor. The branch
versions obtain the divisor's nonzero and support properties from the
original witness; no carrier equality is an input.

This is a finite support identity. It neither discards the deletion
condition nor supplies a bound for its support norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralSupport

theorem prime_avoids_iff_not_mem (p : HeightOneSpectrum (𝓞 K))
    (P : Finset (Ideal (𝓞 K))) (hP : ∀ q ∈ P, Prime q) :
    Avoids p.asIdeal P ↔ p.asIdeal ∉ P := by
  sorry

end CanonicalLiteralSupport

namespace SupportCartesian

open CanonicalLiteralSupport

/-- The complete residual carrier is the actual quotient carrier,
filtered by avoidance of the original extraction primes. -/
theorem plainResidual_eq_quotientSupport_filter
    (S P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hS : ∀ I ∈ S, I ≠ 0) (hP : ∀ p ∈ P, Prime p)
    (hD : D ≠ 0) (hsmooth : primeSupport D ⊆ P) :
    plainResidual S P D =
      (quotientSupport D S).filter (fun I => Avoids I P) := by
  sorry

/-- A retained prime occurrence is its unchanged original finite
carrier with the same prime-avoidance filter. -/
theorem primeLive_eq_filter_avoids
    (S : Finset (HeightOneSpectrum (𝓞 K))) (P : Finset (Ideal (𝓞 K)))
    (hP : ∀ p ∈ P, Prime p) :
    primeLive S P = S.filter (fun p => Avoids p.asIdeal P) := by
  sorry

end SupportCartesian

namespace SupportCartesianBranch

variable {k : ℕ}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S P)

/-- The first actual occurrence witness supplies every divisor
condition needed by the generic quotient identity. -/
theorem plainResidual₁_eq_quotientSupport_filter (hP : ∀ p ∈ P, Prime p) :
    SupportCartesian.plainResidual S₁ P b.plainExtract₁ =
      (quotientSupport b.plainExtract₁ S₁).filter
        (fun I => CanonicalLiteralSupport.Avoids I P) := by
  sorry

/-- The second quotient uses its own original extracted occurrence,
without replacing it by an equal-norm divisor. -/
theorem plainResidual₂_eq_quotientSupport_filter (hP : ∀ p ∈ P, Prime p) :
    SupportCartesian.plainResidual S₂ P b.plainExtract₂ =
      (quotientSupport b.plainExtract₂ S₂).filter
        (fun I => CanonicalLiteralSupport.Avoids I P) := by
  sorry

end SupportCartesianBranch
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralSupport.prime_avoids_iff_not_mem
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesian.plainResidual_eq_quotientSupport_filter
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesian.primeLive_eq_filter_avoids
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.plainResidual₁_eq_quotientSupport_filter
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.plainResidual₂_eq_quotientSupport_filter
