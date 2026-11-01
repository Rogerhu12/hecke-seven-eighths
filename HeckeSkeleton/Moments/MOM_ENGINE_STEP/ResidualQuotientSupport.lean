import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSupport
import HeckePort.Moments.Descent.Quotients

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
  constructor
  · intro ha hp
    exact p.prime.not_unit (isCoprime_self.mp (ha p.asIdeal hp))
  · intro hp
    have ha := residual_avoids p.asIdeal P hP
    rwa [supportResidual_prime p.asIdeal p.prime P, if_neg hp] at ha

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
  ext I
  constructor
  · intro hI
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply (mem_quotientSupport D I hD S).mpr
      exact (Finset.mem_filter.mp (plain_reconstruct_mem S P D I hS hI)).1
    · obtain ⟨J, _, hJI⟩ := Finset.mem_image.mp hI
      rw [← hJI]
      exact residual_avoids J P hP
  · intro hI
    obtain ⟨hq, ha⟩ := Finset.mem_filter.mp hI
    exact plain_residual_mem S P hP D I hD
      (quotientSupport_nonzero D hD S hS I hq) hsmooth ha
      ((mem_quotientSupport D I hD S).mp hq)

/-- A retained prime occurrence is its unchanged original finite
carrier with the same prime-avoidance filter. -/
theorem primeLive_eq_filter_avoids
    (S : Finset (HeightOneSpectrum (𝓞 K))) (P : Finset (Ideal (𝓞 K)))
    (hP : ∀ p ∈ P, Prime p) :
    primeLive S P = S.filter (fun p => Avoids p.asIdeal P) := by
  ext p
  simp only [primeLive, Finset.mem_filter, prime_avoids_iff_not_mem p P hP]

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
  apply SupportCartesian.plainResidual_eq_quotientSupport_filter
    S₁ P b.plainExtract₁ b.plain₁_nonzero hP b.plainExtract₁_ne_zero
  have he := (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).1).2
  rw [← he, supportExtract_support]
  exact Finset.inter_subset_right

/-- The second quotient uses its own original extracted occurrence,
without replacing it by an equal-norm divisor. -/
theorem plainResidual₂_eq_quotientSupport_filter (hP : ∀ p ∈ P, Prime p) :
    SupportCartesian.plainResidual S₂ P b.plainExtract₂ =
      (quotientSupport b.plainExtract₂ S₂).filter
        (fun I => CanonicalLiteralSupport.Avoids I P) := by
  apply SupportCartesian.plainResidual_eq_quotientSupport_filter
    S₂ P b.plainExtract₂ b.plain₂_nonzero hP b.plainExtract₂_ne_zero
  have he := (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).2).2
  rw [← he, supportExtract_support]
  exact Finset.inter_subset_right

end SupportCartesianBranch
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralSupport.prime_avoids_iff_not_mem
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesian.plainResidual_eq_quotientSupport_filter
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesian.primeLive_eq_filter_avoids
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.plainResidual₁_eq_quotientSupport_filter
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.plainResidual₂_eq_quotientSupport_filter
