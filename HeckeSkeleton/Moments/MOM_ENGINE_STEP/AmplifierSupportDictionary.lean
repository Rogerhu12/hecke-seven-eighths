import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierResidualSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportCartesianReindex

/-! Actual singleton-support extraction and residual quotient identities. -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid DedekindZetaZeroFree LocalFiniteSums
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

theorem supportExtract_singleton_power
    (I Q : Ideal (𝓞 K)) :
    supportExtract I {Q} = Q ^ (normalizedFactors I).count Q := by
  have hf : (normalizedFactors I).filter (fun P => P ∈ ({Q} : Finset (Ideal (𝓞 K)))) =
      Multiset.replicate ((normalizedFactors I).count Q) Q := by
    apply Multiset.ext.mpr
    intro P
    rw [Multiset.count_filter, Multiset.count_replicate]
    by_cases h : P = Q <;> simp [h, eq_comm]
  change ((normalizedFactors I).filter (fun P => P ∈ ({Q} : Finset (Ideal (𝓞 K))))).prod = _
  rw [hf, Multiset.prod_replicate]

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS} {p : ExteriorPrime A} {n : ℕ}
variable {I : A.Exterior}

namespace AmplifierResidualPresentation

theorem extracted_eq_power (R : AmplifierResidualPresentation C p n I) :
    supportExtract I.val {p.val.asIdeal} = p.val.asIdeal ^ n := by
  have hv : (normalizedFactors I.val).count p.val.asIdeal = n := by
    rw [R.reconstructed,
      PrimePowerQuotientSupport.count_prime_power_mul p.val n R.residual.val R.residual.property.1]
    have hp := R.primitive
    change (normalizedFactors R.residual.val).count p.val.asIdeal = 0 at hp
    rw [hp, add_zero]
  rw [supportExtract_singleton_power, hv]

theorem residual_eq_supportResidual (R : AmplifierResidualPresentation C p n I) :
    R.residual.val = supportResidual I.val {p.val.asIdeal} := by
  apply mul_left_cancel₀ (pow_ne_zero n p.val.ne_bot)
  calc
    p.val.asIdeal ^ n * R.residual.val = I.val := R.reconstructed.symm
    _ = supportExtract I.val {p.val.asIdeal} * supportResidual I.val {p.val.asIdeal} :=
      (support_reconstruct I.val I.property.1 {p.val.asIdeal}).symm
    _ = _ := by rw [R.extracted_eq_power]

theorem residual_eq_actualExterior (R : AmplifierResidualPresentation C p n I) :
    R.residual = residualExterior I {p.val.asIdeal} :=
  Subtype.ext R.residual_eq_supportResidual

end AmplifierResidualPresentation

namespace CartesianSourceReindex

variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior} {k : ℕ}
variable (R : CartesianSourceReindex columns ideal k)

/-- Only the retained source indices require the residual recipe.
This allows an actual amplifier presentation defined on its valuation
subtype to be used without a fabricated recipe on other valuations. -/
def supportResidualBranchOn
    (P : Finset (Ideal (𝓞 K)))
    (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P)
    (J : ι → A.Exterior)
    (hJ : ∀ i ∈ b.originalColumns.image R.index,
      (J i).val = supportResidual (ideal i).val P) :
    CartesianSourceReindex (b.originalColumns.image R.index) J b.keep.card :=
  (R.supportResidualBranch P b).congrIdeal J hJ

/-- The primitive inputs are the actual quotient presentations on the
retained occurrence branch, not a residual-column identity. -/
def amplifierResidualBranch
    (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots {p.val.asIdeal})
    (J : ι → A.Exterior)
    (Q : ∀ i ∈ b.originalColumns.image R.index,
      AmplifierResidualPresentation C p n (ideal i))
    (hJ : ∀ i (hi : i ∈ b.originalColumns.image R.index), J i = (Q i hi).residual) :
    CartesianSourceReindex (b.originalColumns.image R.index) J b.keep.card :=
  R.supportResidualBranchOn {p.val.asIdeal} b J (by
    intro i hi
    rw [hJ i hi]
    exact (Q i hi).residual_eq_supportResidual)

end CartesianSourceReindex

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.supportExtract_singleton_power
#print axioms HeckeSkeleton.Moments.EngineStep.AmplifierResidualPresentation.residual_eq_supportResidual
#print axioms HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.amplifierResidualBranch

