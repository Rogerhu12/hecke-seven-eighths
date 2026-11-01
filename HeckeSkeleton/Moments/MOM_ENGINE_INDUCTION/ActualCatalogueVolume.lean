import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualAnnularVolume
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalVolume
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalCharacters
import HeckeGeneral.Characters.RadialNormalization

/-!
# The original finite catalogue has actual annular volume control

The same fixed characters used by the exceptional producer inherit the
original radial normalization. The actual contour theorem supplies
continuous remainder seminorms before every profile and scale.
The positive support condition is retained in the raw volume statement.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMoment
open MOM_PRIME EngineStep
open scoped Classical BigOperators SchwartzMap NNReal

variable {K : Type} [Field K] [NumberField K]

/-- The coefficient is exactly the one used by both task owners. -/
theorem actualExceptionalCoefficient_eq (chi : HeckeCharacter K) :
    CanonicalExceptionalVolume.coefficient chi = heckeExceptionalCharacter K chi := rfl

/-- Radial normalization of the original fixed background and the
finite theta twists give the principal-or-nonnorm alternative for the
literal finite character catalogue used in exceptional production. -/
theorem originalCatalogue_normReduced
    (w : InfinitePlace K) (psi : HeckeCharacter K)
    (hpsi : heckeRadialParameter K w psi = 0)
    (theta : Finset (HeckeCharacter K))
    (htheta : ∀ chi ∈ theta, FiniteOrder chi)
    (i : CanonicalLiteralExceptionalCharacters.CatalogueIndex theta) :
    ExceptionalNormReduced K
      (CanonicalLiteralExceptionalCharacters.background psi i.1 * i.2.val) := by
  have hbackground : heckeRadialParameter K w
      (CanonicalLiteralExceptionalCharacters.background psi i.1) = 0 := by
    rcases i with ⟨tag, chi⟩
    cases tag with
    | none => simp only [CanonicalLiteralExceptionalCharacters.background,
        heckeRadialParameter_one]
    | some b =>
      cases b with
      | false => exact hpsi
      | true =>
        simpa only [CanonicalLiteralExceptionalCharacters.background,
          heckeRadialParameter_inv, hpsi, neg_zero]
  have hz := radial_zero_mul_finiteOrder K w
    (CanonicalLiteralExceptionalCharacters.background psi i.1) i.2.val
    hbackground (htheta _ i.2.property)
  by_cases hone : CanonicalLiteralExceptionalCharacters.background psi i.1 * i.2.val = 1
  · exact Or.inl hone
  · exact Or.inr (ne_normTwist_of_radial_zero K w _ hz hone)

/-- The raw analytic input for the entire original finite catalogue is
constructed before any profile, source, Fourier variable or scale. -/
theorem exists_originalCatalogue_supported_volume
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (w : InfinitePlace K) (psi : HeckeCharacter K)
    (hpsi : heckeRadialParameter K w psi = 0)
    (theta : Finset (HeckeCharacter K))
    (htheta : ∀ chi ∈ theta, FiniteOrder chi)
    (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ remainder : CanonicalLiteralExceptionalCharacters.CatalogueIndex theta →
        Seminorm ℂ (𝓢(ℝ, ℂ)),
      (∀ i, Continuous (remainder i)) ∧
      ∀ (i : CanonicalLiteralExceptionalCharacters.CatalogueIndex theta)
        (phi : 𝓢(ℝ, ℂ)), tsupport phi ⊆ Icc lower upper →
      ∀ X : ℝ, 0 < X →
        ‖(∑' I : Ideal (𝓞 K), CanonicalExceptionalVolume.coefficient
            (CanonicalLiteralExceptionalCharacters.background psi i.1 * i.2.val) I *
              phi ((Ideal.absNorm I : ℝ) / X)) -
          (X : ℂ) * actualAnnularDensity
            (CanonicalLiteralExceptionalCharacters.background psi i.1 * i.2.val) phi‖ ≤
          remainder i phi := by
  have hexists (i : CanonicalLiteralExceptionalCharacters.CatalogueIndex theta) :=
    exists_actualAnnularVolumeSeminorm hcomplex
      (CanonicalLiteralExceptionalCharacters.background psi i.1 * i.2.val)
      (originalCatalogue_normReduced w psi hpsi theta htheta i)
      lower upper hlower hinterval
  choose remainder hcontinuous hvolume using hexists
  exact ⟨remainder, hcontinuous, hvolume⟩


end HeckeSkeleton.Moments.EngineInduction
