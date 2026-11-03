import HeckeSkeleton.ExpansionModels.NormalizedRecipePolynomials

/-!
# Exact normalized detector sums for arbitrary shared recipe data

The inverse and plain polynomials and two-scale inverse family are
defined from the same actual recipe data.  These identities additionally identify its values
with the deleted-prime finite sums used by the analytic detector.  The
deletion set is the original S/6/complete-row mask; no conductor-only mask
or independently chosen polynomial replaces it.

This module has no dependency on the named admitted expansion data. It
provides the literal data-level identities used by an explicit recipe
constructor. The named source projections remain in SourceRecipeNormalization.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ExpansionRecipe

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ExpansionBufferedPolynomials ExpansionDetector.Fourier
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {P : ProbeData K S} {R : RowCharacterInput K S P}
variable {ω ψ : HeckeCharacter K} {g : PrimeWindowGeometry}
variable {F : RecipeFamily K ψ g}

def RecipeWitnessData.inverseDetectorPolynomial
    (w : RecipeWitnessData K ψ g F) (t U : ℝ) (u : FrequencyRow K S) : ℂ :=
  let D := U ^ w.inverseLength
  let a := F.presentation w.presentation
  normalizedPolynomial (F.inverseAnnular.support u.ideal.val 0 D)
    (deletedAnnularCoefficient K true (a.inverseBackground * R.character u ^ a.direction)
      (originalDeletedPrimes K S u.ideal.val))
    (idealNorm K)
    (fun y => F.inverseAnnular.profile u.ideal.val 0 y * F.cutoff ((D / U ^ t) * y))
    D (w.realShifts u.ideal.val 0) (F.frequencyScale * w.imagShifts u.ideal.val 0)

def RecipeWitnessData.plainDetectorPolynomial
    (w : RecipeWitnessData K ψ g F) (U : ℝ) (u : FrequencyRow K S) : ℂ :=
  let N := U ^ w.plainLength
  let a := F.presentation w.presentation
  normalizedPolynomial (F.plainAnnular.support u.ideal.val 0 N)
    (deletedAnnularCoefficient K false (a.plainBackground * R.character u)
      (originalDeletedPrimes K S u.ideal.val))
    (idealNorm K) (F.plainAnnular.profile u.ideal.val 0)
    N (w.realShifts u.ideal.val 0) (F.frequencyScale * w.imagShifts u.ideal.val 0)

theorem RecipeWitnessData.inversePolynomial_eq_normalized
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T U : ℝ)
    (u : FrequencyRow K S) (hU : 0 < U) :
    inversePolynomial (w.model (P := P) (R := R) (ω := ω) p t T U u.sector)
      u.ideal.val (U ^ w.inverseLength) 0 =
        w.inverseDetectorPolynomial (R := R) t U u := by
  rw [RecipeWitnessData.model_eq_shared]
  exact shared_inverse_cutoff_eq_normalized K S P R ω ψ
    (F.presentation w.presentation) (F.physicalGeometry p) F.slotCoefficient
    F.inverseAnnular (F.plainTest K ψ g w.realShifts w.imagShifts)
    F.cutoff (U ^ w.inverseLength / U ^ t)
    (fun I => w.realShifts I 0) (fun I => F.frequencyScale * w.imagShifts I 0)
    u (U ^ w.inverseLength) (Real.rpow_pos_of_pos hU _)

theorem RecipeWitnessData.plainPolynomial_eq_normalized
    (w : RecipeWitnessData K ψ g F) (p : Fin 3 → ℝ) (t T U : ℝ)
    (u : FrequencyRow K S) (hU : 0 < U) :
    plainPolynomial (w.model (P := P) (R := R) (ω := ω) p t T U u.sector)
      (F.plainTest K ψ g w.realShifts w.imagShifts)
      u.ideal.val (U ^ w.plainLength) 0 =
        w.plainDetectorPolynomial (R := R) U u := by
  rw [RecipeWitnessData.model_eq_shared]
  exact shared_plain_twist_eq_normalized K S P R ω ψ
    (F.presentation w.presentation) (F.physicalGeometry p) F.slotCoefficient
    (recipeCutoffTwist K F.inverseAnnular F.cutoff (U ^ w.inverseLength / U ^ t)
      (fun I => w.realShifts I 0) (fun I => F.frequencyScale * w.imagShifts I 0))
    F.plainAnnular (fun I => w.realShifts I 0)
    (fun I => F.frequencyScale * w.imagShifts I 0)
    u (U ^ w.plainLength) (Real.rpow_pos_of_pos hU _)

end HeckeGeneral.Analysis.ExpansionRecipe

