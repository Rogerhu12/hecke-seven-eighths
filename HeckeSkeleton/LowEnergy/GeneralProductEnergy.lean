import HeckeSkeleton.LowEnergy.GeneralTupleBlocks
import HeckeSkeleton.LowEnergy.GeneralUniformEnergy

/-!
# Energy of the original product-mark projection

The finite row is defined by the original tuple and prime-choice sum.
Its concrete block family is constructed in `GeneralTupleBlocks`; source
support and the reconstruction equality are proved there.  The consumer
supplies only scalar bounds and arithmetic support of that concrete data.
No source identity, coefficient independence or energy is an assumption.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralProductEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.GeneralCanonicalBlock
open HeckeSkeleton.LowEnergy.GeneralTupleBlocks
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Exact product-mark block energy, uniformly before the finite-order
background and its real norm twist.  `Admissible` concerns only the
actual windows, norm intervals, coefficient bounds and explicit exponent.
The active ideal fibres and saturated patterns are part of the formula. -/
def UniformProductBlockEnergy (F : FiniteMellinData K S) (θ : HeckeCharacter K) : Prop :=
  ∀ (W Fmax Omax Lmax : ℝ) (rmax : ℕ) (eps : ℝ),
    0 ≤ W → 0 ≤ Fmax → 0 ≤ Omax → 0 ≤ Lmax → 0 < eps →
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ), MarkedCoefficientReflectionInput K S D F (ν * θ * heckeNormTwist K t) →
      ∀ (Z O A B E : ℝ),
      1 < Z → 0 ≤ O → O ≤ Omax → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (label puncture : ExteriorIdeal K S)
        (R : Finset (IdealRankin.PowerfulIdeal K))
        (data : IdealRankin.PowerfulIdeal K → Finset (ExteriorPrime K S) →
          SixthUnitClasses K S → ProductData K S rmax),
      ((label.val * puncture.val).val.absNorm : ℝ) ≤ Z ^ Lmax →
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (∀ I ∈ R, ∀ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∀ u, (data I T u).family.Admissible Z W A B E Fmax) →
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S,
          (data I T u).projectedSourceEnergy D F (ν * θ * heckeNormTwist K t) V) ≤
        C * GeneralUniformEnergy.heightFactor K t * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          Z ^ (O / 2 + E + eps)

theorem uniformProductBlockEnergy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D) :
    UniformProductBlockEnergy K S D F θ := by
  intro W Fmax Omax Lmax rmax eps hW hFmax hOmax hLmax heps
  obtain ⟨C, hC, hb⟩ := GeneralUniformEnergy.canonical_complete_family_energy_height
    K S D F hreflection.kernel.finite_admissible θ hreflection.allowed_generators
    hquadratic hcubic W Fmax Omax Lmax rmax eps hW hFmax hOmax hLmax heps
  refine ⟨C, hC, ?_⟩
  intro ν hν t hchild Z O A B E hZ hO hOmax' hA hB V label puncture R data hnorm hR hadm
  have he :
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S,
          (data I T u).projectedSourceEnergy D F (ν * θ * heckeNormTwist K t) V) =
      ∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, sourceMarkedEnergy K S D (data I T u).family F
          (ν * θ * heckeNormTwist K t) V := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro T hT
    apply tsum_congr
    intro u
    exact ProductData.projectedSourceEnergy_eq_sourceMarkedEnergy (D := D) (data I T u)
      F (ν * θ * heckeNormTwist K t) V
  rw [he]
  exact hb ν hν t hchild.kernel hchild.exterior_unramified Z O A B E hZ hO hOmax' hA hB
    V label puncture R (fun I T u => (data I T u).family) hnorm hR hadm
      (fun I _ T _ u => ProductData.family_sourceSupported (data I T u))

#print axioms uniformProductBlockEnergy

end HeckeSkeleton.LowEnergy.GeneralProductEnergy
