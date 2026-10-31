import HeckeSkeleton.LowEnergy.ActualCompleteIdealEnergy
import HeckeSkeleton.LowEnergy.TargetDictionary
import HeckeSkeleton.LowEnergy.TargetSieveDictionary

/-!
# The original completed marked energy

The complete-ideal cutoff is a genuine finite norm ball.  The original
sixth-unit quotient is finite, and all of its sectors are retained.  The
finite complete-ideal estimate is therefore an estimate for the literal
orbital `CompletedMarkedEnergy`, with the original selected-ideal norm in
the denominator.  The only supplied analytic estimates are the original
coefficient reflection and the original quadratic and cubic sieves.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.LowEnergy.ActualRows
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualCompleteIdealEnergy
open HeckeSkeleton.LowEnergy.TargetDictionary
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A finite-support identity, with no interchange of conditionally
convergent series and no omitted unit sectors. -/
theorem idealSector_tsum_eq_finite [Fintype (SixthUnitClasses K S)]
    (E : ExteriorIdeal K S × SixthUnitClasses K S → ℝ) (X : ℝ) :
    (∑' x : ExteriorIdeal K S × SixthUnitClasses K S,
      if exteriorNorm K S x.1 ≤ X then E x else 0) =
      ∑ ξ : SixthUnitClasses K S, ∑ I ∈ exteriorNormBall K S X, E (I, ξ) := by
  calc
    _ = ∑ x ∈ exteriorNormBall K S X ×ˢ (Finset.univ : Finset (SixthUnitClasses K S)),
        if exteriorNorm K S x.1 ≤ X then E x else 0 := by
      apply tsum_eq_sum
      intro x hx
      have hcut : ¬exteriorNorm K S x.1 ≤ X := by
        intro h
        exact hx (Finset.mem_product.mpr
          ⟨(mem_exteriorNormBall K S X x.1).mpr h, Finset.mem_univ _⟩)
      exact if_neg hcut
    _ = ∑ I ∈ exteriorNormBall K S X, ∑ ξ : SixthUnitClasses K S, E (I, ξ) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro ξ _
      exact if_pos ((mem_exteriorNormBall K S X I).mp hI)
    _ = _ := Finset.sum_comm

variable (c : HeckeSkeleton.TargetContext K)
local notation "Sc" => HeckeSkeleton.places K c
local notation "Pc" => HeckeSkeleton.probeData K c
local notation "ψc" => HeckeSkeleton.targetCharacter K c
local notation "θc" => thetaPeriod K Sc Pc ψc
local notation "gc" => c.geometry
local notation "Tc" => HeckeSkeleton.rayFilter K c

/-- LOW-REFLECTED-ENERGY for the repository's original completed marked
row, cutoff, selected ideal, and full sixth-unit quotient. -/
theorem completedMarkedEnergy
    (F : FiniteMellinData K Sc)
    (hreflection : MarkedCoefficientReflectionInput K Sc (Pc).arithmetic F θc)
    (hquadratic : HeckeSkeleton.QuadraticSieveBound K c)
    (hcubic : HeckeSkeleton.CubicSieveBound K c) :
    HeckeSkeleton.LowCauchy.CompletedMarkedEnergy K c := by
  letI : Finite (SixthLocalClasses K Sc) := HeckeSkeleton.sixthLocalClasses_finite K c
  intro B eps hB heps
  obtain ⟨C, Z0, hC, hZ0, hfinite⟩ := actual_finite_complete_ideal_energy K c F
    hreflection ((TargetSieveDictionary.quadratic_bound_iff K c).mp hquadratic)
    ((TargetSieveDictionary.cubic_bound_iff K c).mp hcubic) B eps hB heps
  letI : Fintype (SixthUnitClasses K Sc) := Fintype.ofFinite _
  let sectors : ℝ := Fintype.card (SixthUnitClasses K Sc)
  have hsectors : 0 < sectors := by
    dsimp only [sectors]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (SixthUnitClasses K Sc))
  refine ⟨sectors * C, Z0, mul_pos hsectors hC, hZ0, ?_⟩
  intro Z hZ p hp J
  dsimp only
  let q := exteriorNorm K Sc (subsetPrimeIdeal K Sc p J)
  rw [completedMarkedRow_energy_eq K c,
    idealSector_tsum_eq_finite K Sc]
  calc
    _ ≤ ∑ _ξ : SixthUnitClasses K Sc, C * Z ^ ((5 / 6 : ℝ) + eps) / q ^ 2 := by
      apply Finset.sum_le_sum
      intro ξ _
      change (∑ I ∈ exteriorNormBall K Sc (B * Z ^ (5 / 6 : ℝ) / q ^ 2),
        ‖HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J
          (idealSectorElement K Sc (Pc).arithmetic (I, ξ))‖ ^ 2) ≤ _
      exact hfinite Z hZ p hp J ξ
        (exteriorNormBall K Sc (B * Z ^ (5 / 6 : ℝ) / q ^ 2))
        (fun I hI => (mem_exteriorNormBall K Sc _ I).mp hI)
    _ = (sectors * C) * Z ^ ((5 / 6 : ℝ) + eps) / q ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [sectors]
      ring

#print axioms idealSector_tsum_eq_finite
#print axioms completedMarkedEnergy

end HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy
