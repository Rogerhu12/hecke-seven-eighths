import HeckeSkeleton.GramDefinitions
import HeckeGeneral.Arithmetic.SIntegerOrbitCounting

/-!
GR-06 candidate using the already proved count of actual S-integer orbits.
The mainline bound retains every sector of the original finite-index subgroup
and counts actual orbit norms, via bounded ordinary generator sectors and the
number-field ideal count. No probe data or principalization assumption is used.
The harmless 1 + X is absorbed for X >= 1; below 1 the cutoff is empty.
The bound uses the original sixth-power unit quotient at every scale.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Gram

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem gramOrdinaryFrequencyCount :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X →
      Finite (ordinaryCutoff K S X) ∧
      (Nat.card (ordinaryCutoff K S X) : ℝ) ≤ C * X := by
  letI : (sixthPowerUnits K S).FiniteIndex :=
    sUnit_power_range_finiteIndex K S 6 (by decide)
  obtain ⟨D, hD, hbound⟩ :=
    exists_card_boundedSIntegerOrbits_le K S (sixthPowerUnits K S)
  refine ⟨2 * D, by positivity, ?_⟩
  intro X hX
  refine ⟨inferInstanceAs (Finite
    (BoundedSIntegerOrbits K S (sixthPowerUnits K S) X)), ?_⟩
  by_cases h1 : 1 ≤ X
  · have hb : (Nat.card (ordinaryCutoff K S X) : ℝ) ≤ D * (1 + X) :=
      hbound X hX.le
    exact hb.trans (by nlinarith)
  · letI : IsEmpty (ordinaryCutoff K S X) := ⟨fun q => by
      have hone : 1 ≤ (sIntegerOrbitNorm K S (sixthPowerUnits K S) q.val).val :=
        one_le_actualSIntegerOrbitNorm K S q.val
      exact h1 (hone.trans q.property)⟩
    rw [Nat.card_of_isEmpty]
    simp only [Nat.cast_zero]
    positivity

end HeckeSkeleton.Gram

#print axioms HeckeSkeleton.Gram.gramOrdinaryFrequencyCount
