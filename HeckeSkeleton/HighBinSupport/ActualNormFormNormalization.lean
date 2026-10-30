import HeckeSkeleton.PrimeNormalizer

/-!
The exact existing normalizer dependency of the sharp norm-form route.

Unlike the coarse horizontal-boundary estimate, the cancellation bound
for the character prime sum has no positive window mass as a common
factor. Its normalization therefore uses the existing
`PrimeNormalizer.normalizer_smallPower`. That theorem depends on the
upstream admitted `window_prime_lower` (PR-WINDOW-PIT). The dependency is
deliberately isolated here and appears in the printed axiom audit below.
No new admission or normalizer-bound premise is introduced.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinVerified.NormFormNormalization

open NumberField IsDedekindDomain Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A concrete uniform cutoff for the original prime normalizer. This
inherits PR-WINDOW-PIT through the named existing normalizer theorem. -/
theorem exists_actual_primeNormalizer_inverse_subpower (g : PrimeWindowGeometry)
    {nu : ℝ} (hnu : 0 < nu) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ‖(primeNormalizer K S g ∅ Z)⁻¹‖ ≤ C * Z ^ nu := by
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.mp
    (HeckeSkeleton.PrimeNormalizer.normalizer_smallPower K S g nu hnu)
  obtain ⟨Z0, hZ0⟩ := eventually_atTop.mp hbound
  refine ⟨C, max 1 Z0, hC, le_max_left _ _, ?_⟩
  intro Z hZ
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hb := hZ0 Z ((le_max_right _ _).trans hZ)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hZ1) nu)] using hb

end HighBinVerified.NormFormNormalization

#print axioms HighBinVerified.NormFormNormalization.exists_actual_primeNormalizer_inverse_subpower
