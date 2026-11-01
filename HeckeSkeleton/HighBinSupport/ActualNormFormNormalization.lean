import HeckeSkeleton.PrimeNormalizer

/-!
The actual normalizer dependency of the sharp norm-form route.

The unconditional window prime ideal theorem is proved in `WindowPIT`
from the prime-counting asymptotic.  The existing normalizer deduction
therefore bounds the unchanged inverse with a fixed positive constant.
No admitted prime-window estimate or normalizer-bound premise is used.
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

/-- A concrete uniform cutoff from the proved unconditional window theorem. -/
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
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hZ1) nu)] using hb

end HighBinVerified.NormFormNormalization

#print axioms HighBinVerified.NormFormNormalization.exists_actual_primeNormalizer_inverse_subpower
