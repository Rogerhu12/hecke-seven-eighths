import Expansion.ActualPrimeNormalizer

/-!
The actual normalizer dependency of the sharp norm-form route.

The physical original field supplies its complex-place hypothesis.  The
proved actual prime-window lower theorem then bounds the unchanged
normalizer inverse, with its constant absorbed into a common cutoff.
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

/-- A concrete uniform cutoff from the actual prime-window theorem. -/
theorem exists_actual_primeNormalizer_inverse_subpower
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (g : PrimeWindowGeometry)
    {nu : ℝ} (hnu : 0 < nu) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ‖(primeNormalizer K S g ∅ Z)⁻¹‖ ≤ C * Z ^ nu := by
  obtain ⟨Z0, hZ0, hbound⟩ :=
    Expansion.Project.exists_actual_primeNormalizer_inverse_bound K S hcomplex g nu hnu
  refine ⟨1, Z0, by norm_num, hZ0, ?_⟩
  intro Z hZ
  simpa only [one_mul] using (hbound Z hZ).2

end HighBinVerified.NormFormNormalization

#print axioms HighBinVerified.NormFormNormalization.exists_actual_primeNormalizer_inverse_subpower
