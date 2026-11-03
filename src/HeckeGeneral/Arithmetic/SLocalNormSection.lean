import HeckeGeneral.Arithmetic.SUnitNormOneQuotient

/-!
# A positive radial section of the actual S-local product norm

The section dilates every archimedean coordinate by the degree-th root of the
specified positive norm, and leaves every finite coordinate equal to one.
The degree factor includes the multiplicity two of complex places through
the actual mixed-embedding norm. No choice of an S-unit representative is
used in this radial section.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The section is defined only for strictly positive radial parameters. -/
def sLocalNormSection (r : {r : ℝ // 0 < r}) : sLocalMultiplicativeGroup K S :=
  (realScaleMixedUnit K (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))
    (Real.rpow_pos_of_pos r.property _).ne', 1)

@[simp] theorem sLocalProductNorm_section (r : {r : ℝ // 0 < r}) :
    sLocalProductNorm K S (sLocalNormSection K S r) = r.val := by
  change mixedEmbedding.norm
      (algebraMap ℝ (mixedSpace K) (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))) *
      (∏ v : S, ‖(1 : v.val.adicCompletion K)‖) = r.val
  simp only [norm_one, Finset.prod_const_one, mul_one,
    Algebra.algebraMap_eq_smul_one, mixedEmbedding.norm_smul, map_one,
    abs_of_pos (Real.rpow_pos_of_pos r.property _)]
  exact Real.rpow_inv_natCast_pow r.property.le Module.finrank_pos.ne'

omit [Fintype S] in
theorem continuous_sLocalNormSection : Continuous (sLocalNormSection K S) := by
  have hr : Continuous (fun r : {r : ℝ // 0 < r} =>
      r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹)) :=
    continuous_subtype_val.rpow_const (fun r => Or.inl r.property.ne')
  exact (continuous_realScaleMixedUnit K _ hr
    (fun r => (Real.rpow_pos_of_pos r.property _).ne')).prodMk continuous_const

end HeckeGeneral.Arithmetic
