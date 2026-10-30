import HeckeGeneral.Arithmetic.SLocalNormSection

/-!
# Algebra of the actual positive radial section

The degree-th-root archimedean dilation is multiplicative on positive
real parameters. The finite coordinates remain one. These are identities
of the existing local-group elements, proved from their real unit values.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

@[simp] theorem sLocalNormSection_one :
    sLocalNormSection K S ⟨1, zero_lt_one⟩ = 1 := by
  apply Prod.ext
  · apply Units.ext
    change algebraMap ℝ (mixedSpace K)
      ((1 : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹)) = 1
    rw [Real.one_rpow, map_one]
  · rfl

/-- Multiplication follows from the real positive-root identity, without
assuming a homomorphism structure for the section. -/
theorem sLocalNormSection_mul (r q : {r : ℝ // 0 < r}) :
    sLocalNormSection K S ⟨r.val * q.val, mul_pos r.property q.property⟩ =
      sLocalNormSection K S r * sLocalNormSection K S q := by
  apply Prod.ext
  · apply Units.ext
    change algebraMap ℝ (mixedSpace K)
      ((r.val * q.val) ^ ((Module.finrank ℚ K : ℝ)⁻¹)) =
        algebraMap ℝ (mixedSpace K) (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹)) *
          algebraMap ℝ (mixedSpace K) (q.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))
    rw [Real.mul_rpow r.property.le q.property.le, map_mul]
  · simp [sLocalNormSection]

/-- Taking the reciprocal radius inverts the actual section element. -/
theorem sLocalNormSection_inv (r : {r : ℝ // 0 < r}) :
    sLocalNormSection K S ⟨r.val⁻¹, inv_pos.mpr r.property⟩ =
      (sLocalNormSection K S r)⁻¹ := by
  apply Prod.ext
  · apply Units.ext
    change algebraMap ℝ (mixedSpace K)
      ((r.val⁻¹) ^ ((Module.finrank ℚ K : ℝ)⁻¹)) =
        algebraMap ℝ (mixedSpace K) ((r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹)
    rw [Real.inv_rpow r.property.le]
  · rfl

/-- The inverse local Poisson base point has reciprocal radius. No condition
on the remaining local-group element is needed for this algebraic identity. -/
theorem sLocalNormSection_mul_inverse (r : {r : ℝ // 0 < r})
    (x : sLocalMultiplicativeGroup K S) :
    (sLocalNormSection K S r * x)⁻¹ =
      sLocalNormSection K S ⟨r.val⁻¹, inv_pos.mpr r.property⟩ * x⁻¹ := by
  rw [mul_inv_rev, sLocalNormSection_inv]
  exact mul_comm _ _

end HeckeGeneral.Arithmetic
