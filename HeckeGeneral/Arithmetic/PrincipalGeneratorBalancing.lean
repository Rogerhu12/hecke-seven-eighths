import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A compact normalized shape for ordinary-unit orbits

The representatives come from Mathlib's actual Dirichlet fundamental cone.
The scale is the degree-th root of the multiplicative archimedean norm.
This module concerns ordinary units; S-unit unfolding is a separate step.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-- The length scale corresponding to the multiplicative norm. -/
def arithmeticNormRoot (x : mixedSpace K) : ℝ :=
  mixedEmbedding.norm x ^ ((Module.finrank ℚ K : ℝ)⁻¹)

theorem arithmeticNormRoot_pos {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) : 0 < arithmeticNormRoot K x :=
  Real.rpow_pos_of_pos (lt_of_le_of_ne (mixedEmbedding.norm_nonneg x) hx.symm) _

theorem arithmeticNormRoot_pow (x : mixedSpace K) :
    arithmeticNormRoot K x ^ Module.finrank ℚ K = mixedEmbedding.norm x := by
  exact Real.rpow_inv_natCast_pow (mixedEmbedding.norm_nonneg x)
    (Module.finrank_pos.ne')

theorem norm_normalize_arithmeticNormRoot {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) :
    mixedEmbedding.norm ((arithmeticNormRoot K x)⁻¹ • x) = 1 := by
  rw [mixedEmbedding.norm_smul,
    abs_of_pos (inv_pos.mpr (arithmeticNormRoot_pos K hx)), inv_pow,
    arithmeticNormRoot_pow, inv_mul_cancel₀ hx]

/-- A closed, compact slice, including the boundary of the fundamental cone. -/
def balancedNormOneShape : Set (mixedSpace K) :=
  closure (fundamentalCone.normLeOne K) ∩ {x | mixedEmbedding.norm x = 1}

theorem isCompact_balancedNormOneShape : IsCompact (balancedNormOneShape K) := by
  exact (fundamentalCone.isBounded_normLeOne K).isCompact_closure.inter_right
    (isClosed_eq (mixedEmbedding.continuous_norm K) continuous_const)

theorem norm_eq_one_of_mem_balancedNormOneShape {x : mixedSpace K}
    (hx : x ∈ balancedNormOneShape K) : mixedEmbedding.norm x = 1 := hx.2

/-- No coordinate degenerates in the compact normalized slice. -/
theorem normAtPlace_ne_zero_of_mem_balancedNormOneShape {x : mixedSpace K}
    (hx : x ∈ balancedNormOneShape K) (w : InfinitePlace K) : normAtPlace w x ≠ 0 := by
  apply mixedEmbedding.norm_ne_zero_iff.mp
    (show mixedEmbedding.norm x ≠ 0 by rw [hx.2]; norm_num)

theorem exists_unit_normalize_mem_balancedNormOneShape {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ,
      (arithmeticNormRoot K x)⁻¹ • (u • x) ∈ balancedNormOneShape K := by
  have hn := norm_normalize_arithmeticNormRoot K hx
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem
    (show mixedEmbedding.norm ((arithmeticNormRoot K x)⁻¹ • x) ≠ 0 by rw [hn]; norm_num)
  have hc : u • ((arithmeticNormRoot K x)⁻¹ • x) =
      (arithmeticNormRoot K x)⁻¹ • (u • x) := by
    simp only [unitSMul_smul, mul_smul_comm]
  rw [hc] at hu
  have hnorm : mixedEmbedding.norm ((arithmeticNormRoot K x)⁻¹ • (u • x)) = 1 := by
    rw [← hc, norm_unit_smul, hn]
  exact ⟨u, subset_closure ⟨hu, hnorm.le⟩, hnorm⟩

/-- One field-dependent constant controls every unit-balanced representative. -/
theorem exists_unit_norm_le_arithmeticNormRoot :
    ∃ C : ℝ, 0 < C ∧ ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 →
      ∃ u : (𝓞 K)ˣ, ‖u • x‖ ≤ C * arithmeticNormRoot K x := by
  obtain ⟨C, hC, hbound⟩ := (isCompact_balancedNormOneShape K).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := exists_unit_normalize_mem_balancedNormOneShape K hx
  refine ⟨u, ?_⟩
  have h := hbound _ hu
  rw [_root_.norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (arithmeticNormRoot_pos K hx))] at h
  exact (div_le_iff₀ (arithmeticNormRoot_pos K hx)).mp (by simpa [div_eq_mul_inv, mul_comm] using h)

end HeckeGeneral.Arithmetic
