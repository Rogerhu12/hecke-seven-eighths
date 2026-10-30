import HeckeGeneral.Analysis.CompactSchwartzLatticeBound
import HeckeGeneral.Arithmetic.SLocalNormSection

/-!
# Exact radial scaling of the trace-coordinate multiplier

The actual radial section multiplies every archimedean coordinate by the
degree-th root of its norm parameter. Conjugating by the trace model preserves
this scalar action. Consequently the inverse operator norm has the exact
reciprocal scalar factor, leaving a uniform bound on the fixed compact shape.
This supplies the radial factor for the orbital Schwartz majorant; it does
not itself assert a bound for an orbital integral.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Arithmetic
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "U" => (mixedEmbedding.mixedSpace K)ˣ

/-- The real dilation is scalar multiplication in the actual trace metric. -/
theorem traceUnitMulEquiv_realScale_apply (α : ℝ) (hα : α ≠ 0)
    (u : U) (z : V) :
    traceUnitMulEquiv K (realScaleMixedUnit K α hα * u) z =
      α • traceUnitMulEquiv K u z := by
  apply (traceToMixed K).injective
  rw [traceToMixed_traceUnitMulEquiv, map_smul,
    traceToMixed_traceUnitMulEquiv, Units.val_mul, realScaleMixedUnit_val]
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc]

/-- The inverse map carries the reciprocal radial scale, with no comparison
between the mixed-space norm and the trace norm. -/
theorem traceUnitMulEquiv_realScale_symm_apply (α : ℝ) (hα : α ≠ 0)
    (u : U) (z : V) :
    (traceUnitMulEquiv K (realScaleMixedUnit K α hα * u)).symm z =
      α⁻¹ • (traceUnitMulEquiv K u).symm z := by
  apply (traceUnitMulEquiv K (realScaleMixedUnit K α hα * u)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, traceUnitMulEquiv_realScale_apply,
    map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
    mul_inv_cancel₀ hα, one_smul]

theorem traceUnitMulEquiv_realScale_inverseCLM (α : ℝ) (hα : α ≠ 0) (u : U) :
    (traceUnitMulEquiv K (realScaleMixedUnit K α hα * u)).symm.toContinuousLinearMap =
      α⁻¹ • (traceUnitMulEquiv K u).symm.toContinuousLinearMap := by
  ext z
  exact traceUnitMulEquiv_realScale_symm_apply K α hα u z

/-- Exact operator-norm scaling for a positive real dilation. -/
theorem norm_traceUnitMulEquiv_realScale_inverseCLM (α : ℝ) (hα : 0 < α) (u : U) :
    ‖(traceUnitMulEquiv K (realScaleMixedUnit K α hα.ne' * u)).symm.toContinuousLinearMap‖ =
      α⁻¹ * ‖(traceUnitMulEquiv K u).symm.toContinuousLinearMap‖ := by
  rw [traceUnitMulEquiv_realScale_inverseCLM, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hα)]

/-- One compact-shape constant works simultaneously for every positive
radial parameter. The degree is retained in the reciprocal scale. -/
theorem exists_uniform_radial_traceUnit_inverse_bound
    (C : Set U) (hC : IsCompact C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : {r : ℝ // 0 < r}, ∀ u ∈ C,
      ‖(traceUnitMulEquiv K
        (realScaleMixedUnit K (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))
          (Real.rpow_pos_of_pos r.property _).ne' * u)).symm.toContinuousLinearMap‖ ≤
        (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹ * B := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_traceUnit_inverse_bound K C hC
  refine ⟨B, hB, fun r u hu => ?_⟩
  rw [norm_traceUnitMulEquiv_realScale_inverseCLM K _
    (Real.rpow_pos_of_pos r.property _)]
  exact mul_le_mul_of_nonneg_left (hbound u hu)
    (inv_nonneg.mpr (Real.rpow_pos_of_pos r.property _).le)

variable (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The abstract scalar formula is the actual S-local norm section. -/
theorem traceUnitMulEquiv_normSection_apply
    (r : {r : ℝ // 0 < r}) (u : U) (z : V) :
    traceUnitMulEquiv K ((sLocalNormSection K S r).1 * u) z =
      (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • traceUnitMulEquiv K u z :=
  traceUnitMulEquiv_realScale_apply K _ (Real.rpow_pos_of_pos r.property _).ne' u z

end HeckeGeneral.Analysis
