import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
The allowed section's multiplicativity already
normalizes its generator of the unit ideal modulo sixth powers.  This is
only a finite algebraic consequence; no row Hecke character is constructed.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Global

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem AllowedGeneratorInput.generator_eq_sixth_power_of_ideal_eq_one
    (h : AllowedGeneratorInput K S D) (I : ExteriorIdeal K S) (hI : I.val = 1) :
    ∃ u : S.unit K, D.generator I = (S.unitEquivUnitsInteger K u).val ^ 6 := by
  have hII : exteriorMul K S I I = I := by
    apply Subtype.ext
    change I.val * I.val = I.val
    rw [hI]
    simp
  obtain ⟨u, hu⟩ := h.multiplicative I I
  rw [hII] at hu
  have he : (S.unitEquivUnitsInteger K u).val ^ 6 * D.generator I = 1 := by
    apply mul_right_cancel₀ (D.generator_ne_zero I)
    simpa only [one_mul] using hu.symm
  have huv : (S.unitEquivUnitsInteger K (u⁻¹)).val *
      (S.unitEquivUnitsInteger K u).val = 1 := by
    change ((S.unitEquivUnitsInteger K (u⁻¹) *
      S.unitEquivUnitsInteger K u : (S.integer K)ˣ) : S.integer K) = 1
    rw [← map_mul]
    simp
  have hpow : (S.unitEquivUnitsInteger K (u⁻¹)).val ^ 6 *
      (S.unitEquivUnitsInteger K u).val ^ 6 = 1 := by
    rw [← mul_pow, huv, one_pow]
  refine ⟨u⁻¹, ?_⟩
  calc
    D.generator I = 1 * D.generator I := (one_mul _).symm
    _ = ((S.unitEquivUnitsInteger K (u⁻¹)).val ^ 6 *
        (S.unitEquivUnitsInteger K u).val ^ 6) * D.generator I := by rw [hpow]
    _ = (S.unitEquivUnitsInteger K (u⁻¹)).val ^ 6 *
        ((S.unitEquivUnitsInteger K u).val ^ 6 * D.generator I) := mul_assoc _ _ _
    _ = (S.unitEquivUnitsInteger K (u⁻¹)).val ^ 6 := by rw [he, mul_one]

end HeckeGeneral.ThetaSkeleton.Global
