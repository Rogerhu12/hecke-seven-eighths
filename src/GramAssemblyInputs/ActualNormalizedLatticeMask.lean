import ActualIdealProductPolarMass
import HeckeGeneral.Analysis.TraceProductPoisson

/-!
UNCOMPILED candidate. The normalized coefficient is the actual finite
frequency sum from weighted lattice Poisson, divided by the genuine quotient
cardinality. Its magnitude and origin are proved from the original weight.
The dual tail uses the already constructed uniform two-column ideal mass.
This does not assert an arithmetic weight or a complete Gram estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.ActualNormalizedLatticeMaskDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open ActualIdealProductPolarMassDraft
open scoped Classical BigOperators FourierTransform nonZeroDivisors

section FiniteMask
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (L J : Submodule ℤ E) [Fintype (LatticeQuotient L J)]

/-- Normalization uses the actual quotient rather than a supplied modulus. -/
def normalizedLatticeMaskCoefficient (w : LatticeQuotient L J → ℂ)
    (m : dualLattice J) : ℂ :=
  (Fintype.card (LatticeQuotient L J) : ℂ)⁻¹ * latticeMaskCoefficient L J w m

theorem norm_normalizedLatticeMaskCoefficient_le
    (w : LatticeQuotient L J → ℂ) {Q : ℝ}
    (hw : ∀ q, ‖w q‖ ≤ Q) (m : dualLattice J) :
    ‖normalizedLatticeMaskCoefficient L J w m‖ ≤ Q := by
  have hc : (Fintype.card (LatticeQuotient L J) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ q, ‖w q‖) ≤ (Fintype.card (LatticeQuotient L J) : ℝ) * Q := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hw q)
  calc
    _ = (Fintype.card (LatticeQuotient L J) : ℝ)⁻¹ * ‖latticeMaskCoefficient L J w m‖ := by
      simp only [normalizedLatticeMaskCoefficient, norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (Fintype.card (LatticeQuotient L J) : ℝ)⁻¹ *
        ((Fintype.card (LatticeQuotient L J) : ℝ) * Q) :=
      mul_le_mul_of_nonneg_left ((norm_latticeMaskCoefficient_le L J w m).trans hs)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = Q := by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem normalizedLatticeMaskCoefficient_zero_of_sum_zero
    (w : LatticeQuotient L J → ℂ) (hw : ∑ q, w q = 0) :
    normalizedLatticeMaskCoefficient L J w 0 = 0 := by
  rw [normalizedLatticeMaskCoefficient, latticeMaskCoefficient_zero, hw, mul_zero]

/-- Undoing normalization is exact even at nonprimitive frequencies. -/
theorem latticeMaskCoefficient_eq_card_mul_normalized
    (w : LatticeQuotient L J → ℂ) (m : dualLattice J) :
    latticeMaskCoefficient L J w m = (Fintype.card (LatticeQuotient L J) : ℂ) *
      normalizedLatticeMaskCoefficient L J w m := by
  have hc : (Fintype.card (LatticeQuotient L J) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [normalizedLatticeMaskCoefficient, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

end FiniteMask

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "W" => traceProductSpace K

include S Γ in
/-- A single constant works for every actual period ideal and every
translation. The normalized Fourier bound comes from the weight itself. -/
theorem exists_uniform_idealProduct_normalized_mask_tail (A : ℕ) (hA : 2 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : (Ideal (𝓞 K))⁰) (L : Submodule ℤ W)
      [Fintype (LatticeQuotient L (idealProductLattice K I))]
      (w : LatticeQuotient L (idealProductLattice K I) → ℂ)
      (F : SchwartzMap W ℂ) (N Q : ℝ), 0 < N → 0 ≤ Q →
      (∀ q, ‖w q‖ ≤ Q) → ∀ v : W,
        ‖∑' m : NonzeroLattice (dualLattice (idealProductLattice K I)),
          (𝓕 (F : W → ℂ) ((N ^ (Module.finrank ℚ K : ℝ)⁻¹) •
            ((m : dualLattice (idealProductLattice K I)) : W))) *
            latticePhase v (m : dualLattice (idealProductLattice K I)) *
              normalizedLatticeMaskCoefficient L (idealProductLattice K I) w m‖ ≤
          C * Q * SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F) *
            ((Ideal.absNorm I.val : ℝ) / N) ^ A := by
  obtain ⟨C, hC, htail⟩ := exists_uniform_idealProduct_weighted_tail K S Γ A hA
  refine ⟨C, hC, fun I L _ w F N Q hN hQ hw v => ?_⟩
  let D := dualLattice (idealProductLattice K I)
  let b : NonzeroLattice D → ℂ := fun m => latticePhase v (m : D) *
    normalizedLatticeMaskCoefficient L (idealProductLattice K I) w m
  have hb : ∀ m, ‖b m‖ ≤ Q := by
    intro m
    simpa only [b, norm_mul, norm_latticePhase, one_mul] using
      norm_normalizedLatticeMaskCoefficient_le L (idealProductLattice K I) w hw m
  have h := htail I (𝓕 F) N Q hN hQ b hb
  simpa only [b, SchwartzMap.fourier_coe, mul_comm, mul_left_comm, mul_assoc] using h

end HeckeGeneral.Analysis.ActualNormalizedLatticeMaskDraft
