import HeckeGeneral.Characters.LocalResidueCosetFourier

/-!
# Haar-normalized Fourier transforms of actual local residue cosets

The integer ring is compact and open, so its mass under every additive Haar
measure is finite and strictly positive. Dividing by this actual mass leaves
the inverse prime-power norm, the negative-sign standard-character phase,
and the support bound with the actual different exponent. No normalization
of the original Haar measure is imposed.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain NumberField.StandardAddChar
  NumberField.AdelicFourier MeasureTheory
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
  [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

/-- Compactness excludes infinite mass, and openness and nonemptiness exclude zero. -/
theorem localIntegerHaarMass_pos :
    0 < μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  exact ENNReal.toReal_pos
    ((isOpenAdicCompletionIntegers K v).measure_ne_zero μ ⟨0, Subring.zero_mem _⟩)
    (isCompactAdicCompletionIntegers K v).measure_lt_top.ne

theorem localIntegerHaarMass_ne_zero :
    μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ≠ 0 :=
  (localIntegerHaarMass_pos K v μ).ne'

/-- The local normalization cancels the true integer-ring Haar mass. -/
theorem normalizedFourier_localIntegerResidueCosetIndicator
    (n : ℕ) (center : LocalIntegerRing K v) (w : v.adicCompletion K) :
    ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
        fourierIntegral (psiLocal K v) μ
          (localIntegerResidueCosetIndicator K v n center) w =
      (((v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) : ℝ) : ℂ) *
        psiLocal K v (-((center : v.adicCompletion K) * w)) *
        (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + (n : ℤ))
          then 1 else 0) := by
  have hm : (μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (localIntegerHaarMass_ne_zero K v μ)
  rw [fourierIntegral_localIntegerResidueCosetIndicator_mass, Complex.ofReal_mul]
  calc
    _ = (((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
          (μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ)) *
        ((((v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) : ℝ) : ℂ) *
          psiLocal K v (-((center : v.adicCompletion K) * w)) *
          (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + (n : ℤ))
            then 1 else 0)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hm, one_mul]

/-- The same formula for a residue class and its actual chosen integer lift. -/
theorem normalizedFourier_localResidueCosetIndicator
    (n : ℕ) (r : LocalResidueRing K v n) (w : v.adicCompletion K) :
    ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
        fourierIntegral (psiLocal K v) μ (localResidueCosetIndicator K v n r) w =
      (((v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) : ℝ) : ℂ) *
        psiLocal K v (-((localResidueLift K v n r : v.adicCompletion K) * w)) *
        (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + (n : ℤ))
          then 1 else 0) := by
  rw [localResidueCosetIndicator_eq_center K v n r (localResidueLift K v n r)
    (localResidueLift_mk K v n r)]
  exact normalizedFourier_localIntegerResidueCosetIndicator K v μ n _ w

end HeckeGeneral.Characters
