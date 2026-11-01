import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondSourceNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstAllowanceNormalization

/-!
# The second source pays the actual first normalization allowance

The intermediate first Cauchy scales contain no inverse first-divisor
factor. Their original length exponent is exactly a₀+q+w+B. Dividing
the complete second-source weight by that scale leaves the one pool
length allowance and the genuine moving error norm. The first divisor
is still paid by the second common-support harmonic sum, once.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- The scalar identity belongs to the original coefficient scales,
not to an assumed estimate for a transformed source or child moment. -/
theorem FirstCommonCharacterBlock.secondSourceWeight_relative_allowance_le
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w B krow g ell NL NR N : ℝ)
    (hN : N = Z ^ (a₀ + q + w + B))
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) :
    b.secondSourceWeight C Z a₀ q wo w B krow g ell 1 NL NR r D a d ha hd h / N ≤
      orbitalFieldFactor K * Z ^ wo * Z ^ ell /
        (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hNpos : 0 < N := by
    rw [hN]
    exact Real.rpow_pos_of_pos hz _
  apply (div_le_div_of_nonneg_right
    (b.secondSourceWeight_without_density_le C Z hZ a₀ q wo w B krow g ell
      NL NR r D hrow hcentral a d ha hd h) hNpos.le).trans_eq
  rw [← hN]
  calc
    _ = (orbitalFieldFactor K * Z ^ wo * Z ^ ell /
        (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ)) * (N / N) := by ring
    _ = _ := by rw [div_self hNpos.ne', mul_one]

/-- The actual left first allowance has exactly the exponent cancelled
above. The amplifier loss w occurs once in the residual column length
and once in its paid allowance, and cancels here. -/
theorem firstLeftAllowance_second_exponent
    (Z A q w : ℝ) (D E : Ideal (𝓞 K)) :
    firstLeftAllowance Z (A + q) D E =
      Z ^ ((A - idealLogLength Z D - w) + q + w +
        firstAllowance (idealLogLength Z D) (idealLogLength Z E)
          (idealLogLength Z (firstActiveRadical D E))) := by
  unfold firstLeftAllowance
  congr 1
  ring

theorem firstRightAllowance_second_exponent
    (Z A q w : ℝ) (D E : Ideal (𝓞 K)) :
    firstRightAllowance Z (A + q) D E =
      Z ^ ((A - idealLogLength Z E - w) + q + w +
        firstAllowance (idealLogLength Z E) (idealLogLength Z D)
          (idealLogLength Z (firstActiveRadical D E))) := by
  unfold firstRightAllowance
  congr 1
  ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondSourceWeight_relative_allowance_le
#print axioms HeckeSkeleton.Moments.EngineStep.firstLeftAllowance_second_exponent
