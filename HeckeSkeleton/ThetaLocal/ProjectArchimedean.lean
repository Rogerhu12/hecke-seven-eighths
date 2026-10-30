import HeckeGeneral.Analysis.GlobalThetaData
import HeckeGeneral.Characters.InfinityPacket
import HeckeSkeleton.ThetaLocal.ArchimedeanConstants
import HeckeSkeleton.ThetaLocal.ProjectArchimedeanSign

/-!
# The actual Hecke parameters in the local Mellin reflection

The direct profile uses the inverse radial character, hence the parameter
`heckeComplexParameter`, while the project names its negative `archRadial`.
This file keeps both conventions explicit. In particular, the Gamma quotient
of the direct-to-reflected Mellin identity is
`archGammaProduct θ⁻¹ s / archGammaProduct θ (-s)`.

The existing `reflectionMultiplier θ` contains the opposite quotient. Its
evaluation at `θ⁻¹` supplies the corrected quotient without changing any
existing definition. The equalities below concern genuine local Bessel
profiles and their finite products; they make no global period or Fubini claim.
-/

noncomputable section
set_option autoImplicit false

namespace HeckeSkeleton.ThetaLocal.Project

open NumberField IsDedekindDomain HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

theorem archShift_eq_archWeight (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archShift K θ v = archWeight (heckeComplexWeight K v.val v.property θ) := by
  unfold archShift archWeight
  rw [Nat.cast_natAbs]
  ring

theorem archShift_inv (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archShift K θ⁻¹ v = archShift K θ v := by
  simp only [archShift, heckeComplexWeight_inv, abs_neg]

theorem archRadial_eq_neg_parameter (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archRadial K θ v = -heckeComplexParameter K v.val v.property θ := rfl

theorem archRadial_inv (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archRadial K θ⁻¹ v = -archRadial K θ v := by
  simp only [archRadial, heckeComplexParameter_inv]

theorem actual_archExponent (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archExponent (heckeComplexWeight K v.val v.property θ)
        (heckeComplexParameter K v.val v.property θ) =
      (archShift K θ v : ℂ) + Complex.I * archRadial K θ v := by
  rw [archShift_eq_archWeight]
  unfold archExponent archRadial
  push_cast
  ring

/-- The genuine direct Bessel profile for the actual Hecke character. -/
def directProfile (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) : ℝ → ℂ :=
  archDirectProfile c (heckeComplexWeight K v.val v.property θ)
    (heckeComplexParameter K v.val v.property θ)

/-- The Weyl-reflected profile uses the opposite radial twist. -/
def reflectedProfile (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) : ℝ → ℂ :=
  archReflectedProfile c (heckeComplexWeight K v.val v.property θ)
    (heckeComplexParameter K v.val v.property θ)

/-- The reflected profile with the explicit fixed unit phase removed. -/
def normalizedReflectedProfile (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) : ℝ → ℂ :=
  archNormalizedReflectedProfile c (heckeComplexWeight K v.val v.property θ)
    (heckeComplexParameter K v.val v.property θ)

/-- A single factor of the project's actual `archGammaProduct`. -/
def localGamma (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (s : ℂ) : ℂ :=
  archGammaPair ((archShift K θ v : ℂ) + s + Complex.I * archRadial K θ v)

theorem directProfile_eq (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c t : ℝ) (ht : 0 < t) :
    directProfile K θ v c t =
      (t : ℂ) ^ ((archShift K θ v : ℂ) + Complex.I * archRadial K θ v) *
        (DedekindZetaZeroFree.KThird (c * Real.sqrt t) : ℂ) := by
  rw [directProfile, archDirectProfile_eq _ _ _ _ ht, actual_archExponent]

theorem reflectedProfile_eq (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c t : ℝ) (ht : 0 < t) :
    reflectedProfile K θ v c t =
      (t : ℂ) ^ ((archShift K θ v : ℂ) - Complex.I * archRadial K θ v) *
        (DedekindZetaZeroFree.KThird (c * Real.sqrt t) : ℂ) := by
  rw [reflectedProfile, archReflectedProfile_eq _ _ _ _ ht, archShift_eq_archWeight]
  congr 2
  unfold archRadial
  push_cast
  ring

/-- Character inversion exchanges the two actual radial profiles. -/
theorem reflectedProfile_eq_directProfile_inv (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) :
    reflectedProfile K θ v c = directProfile K θ⁻¹ v c := by
  simp [reflectedProfile, directProfile, archReflectedProfile,
    archDirectProfile, archExponent, heckeComplexWeight_inv,
    heckeComplexParameter_inv, archWeight_neg]

theorem localGamma_eq_direct_pair (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (s : ℂ) :
    localGamma K θ v s =
      archGammaPair (archExponent (heckeComplexWeight K v.val v.property θ)
        (heckeComplexParameter K v.val v.property θ) + s) := by
  rw [actual_archExponent]
  unfold localGamma
  congr 1
  ring

theorem localGamma_inv_eq_reflected_pair (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (s : ℂ) :
    localGamma K θ⁻¹ v s =
      archGammaPair (archExponent (heckeComplexWeight K v.val v.property θ)
        (-heckeComplexParameter K v.val v.property θ) + s) := by
  rw [localGamma_eq_direct_pair]
  simp only [heckeComplexWeight_inv, heckeComplexParameter_inv,
    archExponent, archWeight_neg]

theorem archGammaProduct_eq_prod_localGamma (θ : HeckeCharacter K) (s : ℂ) :
    archGammaProduct K θ s =
      ∏ v : {v : InfinitePlace K // v.IsComplex}, localGamma K θ v s := by
  unfold archGammaProduct localGamma archGammaPair
  apply Finset.prod_congr rfl
  intro v _
  ring

/-- The sign witness applies to the precise local factor of the project multiplier. -/
theorem localGamma_ratio_eq_radialGammaQuotient (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (s : ℂ) :
    localGamma K θ v s / localGamma K θ⁻¹ v (-s) =
      radialGammaQuotient (archShift K θ v) (archRadial K θ v) s := by
  simp only [localGamma, archGammaPair, radialGammaQuotient, archShift_inv, archRadial_inv,
    Complex.ofReal_neg, mul_neg, sub_eq_add_neg, add_assoc]

/-- The genuine reflected/direct ratio has the opposite radial sign. -/
theorem localGamma_reflected_ratio_eq_radialGammaQuotient (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (s : ℂ) :
    localGamma K θ⁻¹ v s / localGamma K θ v (-s) =
      radialGammaQuotient (archShift K θ v) (-archRadial K θ v) s := by
  simp only [localGamma, archGammaPair, radialGammaQuotient, archShift_inv, archRadial_inv,
    Complex.ofReal_neg, mul_neg, neg_neg, sub_eq_add_neg, add_assoc]

/-- The existing and genuine local Gamma quotients differ for nonzero radial parameter. -/
theorem localGamma_quotients_ne_of_radial_ne_zero (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (hv : archRadial K θ v ≠ 0) :
    (fun s : ℂ => localGamma K θ v s / localGamma K θ⁻¹ v (-s)) ≠
      (fun s : ℂ => localGamma K θ⁻¹ v s / localGamma K θ v (-s)) := by
  simp_rw [localGamma_ratio_eq_radialGammaQuotient,
    localGamma_reflected_ratio_eq_radialGammaQuotient]
  apply radialGammaQuotient_ne_neg _ _ _ hv
  rw [archShift_eq_archWeight]
  exact archWeight_ge_half _

/-- A fixed nonzero normalization cannot repair the project's local radial sign. -/
theorem localGamma_quotients_ne_const_mul_of_radial_ne_zero (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (hv : archRadial K θ v ≠ 0)
    (z : ℂ) (hz : z ≠ 0) :
    (fun s : ℂ => localGamma K θ v s / localGamma K θ⁻¹ v (-s)) ≠
      (fun s : ℂ => z * (localGamma K θ⁻¹ v s / localGamma K θ v (-s))) := by
  simp_rw [localGamma_ratio_eq_radialGammaQuotient,
    localGamma_reflected_ratio_eq_radialGammaQuotient]
  apply radialGammaQuotient_ne_const_mul_neg _ _ _ hv z hz
  rw [archShift_eq_archWeight]
  exact archWeight_ge_half _

theorem directProfile_hasMellin (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (hc : 0 < c)
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    HasMellin (directProfile K θ v c) s
      (archDirectConstant c (heckeComplexWeight K v.val v.property θ)
          (heckeComplexParameter K v.val v.property θ) *
        (archScale c : ℂ) ^ s * localGamma K θ v s) := by
  rw [localGamma_eq_direct_pair]
  apply arch_direct_hasMellin c hc
  have hm := archWeight_ge_half (heckeComplexWeight K v.val v.property θ)
  linarith

theorem reflectedProfile_hasMellin (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (hc : 0 < c)
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    HasMellin (reflectedProfile K θ v c) s
      (archReflectedConstant c (heckeComplexWeight K v.val v.property θ)
          (heckeComplexParameter K v.val v.property θ) *
        (archScale c : ℂ) ^ s * localGamma K θ⁻¹ v s) := by
  rw [localGamma_inv_eq_reflected_pair]
  apply arch_reflected_hasMellin c hc
  have hm := archWeight_ge_half (heckeComplexWeight K v.val v.property θ)
  linarith

/-- Raw reflection, including its fixed phase and the actual Hecke signs. -/
theorem reflectedProfile_mellin (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (hc : 0 < c)
    (s : ℂ) (hl : -(1 / 3 : ℝ) < s.re) (hr : s.re < (1 / 3 : ℝ)) :
    mellin (reflectedProfile K θ v c) s =
      mellin (directProfile K θ v c) (-s) * (archScale c : ℂ) ^ (2 * s) *
        archReflectionPhase c (heckeComplexParameter K v.val v.property θ) *
        (localGamma K θ⁻¹ v s / localGamma K θ v (-s)) := by
  rw [localGamma_inv_eq_reflected_pair, localGamma_eq_direct_pair]
  exact arch_reflected_mellin_common_strip c hc _ _ s hl hr

/-- Removing the explicit unit phase leaves the corrected Gamma quotient. -/
theorem normalizedReflectedProfile_mellin (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (hc : 0 < c)
    (s : ℂ) (hl : -(1 / 3 : ℝ) < s.re) (hr : s.re < (1 / 3 : ℝ)) :
    mellin (normalizedReflectedProfile K θ v c) s =
      mellin (directProfile K θ v c) (-s) * (archScale c : ℂ) ^ (2 * s) *
        (localGamma K θ⁻¹ v s / localGamma K θ v (-s)) := by
  rw [localGamma_inv_eq_reflected_pair, localGamma_eq_direct_pair]
  have hm := archWeight_ge_half (heckeComplexWeight K v.val v.property θ)
  exact arch_normalized_reflected_mellin c hc _ _ s (by linarith) (by linarith)

/-- The Gamma factor selected by the genuine direct-to-reflected pair. -/
def directReflectionGammaQuotient (θ : HeckeCharacter K) (s : ℂ) : ℂ :=
  archGammaProduct K θ⁻¹ s / archGammaProduct K θ (-s)

/-- The scale supplied by the actual local Bessel profiles. -/
def productScale (c : {v : InfinitePlace K // v.IsComplex} → ℝ) : ℝ :=
  ∏ v : {v : InfinitePlace K // v.IsComplex}, archScale (c v)

theorem productScale_pos
    (c : {v : InfinitePlace K // v.IsComplex} → ℝ) (hc : ∀ v, 0 < c v) :
    0 < productScale K c :=
  Finset.prod_pos (fun v _ => archScale_pos (c v) (hc v))

theorem productScale_cpow
    (c : {v : InfinitePlace K // v.IsComplex} → ℝ) (hc : ∀ v, 0 < c v) (z : ℂ) :
    (productScale K c : ℂ) ^ z =
      ∏ v : {v : InfinitePlace K // v.IsComplex}, (archScale (c v) : ℂ) ^ z := by
  have hprod : ∀ T : Finset {v : InfinitePlace K // v.IsComplex},
      ((∏ v ∈ T, archScale (c v) : ℝ) : ℂ) ^ z =
        ∏ v ∈ T, (archScale (c v) : ℂ) ^ z := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert v T hv ih =>
      rw [Finset.prod_insert hv, Finset.prod_insert hv, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (archScale_pos (c v) (hc v)).le
          (Finset.prod_nonneg (fun w _ => (archScale_pos (c w) (hc w)).le)), ih]
  exact hprod Finset.univ

theorem normalizedReflectedProfile_mellin_product (θ : HeckeCharacter K)
    (c : {v : InfinitePlace K // v.IsComplex} → ℝ) (hc : ∀ v, 0 < c v)
    (s : ℂ) (hl : -(1 / 3 : ℝ) < s.re) (hr : s.re < (1 / 3 : ℝ)) :
    (∏ v : {v : InfinitePlace K // v.IsComplex},
      mellin (normalizedReflectedProfile K θ v (c v)) s) =
      (∏ v : {v : InfinitePlace K // v.IsComplex},
        mellin (directProfile K θ v (c v)) (-s)) *
      (∏ v : {v : InfinitePlace K // v.IsComplex}, (archScale (c v) : ℂ) ^ (2 * s)) *
      directReflectionGammaQuotient K θ s := by
  simp_rw [normalizedReflectedProfile_mellin K θ _ _ (hc _) s hl hr]
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib]
  rw [directReflectionGammaQuotient, archGammaProduct_eq_prod_localGamma,
    archGammaProduct_eq_prod_localGamma]

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (F : FiniteMellinData K S)

/-- Exact audit of the existing multiplier: it contains the reversed Gamma pair. -/
theorem reflectionMultiplier_eq_gamma_quotient (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ) :
    reflectionMultiplier K S F θ u κ s =
      F.C₀⁻¹ * (F.A₀ : ℂ) ^ (2 * s) * finiteMellinFactor K S F u κ s *
        (archGammaProduct K θ s / archGammaProduct K θ⁻¹ (-s)) := by
  unfold reflectionMultiplier
  rw [archGammaProduct_eq_prod_localGamma, archGammaProduct_eq_prod_localGamma,
    ← Finset.prod_div_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  simp only [localGamma, archGammaPair, archShift_inv, archRadial_inv,
    Complex.ofReal_neg, mul_neg, sub_eq_add_neg, add_assoc,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The corrected direct-to-reflected multiplier is the old definition at `θ⁻¹`.
This additive adapter leaves `GlobalThetaData.reflectionMultiplier` untouched. -/
def directReflectionMultiplier (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ) : ℂ :=
  reflectionMultiplier K S F θ⁻¹ u κ s

theorem directReflectionMultiplier_eq (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ) :
    directReflectionMultiplier K S F θ u κ s =
      F.C₀⁻¹ * (F.A₀ : ℂ) ^ (2 * s) * finiteMellinFactor K S F u κ s *
        directReflectionGammaQuotient K θ s := by
  simp only [directReflectionMultiplier, reflectionMultiplier_eq_gamma_quotient,
    inv_inv, directReflectionGammaQuotient]

/-- The corrected multiplier acts on the finite product of the genuine local transforms.
The only additional assumption identifies the datum's positive scale with the
product of the actual local scales. The finite factor and `C₀` remain explicit. -/
theorem directReflectionMultiplier_mellin_product (θ : HeckeCharacter K)
    (c : {v : InfinitePlace K // v.IsComplex} → ℝ) (hc : ∀ v, 0 < c v)
    (hA : F.A₀ = productScale K c)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (s : ℂ) (hl : -(1 / 3 : ℝ) < s.re) (hr : s.re < (1 / 3 : ℝ)) :
    (∏ v : {v : InfinitePlace K // v.IsComplex},
        mellin (directProfile K θ v (c v)) (-s)) *
      directReflectionMultiplier K S F θ u κ s =
      F.C₀⁻¹ * finiteMellinFactor K S F u κ s *
        ∏ v : {v : InfinitePlace K // v.IsComplex},
          mellin (normalizedReflectedProfile K θ v (c v)) s := by
  rw [directReflectionMultiplier_eq,
    normalizedReflectedProfile_mellin_product K θ c hc s hl hr,
    hA, productScale_cpow K c hc]
  ring

/-- With all radial parameters zero, character inversion leaves the Gamma product fixed. -/
theorem archGammaProduct_inv_of_radial_zero (θ : HeckeCharacter K)
    (hθ : ∀ v : {v : InfinitePlace K // v.IsComplex}, archRadial K θ v = 0)
    (s : ℂ) : archGammaProduct K θ⁻¹ s = archGammaProduct K θ s := by
  simp only [archGammaProduct, archShift_inv, archRadial_inv, hθ, neg_zero]

/-- A sufficient missing hypothesis for the original multiplier to serve the same pair. -/
theorem directReflectionMultiplier_eq_of_radial_zero (θ : HeckeCharacter K)
    (hθ : ∀ v : {v : InfinitePlace K // v.IsComplex}, archRadial K θ v = 0)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ) :
    directReflectionMultiplier K S F θ u κ s =
      reflectionMultiplier K S F θ u κ s := by
  rw [directReflectionMultiplier_eq, reflectionMultiplier_eq_gamma_quotient]
  unfold directReflectionGammaQuotient
  rw [archGammaProduct_inv_of_radial_zero K θ hθ,
    archGammaProduct_inv_of_radial_zero K θ hθ]


end HeckeSkeleton.ThetaLocal.Project
