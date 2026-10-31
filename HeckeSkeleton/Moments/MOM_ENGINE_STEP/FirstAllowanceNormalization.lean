import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstSource

/-!
# Actual first allowances and their original profile scalar

The two positive allowances are computed from the original column
scale and the genuine common-support norms. The mutual first divisor
is left in the second common-support harmonic sum; it is not charged
again in these intermediate allowances. This is an exact choice in
weighted Cauchy, and keeps the same final 1/N(S) density once.

Only the original profile scalar window is supplied. The active Gauss
norm, both allowance square roots and parent normalization combine
internally into the proved first common-support weight.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

variable {K : Type} [Field K] [NumberField K]

def firstLeftAllowance (Z total : ℝ) (D E : Ideal (𝓞 K)) : ℝ :=
  Z ^ (total - idealLogLength Z D +
    firstAllowance (idealLogLength Z D) (idealLogLength Z E)
      (idealLogLength Z (firstActiveRadical D E)))

def firstRightAllowance (Z total : ℝ) (D E : Ideal (𝓞 K)) : ℝ :=
  Z ^ (total - idealLogLength Z E +
    firstAllowance (idealLogLength Z E) (idealLogLength Z D)
      (idealLogLength Z (firstActiveRadical D E)))

theorem firstLeftAllowance_pos (Z total : ℝ) (hZ : 0 < Z) (D E : Ideal (𝓞 K)) :
    0 < firstLeftAllowance Z total D E := Real.rpow_pos_of_pos hZ _

theorem firstRightAllowance_pos (Z total : ℝ) (hZ : 0 < Z) (D E : Ideal (𝓞 K)) :
    0 < firstRightAllowance Z total D E := Real.rpow_pos_of_pos hZ _

/-- Exact scalar identity before the local multiplicity inequality. -/
theorem first_allowance_scalar_identity (Z total M : ℝ) (hZ : 1 < Z)
    (D E : Ideal (𝓞 K)) :
    Z ^ (M - total) * Real.sqrt (Ideal.absNorm (firstActiveRadical D E) : ℝ) *
        Real.sqrt (firstLeftAllowance Z total D E) *
        Real.sqrt (firstRightAllowance Z total D E) / Z ^ M =
      firstCommonWeight Z D E := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [← rpow_idealLogLength Z hZ (firstActiveRadical D E) (firstActiveRadical_ne_zero D E)]
  unfold firstLeftAllowance firstRightAllowance firstCommonWeight
  simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le,
    ← Real.rpow_add hz, ← Real.rpow_sub hz]
  congr 1
  ring

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

local instance firstAllowanceNormalizationCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace FirstBlockPoolData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {mask : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

/-- The primitive input is a pointwise original profile scalar window,
not a normalized total kernel or parent estimate. -/
theorem normalized_allowance_prefactor
    {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
    {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
    (p : FirstBlockPoolData (profiles := profiles) chart P mask X hX) (hZ : 1 < Z)
    (total M amplitude : ℝ)
    (hprofile : p.weightBound ≤ amplitude * Z ^ (M - total)) :
    p.rowBound * Real.sqrt (firstLeftAllowance Z total DE.1 DE.2) *
        Real.sqrt (firstRightAllowance Z total DE.1 DE.2) / Z ^ M ≤
      amplitude * firstCommonWeight Z DE.1 DE.2 := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  unfold rowBound
  rw [b.activeNorm_eq]
  calc
    _ ≤ (amplitude * Z ^ (M - total)) *
        Real.sqrt (Ideal.absNorm (firstActiveRadical DE.1 DE.2) : ℝ) *
        Real.sqrt (firstLeftAllowance Z total DE.1 DE.2) *
        Real.sqrt (firstRightAllowance Z total DE.1 DE.2) / Z ^ M := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hprofile (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = amplitude * (Z ^ (M - total) *
        Real.sqrt (Ideal.absNorm (firstActiveRadical DE.1 DE.2) : ℝ) *
        Real.sqrt (firstLeftAllowance Z total DE.1 DE.2) *
        Real.sqrt (firstRightAllowance Z total DE.1 DE.2) / Z ^ M) := by ring
    _ = _ := by rw [first_allowance_scalar_identity Z total M hZ]

theorem normalized_allowance_prefactor_radical
    {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
    {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
    (p : FirstBlockPoolData (profiles := profiles) chart P mask X hX) (hZ : 1 < Z)
    (total M amplitude : ℝ) (hamp : 0 ≤ amplitude)
    (hprofile : p.weightBound ≤ amplitude * Z ^ (M - total)) :
    p.rowBound * Real.sqrt (firstLeftAllowance Z total DE.1 DE.2) *
        Real.sqrt (firstRightAllowance Z total DE.1 DE.2) / Z ^ M ≤
      amplitude / (Ideal.absNorm (CommonSupportMass.commonRadical DE.1 DE.2) : ℝ) := by
  have hD : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hE : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  exact (p.normalized_allowance_prefactor hZ total M amplitude hprofile).trans
    ((mul_le_mul_of_nonneg_left
      (firstCommonWeight_le_radical Z hZ DE.1 DE.2 hD hE b.common_support_eq) hamp).trans_eq
      (by ring))

end FirstBlockPoolData

namespace ActualFirstSource

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

/-- The actual allowances are positive and fixed before either Fourier
variable. The first mutual divisor remains in the subsequent true
second common-support carrier, where its harmonic density is paid. -/
def canonicalNormalization
    (s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
    (hZ : 1 < Z)
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) : s.Normalization where
  left v D _ _ := firstLeftAllowance Z (total v D) v.val.1 v.val.2
  right v D _ _ := firstRightAllowance Z (total v D) v.val.1 v.val.2
  left_pos v D _ _ := firstLeftAllowance_pos Z _ (zero_lt_one.trans hZ) _ _
  right_pos v D _ _ := firstRightAllowance_pos Z _ (zero_lt_one.trans hZ) _ _

end ActualFirstSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.normalized_allowance_prefactor
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.normalized_allowance_prefactor_radical
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.canonicalNormalization
