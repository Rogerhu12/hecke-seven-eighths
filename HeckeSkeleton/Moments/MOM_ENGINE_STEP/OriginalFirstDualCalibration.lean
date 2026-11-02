import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstTerminalCalibration

set_option linter.unusedSectionVars false

/-!
# The first pure-dual calibration from original individual windows

The raw record is independent of any prime pool.  It contains the
original column ideals, original profile seminorm bounds, actual mask
prime dictionary, and the existing whole-factor tail windows.  Its
dual-zero amplitude is computed, including the original inverse radius
and the full common principal mask.  No original profile is required to
vanish at zero and no summed zero normalization is an input.

The same record applies to a direct first entrance and to an amplified
first entrance.  The final conversion below merely installs its proved
pointwise normalization in the unchanged amplified source.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Original individual source windows, before any pool or terminal
sum. The profile at the additive origin is unrestricted. -/
structure FirstDualOriginalWindows
    (C : A.GeneralArithmeticContext σ η hS)
    {ι : Type*} (columns : Finset ι) (I : ι → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel columns columns I I,
      FirstCommonCharacterBlock I I DE.val)
    (profiles : ι → ι → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ)
    (Z X normBound Lmax Nsave decay : ℝ) where
  productExponent : ℝ
  /-- A sharp product window on the actual nonzero profiles. The
  full Cartesian carrier and the larger tail window are unchanged. -/
  zeroProductExponent : ℝ
  zeroProductExponent_nonneg : 0 ≤ zeroProductExponent
  zero_product_norm : ∀ ij ∈ columns ×ˢ columns, profiles ij.1 ij.2 ≠ 0 →
    (Ideal.absNorm ((I ij.1).val * (I ij.2).val) : ℝ) ≤ Z ^ zeroProductExponent
  profileExponent : ℝ
  maskExponent : ℝ
  modulusExponent : ℝ
  tailProfileConstant : ℝ
  zeroProfileConstant : ℝ
  zeroProfileConstant_nonneg : 0 ≤ zeroProfileConstant
  zeroProfileExponent : ℝ
  /-- The actual inverse-radius window used only by the pure-dual zero
  term. It is independent of the larger pair-modulus tail window. -/
  zeroInverseRadiusExponent : ℝ
  zero_inverse_radius : radius.val⁻¹ ≤ Z ^ zeroInverseRadiusExponent
  windows : FirstTailWindows hΓ C columns columns I I blocks
    sTail profiles radius M k Z productExponent profileExponent maskExponent
    modulusExponent tailProfileConstant
  exponent_bound : firstTailExponent k productExponent profileExponent maskExponent
    modulusExponent ≤ Lmax
  cutoff_eq : X = Z ^ firstTailCutoffExponent Lmax Nsave decay
  zero_profile : ∀ v ∈ firstZeroPairs columns columns I I,
    sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) ≤
      zeroProfileConstant * Z ^ zeroProfileExponent
  maskIdeal : Ideal (𝓞 K)
  mask_ne_zero : maskIdeal ≠ 0
  mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBound
  original_mask : OriginalMaskPrimeData M maskIdeal
  column_norm : ∀ i ∈ columns, (Ideal.absNorm (I i).val : ℝ) ≤ Z ^ normBound

namespace FirstDualOriginalWindows

variable {C : A.GeneralArithmeticContext σ η hS}
variable {ι : Type*} {columns : Finset ι} {I : ι → A.Exterior}
variable {blocks : ∀ DE : FirstZeroLabel columns columns I I,
  FirstCommonCharacterBlock I I DE.val}
variable {profiles : ι → ι → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {M : Finset (HeightOneSpectrum A.R)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ}
variable {Z X normBound Lmax Nsave decay : ℝ}
variable (T : FirstDualOriginalWindows (hΓ := hΓ) C columns I blocks profiles radius M
  sTail sZero k Z X normBound Lmax Nsave decay)

def zeroExponent (δ : ℝ) : ℝ :=
  T.zeroProfileExponent + T.zeroInverseRadiusExponent + δ + T.zeroProductExponent / 2

/-- Install the product window proved only for the same nonzero
original profiles; no column is removed or reindexed. -/
def withZeroProduct (exponent : ℝ) (hpos : 0 ≤ exponent)
    (hnorm : ∀ ij ∈ columns ×ˢ columns, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((I ij.1).val * (I ij.2).val) : ℝ) ≤ Z ^ exponent) :
    FirstDualOriginalWindows (hΓ := hΓ) C columns I blocks profiles radius M
      sTail sZero k Z X normBound Lmax Nsave decay :=
  { T with zeroProductExponent := exponent, zeroProductExponent_nonneg := hpos,
    zero_product_norm := hnorm }

@[simp] theorem withZeroProduct_zeroExponent
    (exponent δ : ℝ) (hpos : 0 ≤ exponent)
    (hnorm : ∀ ij ∈ columns ×ˢ columns, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((I ij.1).val * (I ij.2).val) : ℝ) ≤ Z ^ exponent) :
    (T.withZeroProduct exponent hpos hnorm).zeroExponent δ =
      T.zeroProfileExponent + T.zeroInverseRadiusExponent + δ + exponent / 2 := rfl

@[simp] theorem withZeroProduct_windows
    (exponent : ℝ) (hpos : 0 ≤ exponent)
    (hnorm : ∀ ij ∈ columns ×ˢ columns, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((I ij.1).val * (I ij.2).val) : ℝ) ≤ Z ^ exponent) :
    (T.withZeroProduct exponent hpos hnorm).windows = T.windows := rfl

/-- Install a sharper original radius window without changing the
source, profiles, mask, cutoff, or any of the original tail windows. -/
def withZeroInverseRadius (exponent : ℝ) (hradius : radius.val⁻¹ ≤ Z ^ exponent) :
    FirstDualOriginalWindows (hΓ := hΓ) C columns I blocks profiles radius M
      sTail sZero k Z X normBound Lmax Nsave decay :=
  { T with zeroInverseRadiusExponent := exponent, zero_inverse_radius := hradius }

@[simp] theorem withZeroInverseRadius_zeroExponent
    (exponent δ : ℝ) (hradius : radius.val⁻¹ ≤ Z ^ exponent) :
    (T.withZeroInverseRadius exponent hradius).zeroExponent δ =
      T.zeroProfileExponent + exponent + δ + T.zeroProductExponent / 2 := rfl

@[simp] theorem withZeroInverseRadius_windows
    (exponent : ℝ) (hradius : radius.val⁻¹ ≤ Z ^ exponent) :
    (T.withZeroInverseRadius exponent hradius).windows = T.windows := rfl

def zeroAmplitude (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  originalFirstMaskConstant (K := K) normBound δ hB hδ *
    T.zeroProfileConstant * Z ^ T.zeroExponent δ

theorem zeroAmplitude_nonneg (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ T.zeroAmplitude hB δ hδ := by
  sorry

/-- The actual first mask-divisor sum is paid by the original prime
dictionary and original column norms. Its small-power constant is fixed
before this source. -/
theorem zero_normalization (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ) :
    ∀ v ∈ firstZeroPairs columns columns I I,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) ≤
          T.zeroAmplitude hB δ hδ / Real.sqrt (Z ^ T.zeroProductExponent) := by
  sorry

/-- Both first terminal scalars are computed from the same original
profile windows, independently of any prime pool. -/
def cost (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (ε Cerror Czero : ℝ) : ℝ :=
  Czero * T.zeroAmplitude hB δ hδ * Z ^ (T.zeroProductExponent * ε) +
    Cerror * T.tailProfileConstant * Z ^ (-Nsave)

theorem tailMass_bound (hdecay : 1 < decay) (Ctail : ℝ) (hCtail : 0 ≤ Ctail) :
    Ctail * X ^ (1 - decay) *
      firstBlockTailMass hΓ C columns columns I I blocks sTail profiles radius M ≤
      (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) *
        T.tailProfileConstant * Z ^ (-Nsave) := by
  sorry

/-- The normalized zero scalar retains the literal original parent
width. Only its explicit real exponent is compared at the final step. -/
theorem normalized_zero_le (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (fiber : ℕ) (parentWidth ε Czero terminalExponent : ℝ) (hC : 0 ≤ Czero)
    (hledger : T.zeroExponent δ + T.zeroProductExponent * ε - parentWidth ≤ terminalExponent) :
    ((fiber : ℝ) * Czero * T.zeroAmplitude hB δ hδ * Z ^ (T.zeroProductExponent * ε)) /
        Z ^ parentWidth ≤
      (fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant * Z ^ terminalExponent := by
  sorry

theorem normalized_tail_le (fiber : ℕ) (parentWidth Cerror terminalExponent : ℝ)
    (hC : 0 ≤ Cerror) (hledger : -Nsave - parentWidth ≤ terminalExponent) :
    ((fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ (-Nsave)) / Z ^ parentWidth ≤
      (fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ terminalExponent := by
  sorry

end FirstDualOriginalWindows

variable {C : A.GeneralArithmeticContext σ η hS}
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
variable {a : RealParameters} {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualFirstSource

variable (s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {normBound Lmax Nsave decay : ℝ}

/-- The proved per-pair normalization is installed on this exact
source. No annularity field or aggregate terminal bound is introduced. -/
def originalDualTerminalCalibration
    (T : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sTail sZero k Z X normBound Lmax Nsave decay)
    (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ) :
    s.DualTerminalCalibration sTail sZero k Lmax Nsave decay where
  productExponent := T.productExponent
  zeroProductExponent := T.zeroProductExponent
  zeroProductExponent_nonneg := T.zeroProductExponent_nonneg
  zero_product_norm := T.zero_product_norm
  profileExponent := T.profileExponent
  maskExponent := T.maskExponent
  modulusExponent := T.modulusExponent
  tailAmplitude := T.tailProfileConstant
  zeroAmplitude := T.zeroAmplitude hB δ hδ
  zeroAmplitude_nonneg := T.zeroAmplitude_nonneg hB δ hδ
  windows := T.windows
  exponent_bound := T.exponent_bound
  cutoff_eq := T.cutoff_eq
  zero_normalization := T.zero_normalization hB δ hδ

theorem normalizedFirstDualZero_of_original_le
    (T : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sTail sZero k Z X normBound Lmax Nsave decay)
    (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (ε Czero terminalExponent : ℝ) (hC : 0 ≤ Czero)
    (hledger : T.zeroExponent δ + T.zeroProductExponent * ε - (a.m + a.q) ≤ terminalExponent) :
    ((s.fiber : ℝ) * Czero * (s.originalDualTerminalCalibration T hB δ hδ).zeroAmplitude *
        Z ^ ((s.originalDualTerminalCalibration T hB δ hδ).zeroProductExponent * ε)) /
        Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant * Z ^ terminalExponent := by
  sorry

theorem normalizedFirstDualTail_of_original_le
    (T : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sTail sZero k Z X normBound Lmax Nsave decay)
    (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (Cerror terminalExponent : ℝ) (hC : 0 ≤ Cerror)
    (hledger : -Nsave - (a.m + a.q) ≤ terminalExponent) :
    ((s.fiber : ℝ) * Cerror * (s.originalDualTerminalCalibration T hB δ hδ).tailAmplitude *
        Z ^ (-Nsave)) / Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ terminalExponent := by
  sorry

end ActualFirstSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstDualOriginalWindows.zero_normalization
#print axioms HeckeSkeleton.Moments.EngineStep.FirstDualOriginalWindows.withZeroProduct
#print axioms HeckeSkeleton.Moments.EngineStep.FirstDualOriginalWindows.withZeroInverseRadius
#print axioms HeckeSkeleton.Moments.EngineStep.FirstDualOriginalWindows.tailMass_bound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.originalDualTerminalCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.normalizedFirstDualZero_of_original_le
