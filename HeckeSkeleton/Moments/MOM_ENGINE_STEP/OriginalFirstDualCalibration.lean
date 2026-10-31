import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstTerminalCalibration

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
  profileExponent : ℝ
  maskExponent : ℝ
  modulusExponent : ℝ
  tailProfileConstant : ℝ
  zeroProfileConstant : ℝ
  zeroProfileConstant_nonneg : 0 ≤ zeroProfileConstant
  zeroProfileExponent : ℝ
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
  T.zeroProfileExponent + T.modulusExponent + δ + T.productExponent / 2

def zeroAmplitude (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  originalFirstMaskConstant (K := K) normBound δ hB hδ *
    T.zeroProfileConstant * Z ^ T.zeroExponent δ

theorem zeroAmplitude_nonneg (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ T.zeroAmplitude hB δ hδ := by
  exact mul_nonneg
    (mul_nonneg (originalFirstMaskConstant_pos (K := K) normBound δ hB hδ).le
      T.zeroProfileConstant_nonneg)
    (Real.rpow_nonneg (zero_le_one.trans T.windows.base_ge_one) _)

/-- The actual first mask-divisor sum is paid by the original prime
dictionary and original column norms. Its small-power constant is fixed
before this source. -/
theorem zero_normalization (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ) :
    ∀ v ∈ firstZeroPairs columns columns I I,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) ≤
          T.zeroAmplitude hB δ hδ / Real.sqrt (Z ^ T.productExponent) := by
  intro v hv
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  have hcommon := actualCommonLabels_norm columns columns _ _
    (fun i _ => (I i).property.1) (fun i _ => (I i).property.1)
    (Z ^ normBound) T.column_norm T.column_norm (v.1.val, ∅)
    ((mem_actualCommonLabels _ _ _ _ _).mpr ⟨v.1.property, Finset.empty_subset _⟩)
  have hcard := originalFirstMaskConstant_bound normBound δ hB hδ Z T.windows.base_ge_one
    (blocks v.1) M T.maskIdeal T.mask_ne_zero T.mask_norm hcommon.1 T.original_mask
  have hmask := (firstZeroDivisorSum_le_card radius ((blocks v.1).mask M)).trans
    (mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr radius.property.le))
  have hmask' := hmask.trans
    (mul_le_mul_of_nonneg_left T.windows.inverse_radius
      (mul_nonneg (originalFirstMaskConstant_pos (K := K) normBound δ hB hδ).le
        (Real.rpow_nonneg hz.le _)))
  have hp := mul_le_mul (T.zero_profile v hv) hmask'
    (Finset.sum_nonneg fun D _ => firstZeroDivisorWeight_nonneg radius D)
    (mul_nonneg T.zeroProfileConstant_nonneg (Real.rpow_nonneg hz.le _))
  apply hp.trans_eq
  have hsqrt : Real.sqrt (Z ^ T.productExponent) = Z ^ (T.productExponent / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]
    congr 1
    ring
  unfold zeroAmplitude zeroExponent
  rw [hsqrt, mul_div_assoc, ← Real.rpow_sub hz,
    show (T.zeroProfileExponent + T.modulusExponent + δ + T.productExponent / 2) -
      T.productExponent / 2 = T.zeroProfileExponent + T.modulusExponent + δ by ring,
    Real.rpow_add hz, Real.rpow_add hz]
  ring

/-- Both first terminal scalars are computed from the same original
profile windows, independently of any prime pool. -/
def cost (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (ε Cerror Czero : ℝ) : ℝ :=
  Czero * T.zeroAmplitude hB δ hδ * Z ^ (T.productExponent * ε) +
    Cerror * T.tailProfileConstant * Z ^ (-Nsave)

theorem tailMass_bound (hdecay : 1 < decay) (Ctail : ℝ) (hCtail : 0 ≤ Ctail) :
    Ctail * X ^ (1 - decay) *
      firstBlockTailMass hΓ C columns columns I I blocks sTail profiles radius M ≤
      (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) *
        T.tailProfileConstant * Z ^ (-Nsave) := by
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  let L := firstTailExponent k T.productExponent T.profileExponent T.maskExponent T.modulusExponent
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  have hw := T.windows.power_bound
  change firstBlockTailMass hΓ C columns columns I I blocks sTail profiles radius M ≤
    Cnum * T.tailProfileConstant * Z ^ L at hw
  have hX : 1 ≤ X := by
    rw [T.cutoff_eq]
    exact Real.one_le_rpow T.windows.base_ge_one
      (firstTailCutoffExponent_nonneg Lmax Nsave decay hdecay)
  calc
    _ ≤ Ctail * X ^ (1 - decay) * (Cnum * T.tailProfileConstant * Z ^ L) :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg hCtail (Real.rpow_nonneg (zero_le_one.trans hX) _))
    _ = (Ctail * Cnum) * T.tailProfileConstant * (X ^ (1 - decay) * Z ^ L) := by ring
    _ ≤ (Ctail * Cnum) * T.tailProfileConstant * Z ^ (-Nsave) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hCtail hCnum) T.windows.amplitude_nonneg)
      rw [T.cutoff_eq]
      exact first_tail_cutoff_power_of_le Z L Lmax Nsave decay
        T.windows.base_ge_one hdecay T.exponent_bound

/-- The normalized zero scalar retains the literal original parent
width. Only its explicit real exponent is compared at the final step. -/
theorem normalized_zero_le (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (fiber : ℕ) (parentWidth ε Czero terminalExponent : ℝ) (hC : 0 ≤ Czero)
    (hledger : T.zeroExponent δ + T.productExponent * ε - parentWidth ≤ terminalExponent) :
    ((fiber : ℝ) * Czero * T.zeroAmplitude hB δ hδ * Z ^ (T.productExponent * ε)) /
        Z ^ parentWidth ≤
      (fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant * Z ^ terminalExponent := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  calc
    _ = ((fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant) *
          Z ^ (T.zeroExponent δ + T.productExponent * ε - parentWidth) := by
      unfold zeroAmplitude
      rw [Real.rpow_sub hz, Real.rpow_add hz]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le T.windows.base_ge_one hledger)
      (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
        (originalFirstMaskConstant_pos (K := K) normBound δ hB hδ).le) T.zeroProfileConstant_nonneg)

theorem normalized_tail_le (fiber : ℕ) (parentWidth Cerror terminalExponent : ℝ)
    (hC : 0 ≤ Cerror) (hledger : -Nsave - parentWidth ≤ terminalExponent) :
    ((fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ (-Nsave)) / Z ^ parentWidth ≤
      (fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ terminalExponent := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  rw [mul_div_assoc, ← Real.rpow_sub hz]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le T.windows.base_ge_one hledger)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) T.windows.amplitude_nonneg)

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
    (hledger : T.zeroExponent δ + T.productExponent * ε - (a.m + a.q) ≤ terminalExponent) :
    ((s.fiber : ℝ) * Czero * (s.originalDualTerminalCalibration T hB δ hδ).zeroAmplitude *
        Z ^ ((s.originalDualTerminalCalibration T hB δ hδ).productExponent * ε)) /
        Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant * Z ^ terminalExponent :=
  T.normalized_zero_le hB δ hδ s.fiber (a.m + a.q) ε Czero terminalExponent hC hledger

theorem normalizedFirstDualTail_of_original_le
    (T : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sTail sZero k Z X normBound Lmax Nsave decay)
    (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (Cerror terminalExponent : ℝ) (hC : 0 ≤ Cerror)
    (hledger : -Nsave - (a.m + a.q) ≤ terminalExponent) :
    ((s.fiber : ℝ) * Cerror * (s.originalDualTerminalCalibration T hB δ hδ).tailAmplitude *
        Z ^ (-Nsave)) / Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ terminalExponent :=
  T.normalized_tail_le s.fiber (a.m + a.q) Cerror terminalExponent hC hledger

end ActualFirstSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstDualOriginalWindows.zero_normalization
#print axioms HeckeSkeleton.Moments.EngineStep.FirstDualOriginalWindows.tailMass_bound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.originalDualTerminalCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.normalizedFirstDualZero_of_original_le
