import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroMaskSubpower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedSourceBudgets

/-!
# The original first zero and tail calibrations are constructed

The first zero amplitude is computed from the original individual
profile seminorm, original inverse radius and the genuine transformed
first mask.  Its small-power cost follows from the original prime
dictionary and original column norms.  Neither a zero amplitude bound
nor a whole terminal normalization is an input.

The proof is on the original source with no prime pool.  An amplified
source uses precisely the same construction through `directEntrance`,
which preserves all original columns, profiles, masks and fibres.
Thus the argument is independent of the number of slots and does not
introduce an auxiliary positive pool at the direct entrance.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments MeasureTheory

variable {K : Type} [Field K] [NumberField K]

/-- This constant is selected before every moving original source. -/
def originalFirstMaskConstant (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) : ℝ :=
  Classical.choose (first_block_mask_labels_subpower (K := K) B δ hB hδ)

theorem originalFirstMaskConstant_pos (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    0 < originalFirstMaskConstant (K := K) B δ hB hδ :=
  (Classical.choose_spec (first_block_mask_labels_subpower (K := K) B δ hB hδ)).1

theorem originalFirstMaskConstant_bound (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (Z : ℝ) (hZ : 1 ≤ Z) {A : SArithmeticData K} {ι κ : Type*}
    {I : ι → A.Exterior} {J : κ → A.Exterior} {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock I J DE)
    (M : Finset (HeightOneSpectrum A.R)) (R : Ideal (𝓞 K)) (hR : R ≠ 0)
    (hNR : (Ideal.absNorm R : ℝ) ≤ Z ^ B) (hND : (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B)
    (W : OriginalMaskPrimeData M R) :
    ((b.mask M).powerset.card : ℝ) ≤ originalFirstMaskConstant (K := K) B δ hB hδ * Z ^ δ :=
  (Classical.choose_spec (first_block_mask_labels_subpower (K := K) B δ hB hδ)).2
    Z hZ b M R hR hNR hND W

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ} {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters} {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)

/-- All hypotheses concern original individual profiles, original
ideal coordinates or original prime/generator data.  The whole-factor
injection and tail windows are the literal original first ones. -/
structure OriginalTerminalWindows (normBound : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  productExponent : ℝ
  profileExponent : ℝ
  maskExponent : ℝ
  modulusExponent : ℝ
  tailProfileConstant : ℝ
  zeroProfileConstant : ℝ
  zeroProfileConstant_nonneg : 0 ≤ zeroProfileConstant
  zeroProfileExponent : ℝ
  windows : FirstTailWindows hΓ C s.columns s.columns s.ideal s.ideal s.block
    sTail s.profiles s.radius s.mask k Z productExponent profileExponent maskExponent
    modulusExponent tailProfileConstant
  exponent_bound : firstTailExponent k productExponent profileExponent maskExponent
    modulusExponent ≤ Lmax
  cutoff_eq : X = Z ^ firstTailCutoffExponent Lmax Nsave decay
  profile_zero : ∀ i ∈ s.columns, ∀ j ∈ s.columns, s.profiles i j 0 = 0
  zero_profile : ∀ v ∈ firstZeroPairs s.columns s.columns s.ideal s.ideal,
    sZero.sup (schwartzSeminormFamily ℂ V ℂ) (s.profiles v.2.1 v.2.2) ≤
      zeroProfileConstant * Z ^ zeroProfileExponent
  maskIdeal : Ideal (𝓞 K)
  mask_ne_zero : maskIdeal ≠ 0
  mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBound
  original_mask : OriginalMaskPrimeData s.mask maskIdeal
  column_norm : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ normBound

namespace OriginalTerminalWindows

variable {s} {normBound : ℝ} {sTail sZero : Finset (ℕ × ℕ)}
variable {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.OriginalTerminalWindows normBound sTail sZero k Lmax Nsave decay)
variable (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)

def zeroExponent : ℝ :=
  T.zeroProfileExponent + T.modulusExponent + δ + T.productExponent / 2

def zeroAmplitude : ℝ :=
  originalFirstMaskConstant (K := K) normBound δ hB hδ *
    T.zeroProfileConstant * Z ^ T.zeroExponent δ

theorem zeroAmplitude_nonneg : 0 ≤ T.zeroAmplitude hB δ hδ := by
  exact mul_nonneg
    (mul_nonneg (originalFirstMaskConstant_pos (K := K) normBound δ hB hδ).le
      T.zeroProfileConstant_nonneg)
    (Real.rpow_nonneg (zero_le_one.trans T.windows.base_ge_one) _)

theorem zero_normalization :
    ∀ v ∈ firstZeroPairs s.columns s.columns s.ideal s.ideal,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (s.profiles v.2.1 v.2.2) *
        (∑ D ∈ ((s.block v.1).mask s.mask).powerset, firstZeroDivisorWeight s.radius D) ≤
          T.zeroAmplitude hB δ hδ / Real.sqrt (Z ^ T.productExponent) := by
  intro v hv
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  have hcommon := actualCommonLabels_norm s.columns s.columns _ _
    (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1)
    (Z ^ normBound) T.column_norm T.column_norm (v.1.val, ∅)
    ((mem_actualCommonLabels _ _ _ _ _).mpr ⟨v.1.property, Finset.empty_subset _⟩)
  have hcard := originalFirstMaskConstant_bound normBound δ hB hδ Z T.windows.base_ge_one
    (s.block v.1) s.mask T.maskIdeal T.mask_ne_zero T.mask_norm hcommon.1 T.original_mask
  have hmask := (firstZeroDivisorSum_le_card s.radius ((s.block v.1).mask s.mask)).trans
    (mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr s.radius.property.le))
  have hmask' := hmask.trans
    (mul_le_mul_of_nonneg_left T.windows.inverse_radius
      (mul_nonneg (originalFirstMaskConstant_pos (K := K) normBound δ hB hδ).le
        (Real.rpow_nonneg hz.le _)))
  have hp := mul_le_mul (T.zero_profile v hv) hmask'
    (Finset.sum_nonneg fun D _ => firstZeroDivisorWeight_nonneg s.radius D)
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

/-- The first terminal calibration is a computed result of the raw
windows.  Its scalar zero-normalization is proved above. -/
def calibration : s.TerminalCalibration sTail sZero k Lmax Nsave decay where
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
  profile_zero := T.profile_zero
  zero_normalization := T.zero_normalization hB δ hδ

/-- This is the literal first-zero quantity in parent normalization.
The only final step is the original numerical exponent ledger. -/
theorem normalized_first_zero_le (ε Czero terminalExponent : ℝ) (hC : 0 ≤ Czero)
    (hledger : T.zeroExponent δ + T.productExponent * ε - (a.m + a.q) ≤ terminalExponent) :
    ((s.fiber : ℝ) * Czero * (T.calibration hB δ hδ).zeroAmplitude *
        Z ^ ((T.calibration hB δ hδ).productExponent * ε)) / Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant * Z ^ terminalExponent := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  change ((s.fiber : ℝ) * Czero * T.zeroAmplitude hB δ hδ *
    Z ^ (T.productExponent * ε)) / Z ^ (a.m + a.q) ≤ _
  calc
    _ = ((s.fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant) *
          Z ^ (T.zeroExponent δ + T.productExponent * ε - (a.m + a.q)) := by
      unfold zeroAmplitude
      rw [Real.rpow_sub hz, Real.rpow_add hz]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le T.windows.base_ge_one hledger)
      (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
        (originalFirstMaskConstant_pos (K := K) normBound δ hB hδ).le) T.zeroProfileConstant_nonneg)

/-- The first tail uses the same constructed calibration and literal
original profile constant.  No amplitude estimate is assumed. -/
theorem normalized_first_tail_le (Cerror terminalExponent : ℝ) (hC : 0 ≤ Cerror)
    (hledger : -Nsave - (a.m + a.q) ≤ terminalExponent) :
    ((s.fiber : ℝ) * Cerror * (T.calibration hB δ hδ).tailAmplitude * Z ^ (-Nsave)) /
        Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ terminalExponent := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  change ((s.fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ (-Nsave)) /
    Z ^ (a.m + a.q) ≤ _
  rw [mul_div_assoc, ← Real.rpow_sub hz]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le T.windows.base_ge_one hledger)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) T.windows.amplitude_nonneg)

end OriginalTerminalWindows
end ActualDirectFirstSource

namespace ActualFirstSource

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable (s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
variable {normBound : ℝ} {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.directEntrance.OriginalTerminalWindows normBound sTail sZero k Lmax Nsave decay)
variable (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)

/-- Both entrances have literally the same original profiles and
masks.  This only transports the already constructed first calibration. -/
def originalTerminalCalibration : s.TerminalCalibration sTail sZero k Lmax Nsave decay where
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
  profile_zero := T.profile_zero
  zero_normalization := T.zero_normalization hB δ hδ

theorem normalizedFirstZeroBudget_of_original_le
    (ε Czero terminalExponent : ℝ) (hC : 0 ≤ Czero)
    (hledger : T.zeroExponent δ + T.productExponent * ε - (a.m + a.q) ≤ terminalExponent) :
    SecondStages.normalizedFirstZeroBudget (s.originalTerminalCalibration T hB δ hδ) ε Czero ≤
      (s.fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant * Z ^ terminalExponent :=
  T.normalized_first_zero_le hB δ hδ ε Czero terminalExponent hC hledger

theorem normalizedFirstTailBudget_of_original_le
    (Cerror terminalExponent : ℝ) (hC : 0 ≤ Cerror)
    (hledger : -Nsave - (a.m + a.q) ≤ terminalExponent) :
    ((s.fiber : ℝ) * Cerror * (s.originalTerminalCalibration T hB δ hδ).tailAmplitude *
        Z ^ (-Nsave)) / Z ^ (a.m + a.q) ≤
      (s.fiber : ℝ) * Cerror * T.tailProfileConstant * Z ^ terminalExponent :=
  T.normalized_first_tail_le hB δ hδ Cerror terminalExponent hC hledger

end ActualFirstSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.OriginalTerminalWindows.calibration
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.OriginalTerminalWindows.normalized_first_zero_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.normalizedFirstZeroBudget_of_original_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.normalizedFirstTailBudget_of_original_le
