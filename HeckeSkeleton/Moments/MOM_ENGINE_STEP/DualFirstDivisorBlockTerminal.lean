import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstBlockFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorBlockTerminal

/-!
# Pure-dual terminals on the original first common block

The first-divisor windows refer to the same original left and right
sources for every actual divisor and finite character. Their pure-dual
calibrations contain no condition that the original row profile vanish
at the origin. Each side allowance cancels its actual power before the
original first Fourier mass and common-support scalar are applied.

The public scalar identities and coefficient definitions are reused.
The original `1 / Norm S`, `τ(D²)^k`, amplifier tuple counts, and both
finite phase and Möbius weights remain literal. The whole-block bounds
sum the proved class estimates on precisely their original carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory
open UniqueFactorizationMonoid

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
variable {K : Type} [Field K] [NumberField K]

private theorem dual_first_allowance_power_cancel
    (Z allowance loss eps coefficient : ℝ) (hZ : 0 < Z) :
    (coefficient * Z ^ (allowance + loss - eps + eps)) / Z ^ allowance =
      coefficient * Z ^ loss := by
  rw [show allowance + loss - eps + eps = allowance + loss by ring]
  calc
    _ = coefficient * (Z ^ (allowance + loss) / Z ^ allowance) := by ring
    _ = _ := by
      rw [← Real.rpow_sub hZ]
      congr 2
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
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace ActualPoolStages.DualFirstDivisorWindows

variable {ι : Type*} {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {S : Ideal (𝓞 K)} {slots k : ℕ} {B Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}
variable (T : s.DualFirstDivisorWindows S slots B sTail sZero k Lmax Nsave decay)

theorem zeroBudget_div_allowance_le_original_profiles
    (D : Ideal (𝓞 K)) (Q : T.OriginalTupleMultiplicities D)
    (ε Czero profileConstant allowance loss Mmax : ℝ) (fiberCap maskCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (hmask : ∀ b, (s.tag b).mask.card ≤ maskCap)
    (hraw : ∀ b, (T.profile b).zeroProfileConstant ≤ profileConstant * poolTagNormCharge P b)
    (hbudget : ∀ b, T.zeroExponent b + (T.profile b).productExponent * ε ≤
      allowance + loss - eps) :
    T.calibration.zeroBudget ε Czero / Z ^ allowance ≤
      (firstDivisorZeroCoefficient ell Mmax B Czero profileConstant slots k fiberCap maskCap D /
        (Ideal.absNorm S : ℝ)) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hp := T.zeroBudget_le_original_profiles D Q ε Czero profileConstant
    (allowance + loss - eps) Mmax fiberCap maskCap hC hprofile hrow hlarge hfiber hmask
    hraw hbudget
  apply (div_le_div_of_nonneg_right hp (Real.rpow_nonneg hz.le allowance)).trans_eq
  have heq : poolTerminalConstant K ell Mmax *
      ((fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) * Czero *
        (B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ))) =
      firstDivisorZeroCoefficient ell Mmax B Czero profileConstant slots k fiberCap maskCap D /
        (Ideal.absNorm S : ℝ) := by unfold firstDivisorZeroCoefficient; ring
  rw [heq]
  exact dual_first_allowance_power_cancel Z allowance loss eps _ hz

theorem tailBudget_div_allowance_le_original_profiles
    (D : Ideal (𝓞 K)) (Q : T.OriginalTupleMultiplicities D)
    (Cerror profileConstant allowance loss Mmax : ℝ) (fiberCap : ℕ)
    (profileExponent : PoolSourceTag P → ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (hraw : ∀ b, (T.profile b).tailProfileConstant ≤
      profileConstant * poolTagNormCharge P b * Z ^ profileExponent b)
    (hbudget : ∀ b, profileExponent b - Nsave ≤ allowance + loss - eps) :
    T.calibration.tailBudget Cerror / Z ^ allowance ≤
      (firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slots k fiberCap D /
        (Ideal.absNorm S : ℝ)) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hp := T.tailBudget_le_original_profiles D Q Cerror profileConstant
    (allowance + loss - eps) Mmax fiberCap profileExponent hC hprofile hrow hlarge hfiber
    hraw hbudget
  apply (div_le_div_of_nonneg_right hp (Real.rpow_nonneg hz.le allowance)).trans_eq
  have heq : poolTerminalConstant K ell Mmax *
      ((fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) * Cerror *
        (B ^ slots * profileConstant / (Ideal.absNorm S : ℝ))) =
      firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slots k fiberCap D /
        (Ideal.absNorm S : ℝ) := by unfold firstDivisorTailCoefficient; ring
  rw [heq]
  exact dual_first_allowance_power_cancel Z allowance loss eps _ hz

end ActualPoolStages.DualFirstDivisorWindows

local instance dualFirstDivisorBlockTerminalCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace FirstBlockPoolData.SecondStages

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {mask : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P mask X hX}
variable (s : p.SecondStages (E := E) (hDiff := hDiff))

/-- All fields are primitive coefficient atoms and residual-profile
windows on the actual original `S, χ` carriers. -/
structure DualFirstDivisorWindows (slotsL slotsR : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  left : ∀ S χ, (s.left S χ).DualFirstDivisorWindows S.val slotsL B sTail sZero k Lmax Nsave decay
  right : ∀ S χ, (s.right S χ).DualFirstDivisorWindows S.val slotsR B sTail sZero k Lmax Nsave decay

namespace DualFirstDivisorWindows

variable {s} {slotsL slotsR k : ℕ} {B Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}
variable (T : s.DualFirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay)

def calibration : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay where
  left S χ := (T.left S χ).calibration
  right S χ := (T.right S χ).calibration

/-- These are the original per-tag zero-profile windows and exact
tuple metadata.  No resulting zero amplitude or budget is a field. -/
structure ZeroWindows
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (ε total loss profileL profileR Mmax : ℝ) (fiberCap maskCap : ℕ) : Prop where
  left_tuples : (T.left S χ).OriginalTupleMultiplicities DE.1
  right_tuples : (T.right S χ).OriginalTupleMultiplicities DE.2
  left_row : (p.divisorPools.leftData S).rowExponent ≤ Mmax
  right_row : (p.divisorPools.rightData S).rowExponent ≤ Mmax
  left_large : 2 * ((p.divisorPools.leftData S).rowExponent / (ell / 2) +
    (p.divisorPools.leftData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)
  right_large : 2 * ((p.divisorPools.rightData S).rowExponent / (ell / 2) +
    (p.divisorPools.rightData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)
  left_fiber : ∀ b, ((s.left S χ).tag b).fiber ≤ fiberCap
  right_fiber : ∀ b, ((s.right S χ).tag b).fiber ≤ fiberCap
  left_mask : ∀ b, ((s.left S χ).tag b).mask.card ≤ maskCap
  right_mask : ∀ b, ((s.right S χ).tag b).mask.card ≤ maskCap
  left_profile : ∀ b, ((T.left S χ).profile b).zeroProfileConstant ≤
    profileL * poolTagNormCharge P b
  right_profile : ∀ b, ((T.right S χ).profile b).zeroProfileConstant ≤
    profileR * poolTagNormCharge P b
  left_ledger : ∀ b, (T.left S χ).zeroExponent b +
    ((T.left S χ).profile b).productExponent * ε ≤
      (total - idealLogLength Z DE.1 +
        firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - eps
  right_ledger : ∀ b, (T.right S χ).zeroExponent b +
    ((T.right S χ).profile b).productExponent * ε ≤
      (total - idealLogLength Z DE.2 +
        firstAllowance (idealLogLength Z DE.2) (idealLogLength Z DE.1)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - eps

/-- The canonical original `S, χ` zero class has its first-divisor
density proved from frozen atoms.  The original first allowance and
Fourier normalizations are discharged internally. -/
theorem classZeroBudget_le_original_profiles
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (ε Czero total parentWidth loss firstAmplitude profileL profileR Mmax : ℝ)
    (fiberCap maskCap : ℕ)
    (U : T.ZeroWindows S χ ε total loss profileL profileR Mmax fiberCap maskCap)
    (hC : 0 ≤ Czero) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total)) :
    T.calibration.classZeroBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) ε Czero S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        ((firstDivisorZeroCoefficient ell Mmax B Czero profileL slotsL k fiberCap maskCap DE.1 +
          firstDivisorZeroCoefficient ell Mmax B Czero profileR slotsR k fiberCap maskCap DE.2) / 2)) *
        (firstCommonWeight Z DE.1 DE.2 * (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hB : 0 ≤ B := zero_le_one.trans ((T.left S χ).atoms (.inl ())).bound_ge_one
  have hpool : 0 ≤ poolTerminalConstant K ell Mmax :=
    (poolTerminalConstant_pos (K := K) ell Mmax P.exponent_pos
      ((p.divisorPools.leftData S).rowExponent_nonneg.trans U.left_row)).le
  have hCL : 0 ≤ firstDivisorZeroCoefficient ell Mmax B Czero profileL
      slotsL k fiberCap maskCap DE.1 := by unfold firstDivisorZeroCoefficient; positivity
  have hCR : 0 ≤ firstDivisorZeroCoefficient ell Mmax B Czero profileR
      slotsR k fiberCap maskCap DE.2 := by unfold firstDivisorZeroCoefficient; positivity
  have hL := (T.left S χ).zeroBudget_div_allowance_le_original_profiles DE.1
    U.left_tuples ε Czero profileL _ loss Mmax fiberCap maskCap hC hprofileL
    U.left_row U.left_large U.left_fiber U.left_mask U.left_profile U.left_ledger
  have hR := (T.right S χ).zeroBudget_div_allowance_le_original_profiles DE.2
    U.right_tuples ε Czero profileR _ loss Mmax fiberCap maskCap hC hprofileR
    U.right_row U.right_large U.right_fiber U.right_mask U.right_profile U.right_ledger
  have hc := original_terminal_class_scalar Z parentWidth
    (firstLeftAllowance Z total DE.1 DE.2) (firstRightAllowance Z total DE.1 DE.2)
    p.rowBound ‖(moebius S.val : ℂ)‖
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖
    ((actualFourierMeasure chart.kernel).real Set.univ) (firstTerminalFourierCost chart.kernel)
    ((T.left S χ).calibration.zeroBudget ε Czero) ((T.right S χ).calibration.zeroBudget ε Czero)
    _ _ (Ideal.absNorm S.val : ℝ) loss firstAmplitude (firstCommonWeight Z DE.1 DE.2)
    hz (firstLeftAllowance_pos Z total hz _ _) (firstRightAllowance_pos Z total hz _ _)
    p.rowBound_nonneg (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg
    (firstTerminalFourierCost_nonneg chart.kernel) hCL hCR (Nat.cast_nonneg _) hL hR
    (firstTerminalFourierCost_bound chart.kernel)
    (p.normalized_allowance_prefactor P.base_gt_one total parentWidth firstAmplitude hfirst)
  simpa only [calibration, DualTerminalCalibration.classZeroBudget, classWeight] using hc

/-- Tail windows retain the actual residual-profile exponents.  The
decay ledger is numerical, after the exact original tuple calibration. -/
structure TailWindows
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (total loss profileL profileR Mmax : ℝ) (fiberCap : ℕ)
    (exponentL exponentR : PoolSourceTag P → ℝ) : Prop where
  left_tuples : (T.left S χ).OriginalTupleMultiplicities DE.1
  right_tuples : (T.right S χ).OriginalTupleMultiplicities DE.2
  left_row : (p.divisorPools.leftData S).rowExponent ≤ Mmax
  right_row : (p.divisorPools.rightData S).rowExponent ≤ Mmax
  left_large : 2 * ((p.divisorPools.leftData S).rowExponent / (ell / 2) +
    (p.divisorPools.leftData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)
  right_large : 2 * ((p.divisorPools.rightData S).rowExponent / (ell / 2) +
    (p.divisorPools.rightData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)
  left_fiber : ∀ b, ((s.left S χ).tag b).fiber ≤ fiberCap
  right_fiber : ∀ b, ((s.right S χ).tag b).fiber ≤ fiberCap
  left_profile : ∀ b, ((T.left S χ).profile b).tailProfileConstant ≤
    profileL * poolTagNormCharge P b * Z ^ exponentL b
  right_profile : ∀ b, ((T.right S χ).profile b).tailProfileConstant ≤
    profileR * poolTagNormCharge P b * Z ^ exponentR b
  left_ledger : ∀ b, exponentL b - Nsave ≤
    (total - idealLogLength Z DE.1 +
      firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - eps
  right_ledger : ∀ b, exponentR b - Nsave ≤
    (total - idealLogLength Z DE.2 +
      firstAllowance (idealLogLength Z DE.2) (idealLogLength Z DE.1)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - eps

theorem classTailBudget_le_original_profiles
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (Cerror total parentWidth loss firstAmplitude profileL profileR Mmax : ℝ)
    (fiberCap : ℕ) (exponentL exponentR : PoolSourceTag P → ℝ)
    (U : T.TailWindows S χ total loss profileL profileR Mmax fiberCap exponentL exponentR)
    (hC : 0 ≤ Cerror) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total)) :
    T.calibration.classTailBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) Cerror S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        ((firstDivisorTailCoefficient ell Mmax B Cerror profileL slotsL k fiberCap DE.1 +
          firstDivisorTailCoefficient ell Mmax B Cerror profileR slotsR k fiberCap DE.2) / 2)) *
        (firstCommonWeight Z DE.1 DE.2 * (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
          ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hB : 0 ≤ B := zero_le_one.trans ((T.left S χ).atoms (.inl ())).bound_ge_one
  have hpool : 0 ≤ poolTerminalConstant K ell Mmax :=
    (poolTerminalConstant_pos (K := K) ell Mmax P.exponent_pos
      ((p.divisorPools.leftData S).rowExponent_nonneg.trans U.left_row)).le
  have hCL : 0 ≤ firstDivisorTailCoefficient ell Mmax B Cerror profileL
      slotsL k fiberCap DE.1 := by unfold firstDivisorTailCoefficient; positivity
  have hCR : 0 ≤ firstDivisorTailCoefficient ell Mmax B Cerror profileR
      slotsR k fiberCap DE.2 := by unfold firstDivisorTailCoefficient; positivity
  have hL := (T.left S χ).tailBudget_div_allowance_le_original_profiles DE.1
    U.left_tuples Cerror profileL _ loss Mmax fiberCap exponentL hC hprofileL
    U.left_row U.left_large U.left_fiber U.left_profile U.left_ledger
  have hR := (T.right S χ).tailBudget_div_allowance_le_original_profiles DE.2
    U.right_tuples Cerror profileR _ loss Mmax fiberCap exponentR hC hprofileR
    U.right_row U.right_large U.right_fiber U.right_profile U.right_ledger
  have hc := original_terminal_class_scalar Z parentWidth
    (firstLeftAllowance Z total DE.1 DE.2) (firstRightAllowance Z total DE.1 DE.2)
    p.rowBound ‖(moebius S.val : ℂ)‖
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖
    ((actualFourierMeasure chart.kernel).real Set.univ) (firstTerminalFourierCost chart.kernel)
    ((T.left S χ).calibration.tailBudget Cerror) ((T.right S χ).calibration.tailBudget Cerror)
    _ _ (Ideal.absNorm S.val : ℝ) loss firstAmplitude (firstCommonWeight Z DE.1 DE.2)
    hz (firstLeftAllowance_pos Z total hz _ _) (firstRightAllowance_pos Z total hz _ _)
    p.rowBound_nonneg (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg
    (firstTerminalFourierCost_nonneg chart.kernel) hCL hCR (Nat.cast_nonneg _) hL hR
    (firstTerminalFourierCost_bound chart.kernel)
    (p.normalized_allowance_prefactor P.base_gt_one total parentWidth firstAmplitude hfirst)
  simpa only [calibration, DualTerminalCalibration.classTailBudget, classWeight] using hc

/-- The complete original divisor-and-character sum has the proved
zero-class scalar. The common and Möbius harmonic weights remain on
their actual carrier for the subsequent first-label estimate. -/
theorem zeroBudget_le_original_label_sum
    (ε Czero total parentWidth loss firstAmplitude profileL profileR Mmax : ℝ)
    (fiberCap maskCap : ℕ)
    (U : ∀ S χ, T.ZeroWindows S χ ε total loss profileL profileR Mmax fiberCap maskCap)
    (hC : 0 ≤ Czero) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total)) :
    T.calibration.zeroBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) ε Czero / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        ((firstDivisorZeroCoefficient ell Mmax B Czero profileL slotsL k fiberCap maskCap DE.1 +
          firstDivisorZeroCoefficient ell Mmax B Czero profileR slotsR k fiberCap maskCap DE.2) / 2)) *
        (∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val),
          ∑ χ : (PUnit × PUnit) →* Circle,
            firstCommonWeight Z DE.1 DE.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  simp only [DualTerminalCalibration.zeroBudget, Finset.sum_div]
  calc
    _ ≤ ∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          (firstAmplitude * firstTerminalFourierCost chart.kernel *
            ((firstDivisorZeroCoefficient ell Mmax B Czero profileL slotsL k fiberCap maskCap DE.1 +
              firstDivisorZeroCoefficient ell Mmax B Czero profileR slotsR k fiberCap maskCap DE.2) / 2)) *
            (firstCommonWeight Z DE.1 DE.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
      apply Finset.sum_le_sum
      intro S _
      apply Finset.sum_le_sum
      intro χ _
      exact T.classZeroBudget_le_original_profiles S χ ε Czero total parentWidth loss
        firstAmplitude profileL profileR Mmax fiberCap maskCap (U S χ)
        hC hprofileL hprofileR hfirst
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

/-- The complete tail uses the same first labels, original Fourier
kernel and two side allowances as the zero term. -/
theorem tailBudget_le_original_label_sum
    (Cerror total parentWidth loss firstAmplitude profileL profileR Mmax : ℝ)
    (fiberCap : ℕ) (exponentL exponentR : PoolSourceTag P → ℝ)
    (U : ∀ S χ, T.TailWindows S χ total loss profileL profileR Mmax
      fiberCap exponentL exponentR)
    (hC : 0 ≤ Cerror) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total)) :
    T.calibration.tailBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) Cerror / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        ((firstDivisorTailCoefficient ell Mmax B Cerror profileL slotsL k fiberCap DE.1 +
          firstDivisorTailCoefficient ell Mmax B Cerror profileR slotsR k fiberCap DE.2) / 2)) *
        (∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val),
          ∑ χ : (PUnit × PUnit) →* Circle,
            firstCommonWeight Z DE.1 DE.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  simp only [DualTerminalCalibration.tailBudget, Finset.sum_div]
  calc
    _ ≤ ∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          (firstAmplitude * firstTerminalFourierCost chart.kernel *
            ((firstDivisorTailCoefficient ell Mmax B Cerror profileL slotsL k fiberCap DE.1 +
              firstDivisorTailCoefficient ell Mmax B Cerror profileR slotsR k fiberCap DE.2) / 2)) *
            (firstCommonWeight Z DE.1 DE.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
      apply Finset.sum_le_sum
      intro S _
      apply Finset.sum_le_sum
      intro χ _
      exact T.classTailBudget_le_original_profiles S χ Cerror total parentWidth loss
        firstAmplitude profileL profileR Mmax fiberCap exponentL exponentR (U S χ)
        hC hprofileL hprofileR hfirst
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

end DualFirstDivisorWindows
end FirstBlockPoolData.SecondStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualFirstDivisorWindows.zeroBudget_div_allowance_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualFirstDivisorWindows.tailBudget_div_allowance_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualFirstDivisorWindows.classZeroBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualFirstDivisorWindows.classTailBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualFirstDivisorWindows.zeroBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualFirstDivisorWindows.tailBudget_le_original_label_sum
