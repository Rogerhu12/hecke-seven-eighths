import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedPoolTerminalPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstBlockFiniteLeaves

set_option linter.unusedSectionVars false

/-!
# Original first allowances after the same one-pool sharp calibration

The first profile and original second numerator combine before any
uniform estimate. The actual main and 1/6/7 tags have already paid one
pool density. This class estimate retains the original first divisor,
finite character, Fourier kernel and both Cauchy allowances.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

local instance combinedPoolSecondTerminalCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstBlockPoolData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {mask : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P mask X hX}

namespace SecondStages.DualTerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)

/-- The inputs describe the two individual original amplitudes and
the actual tuple fibres. The scalar estimate for the full pooled zero class
is proved here after the central degree cancels. -/
theorem classZeroBudget_le_combined_profiles
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (ε Czero total parentWidth loss shift firstAmplitude profileL profileR
      Mmax : ℝ) (exponentL exponentR : PoolSourceTag P → ℝ) (fiberCap tupleL tupleR : ℕ)
    (hC : 0 ≤ Czero) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hleftRow : (p.divisorPools.leftData S).rowExponent ≤ Mmax)
    (hrightRow : (p.divisorPools.rightData S).rowExponent ≤ Mmax)
    (hleftLarge : 2 * ((p.divisorPools.leftData S).rowExponent / (ell / 2) +
      (p.divisorPools.leftData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hrightLarge : 2 * ((p.divisorPools.rightData S).rowExponent / (ell / 2) +
      (p.divisorPools.rightData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hleftFiber : ∀ tag, ((s.left S χ).tag tag).fiber ≤ fiberCap)
    (hrightFiber : ∀ tag, ((s.right S χ).tag tag).fiber ≤ fiberCap)
    (hleftTuples : ∀ tag, ((T.left S χ).tag tag).windows.multiplicity ≤ tupleL)
    (hrightTuples : ∀ tag, ((T.right S χ).tag tag).windows.multiplicity ≤ tupleR)
    (hleftProfile : ∀ tag, ((s.left S χ).tag tag).fiber ≠ 0 → ((T.left S χ).tag tag).zeroAmplitude ≤
      (profileL * poolTagNormCharge P tag / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentL tag)
    (hrightProfile : ∀ tag, ((s.right S χ).tag tag).fiber ≠ 0 → ((T.right S χ).tag tag).zeroAmplitude ≤
      (profileR * poolTagNormCharge P tag / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentR tag)
    (hleftExponent : ∀ tag, ((s.left S χ).tag tag).fiber ≠ 0 → exponentL tag + ((T.left S χ).tag tag).zeroProductExponent * ε ≤
      (total - idealLogLength Z DE.1 + firstAllowance
        (idealLogLength Z DE.1) (idealLogLength Z DE.2)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - shift - eps)
    (hrightExponent : ∀ tag, ((s.right S χ).tag tag).fiber ≠ 0 → exponentR tag + ((T.right S χ).tag tag).zeroProductExponent * ε ≤
      (total - idealLogLength Z DE.2 + firstAllowance
        (idealLogLength Z DE.2) (idealLogLength Z DE.1)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - shift - eps)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total + shift)) :
    T.classZeroBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) ε Czero S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        ((poolTerminalConstant K ell Mmax * ((fiberCap : ℝ) * Czero * (tupleL : ℝ) * profileL) +
          poolTerminalConstant K ell Mmax * ((fiberCap : ℝ) * Czero * (tupleR : ℝ) * profileR)) / 2)) *
        (firstCommonWeight Z DE.1 DE.2 *
          (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
            ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  sorry

/-- The same pooled source, divisor and Fourier mass are used for
the tail. The uniform cutoff saving is combined with the actual
coefficient degree before the original first profile is paid. -/
theorem classTailBudget_le_combined_profiles
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (Cerror total parentWidth loss shift firstAmplitude profileL profileR
      Mmax : ℝ) (exponentL exponentR : PoolSourceTag P → ℝ) (fiberCap tupleL tupleR : ℕ)
    (hC : 0 ≤ Cerror) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hleftRow : (p.divisorPools.leftData S).rowExponent ≤ Mmax)
    (hrightRow : (p.divisorPools.rightData S).rowExponent ≤ Mmax)
    (hleftLarge : 2 * ((p.divisorPools.leftData S).rowExponent / (ell / 2) +
      (p.divisorPools.leftData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hrightLarge : 2 * ((p.divisorPools.rightData S).rowExponent / (ell / 2) +
      (p.divisorPools.rightData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hleftFiber : ∀ tag, ((s.left S χ).tag tag).fiber ≤ fiberCap)
    (hrightFiber : ∀ tag, ((s.right S χ).tag tag).fiber ≤ fiberCap)
    (hleftTuples : ∀ tag, ((T.left S χ).tag tag).windows.multiplicity ≤ tupleL)
    (hrightTuples : ∀ tag, ((T.right S χ).tag tag).windows.multiplicity ≤ tupleR)
    (hleftProfile : ∀ tag, ((s.left S χ).tag tag).fiber ≠ 0 → ((T.left S χ).tag tag).tailAmplitude ≤
      (profileL * poolTagNormCharge P tag / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentL tag)
    (hrightProfile : ∀ tag, ((s.right S χ).tag tag).fiber ≠ 0 → ((T.right S χ).tag tag).tailAmplitude ≤
      (profileR * poolTagNormCharge P tag / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentR tag)
    (hleftExponent : ∀ tag, ((s.left S χ).tag tag).fiber ≠ 0 → exponentL tag - Nsave ≤
      (total - idealLogLength Z DE.1 + firstAllowance
        (idealLogLength Z DE.1) (idealLogLength Z DE.2)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - shift - eps)
    (hrightExponent : ∀ tag, ((s.right S χ).tag tag).fiber ≠ 0 → exponentR tag - Nsave ≤
      (total - idealLogLength Z DE.2 + firstAllowance
        (idealLogLength Z DE.2) (idealLogLength Z DE.1)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - shift - eps)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total + shift)) :
    T.classTailBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) Cerror S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        ((poolTerminalConstant K ell Mmax * ((fiberCap : ℝ) * Cerror * (tupleL : ℝ) * profileL) +
          poolTerminalConstant K ell Mmax * ((fiberCap : ℝ) * Cerror * (tupleR : ℝ) * profileR)) / 2)) *
        (firstCommonWeight Z DE.1 DE.2 *
          (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
            ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  sorry

end SecondStages.DualTerminalCalibration
end FirstBlockPoolData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualTerminalCalibration.classZeroBudget_le_combined_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualTerminalCalibration.classTailBudget_le_combined_profiles
