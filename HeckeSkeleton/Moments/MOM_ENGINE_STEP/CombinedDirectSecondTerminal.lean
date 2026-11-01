import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedDualTerminalPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectSecondTerminalAtoms

/-!
# Direct second terminals with the original central degree

These estimates use the actual direct dual calibrations, without a
residual-window wrapper. The positive power in the first row weight
is cancelled by the central decay in the same source coefficients.
The first divisor, the side allowances and the first Fourier kernel
are the original ones. No prime-pool object is present.
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

local instance combinedDirectSecondTerminalCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {mask : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart mask X hX}
variable {Z : ℝ}

namespace SecondStages.DualTerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)

/-- The inputs describe the two individual original amplitudes and
the actual tuple fibres. The scalar estimate for the full zero class
is proved here after the central degree cancels. -/
theorem classZeroBudget_le_combined_profiles
    (hZ : 1 < Z)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (ε Czero total parentWidth loss shift firstAmplitude profileL profileR
      exponentL exponentR : ℝ) (fiberCap tupleL tupleR : ℕ)
    (hC : 0 ≤ Czero) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hleftFiber : (s.left S χ).fiber ≤ fiberCap)
    (hrightFiber : (s.right S χ).fiber ≤ fiberCap)
    (hleftTuples : (T.left S χ).windows.multiplicity ≤ tupleL)
    (hrightTuples : (T.right S χ).windows.multiplicity ≤ tupleR)
    (hleftProfile : (s.left S χ).fiber ≠ 0 → (T.left S χ).zeroAmplitude ≤
      (profileL / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentL)
    (hrightProfile : (s.right S χ).fiber ≠ 0 → (T.right S χ).zeroAmplitude ≤
      (profileR / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentR)
    (hleftExponent : (s.left S χ).fiber ≠ 0 → exponentL + (T.left S χ).zeroProductExponent * ε ≤
      (total - idealLogLength Z DE.1 + firstAllowance
        (idealLogLength Z DE.1) (idealLogLength Z DE.2)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - shift)
    (hrightExponent : (s.right S χ).fiber ≠ 0 → exponentR + (T.right S χ).zeroProductExponent * ε ≤
      (total - idealLogLength Z DE.2 + firstAllowance
        (idealLogLength Z DE.2) (idealLogLength Z DE.1)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - shift)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total + shift)) :
    T.classZeroBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) ε Czero S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        (((fiberCap : ℝ) * Czero * (tupleL : ℝ) * profileL +
          (fiberCap : ℝ) * Czero * (tupleR : ℝ) * profileR) / 2)) *
        (firstCommonWeight Z DE.1 DE.2 *
          (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
            ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hL := (T.left S χ).zeroBudget_div_allowance_le_of_nonzero_fiber
    ε Czero profileL (Ideal.absNorm S.val : ℝ) exponentL _ loss shift fiberCap tupleL
    hC hprofileL (Nat.cast_nonneg _) hleftFiber hleftTuples hleftProfile hleftExponent
  have hR := (T.right S χ).zeroBudget_div_allowance_le_of_nonzero_fiber
    ε Czero profileR (Ideal.absNorm S.val : ℝ) exponentR _ loss shift fiberCap tupleR
    hC hprofileR (Nat.cast_nonneg _) hrightFiber hrightTuples hrightProfile hrightExponent
  have hfirst' := first_profile_power_with_shift
    Z parentWidth total shift firstAmplitude p.weightBound hz hfirst
  have hc := original_terminal_class_scalar_with_shift Z parentWidth
    (firstLeftAllowance Z total DE.1 DE.2) (firstRightAllowance Z total DE.1 DE.2)
    p.rowBound ‖(moebius S.val : ℂ)‖
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖
    ((actualFourierMeasure chart.kernel).real Set.univ) (firstTerminalFourierCost chart.kernel)
    ((T.left S χ).zeroBudget ε Czero) ((T.right S χ).zeroBudget ε Czero)
    ((fiberCap : ℝ) * Czero * (tupleL : ℝ) * profileL)
    ((fiberCap : ℝ) * Czero * (tupleR : ℝ) * profileR)
    (Ideal.absNorm S.val : ℝ) loss shift firstAmplitude (firstCommonWeight Z DE.1 DE.2)
    hz (firstLeftAllowance_pos Z total hz _ _) (firstRightAllowance_pos Z total hz _ _)
    p.rowBound_nonneg (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg
    (firstTerminalFourierCost_nonneg chart.kernel) (by positivity) (by positivity)
    (Nat.cast_nonneg _) hL hR (firstTerminalFourierCost_bound chart.kernel)
    (p.normalized_allowance_prefactor hZ total parentWidth
      (firstAmplitude * Z ^ shift) hfirst')
  simpa only [classZeroBudget, classWeight] using hc

/-- The same direct source, divisor and Fourier mass are used for
the tail. The uniform cutoff saving is combined with the actual
coefficient degree before the original first profile is paid. -/
theorem classTailBudget_le_combined_profiles
    (hZ : 1 < Z)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle)
    (Cerror total parentWidth loss shift firstAmplitude profileL profileR
      exponentL exponentR : ℝ) (fiberCap tupleL tupleR : ℕ)
    (hC : 0 ≤ Cerror) (hprofileL : 0 ≤ profileL) (hprofileR : 0 ≤ profileR)
    (hleftFiber : (s.left S χ).fiber ≤ fiberCap)
    (hrightFiber : (s.right S χ).fiber ≤ fiberCap)
    (hleftTuples : (T.left S χ).windows.multiplicity ≤ tupleL)
    (hrightTuples : (T.right S χ).windows.multiplicity ≤ tupleR)
    (hleftProfile : (s.left S χ).fiber ≠ 0 → (T.left S χ).tailAmplitude ≤
      (profileL / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentL)
    (hrightProfile : (s.right S χ).fiber ≠ 0 → (T.right S χ).tailAmplitude ≤
      (profileR / (Ideal.absNorm S.val : ℝ)) * Z ^ exponentR)
    (hleftExponent : (s.left S χ).fiber ≠ 0 → exponentL - Nsave ≤
      (total - idealLogLength Z DE.1 + firstAllowance
        (idealLogLength Z DE.1) (idealLogLength Z DE.2)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - shift)
    (hrightExponent : (s.right S χ).fiber ≠ 0 → exponentR - Nsave ≤
      (total - idealLogLength Z DE.2 + firstAllowance
        (idealLogLength Z DE.2) (idealLogLength Z DE.1)
        (idealLogLength Z (firstActiveRadical DE.1 DE.2))) + loss - shift)
    (hfirst : p.weightBound ≤ firstAmplitude * Z ^ (parentWidth - total + shift)) :
    T.classTailBudget
        (fun _ _ => firstLeftAllowance Z total DE.1 DE.2)
        (fun _ _ => firstRightAllowance Z total DE.1 DE.2) Cerror S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost chart.kernel *
        (((fiberCap : ℝ) * Cerror * (tupleL : ℝ) * profileL +
          (fiberCap : ℝ) * Cerror * (tupleR : ℝ) * profileR) / 2)) *
        (firstCommonWeight Z DE.1 DE.2 *
          (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
            ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hL := (T.left S χ).tailBudget_div_allowance_le_of_nonzero_fiber
    Cerror profileL (Ideal.absNorm S.val : ℝ) exponentL _ loss shift fiberCap tupleL
    hC hprofileL (Nat.cast_nonneg _) hleftFiber hleftTuples hleftProfile hleftExponent
  have hR := (T.right S χ).tailBudget_div_allowance_le_of_nonzero_fiber
    Cerror profileR (Ideal.absNorm S.val : ℝ) exponentR _ loss shift fiberCap tupleR
    hC hprofileR (Nat.cast_nonneg _) hrightFiber hrightTuples hrightProfile hrightExponent
  have hfirst' := first_profile_power_with_shift
    Z parentWidth total shift firstAmplitude p.weightBound hz hfirst
  have hc := original_terminal_class_scalar_with_shift Z parentWidth
    (firstLeftAllowance Z total DE.1 DE.2) (firstRightAllowance Z total DE.1 DE.2)
    p.rowBound ‖(moebius S.val : ℂ)‖
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖
    ((actualFourierMeasure chart.kernel).real Set.univ) (firstTerminalFourierCost chart.kernel)
    ((T.left S χ).tailBudget Cerror) ((T.right S χ).tailBudget Cerror)
    ((fiberCap : ℝ) * Cerror * (tupleL : ℝ) * profileL)
    ((fiberCap : ℝ) * Cerror * (tupleR : ℝ) * profileR)
    (Ideal.absNorm S.val : ℝ) loss shift firstAmplitude (firstCommonWeight Z DE.1 DE.2)
    hz (firstLeftAllowance_pos Z total hz _ _) (firstRightAllowance_pos Z total hz _ _)
    p.rowBound_nonneg (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg
    (firstTerminalFourierCost_nonneg chart.kernel) (by positivity) (by positivity)
    (Nat.cast_nonneg _) hL hR (firstTerminalFourierCost_bound chart.kernel)
    (p.normalized_allowance_prefactor hZ total parentWidth
      (firstAmplitude * Z ^ shift) hfirst')
  simpa only [classTailBudget, classWeight] using hc

end SecondStages.DualTerminalCalibration
end FirstBlockDirectData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.DualTerminalCalibration.classZeroBudget_le_combined_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.DualTerminalCalibration.classTailBudget_le_combined_profiles
