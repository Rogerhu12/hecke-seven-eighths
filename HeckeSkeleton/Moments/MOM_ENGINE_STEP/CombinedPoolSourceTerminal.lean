import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedPoolSecondTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstDivisorSourceTerminal

set_option linter.unusedSectionVars false

/-!
# Original pooled source sums after the central degree cancels

The first profile shift and the opposite second coefficient exponent
are combined on each actual class. The original common label, physical
mask, internal divisor, finite phase and first Fourier mass are then
summed without changing their carrier. The inverse internal-divisor
norm remains in the original arithmetic mass.

The only counting costs are the actual complete-tuple multiplicities
and the already proved original arithmetic mass. Their constants are
chosen before all moving sources and scales. The public zero and tail
entries build their class bounds from individual amplitude windows;
neither accepts a terminal or transformed-source bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open CommonSupportMass UniqueFactorizationMonoid MeasureTheory

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
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

local instance combinedPoolSourceTerminalCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualFirstSource

/-- Individual original arithmetic and first-profile windows. The
shift stays with its own first common label and physical divisor. -/
structure CombinedTerminalOriginalWindows
    (s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
    (normBound parentWidth firstAmplitude kernelBound : ℝ)
    (total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) where
  oldMask : Ideal (𝓞 K)
  old_squarefree : Squarefree oldMask
  old_ne_zero : oldMask ≠ 0
  old_divides : ∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val
  column_norm : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ normBound
  maskIdeal : Ideal (𝓞 K)
  mask_ne_zero : maskIdeal ≠ 0
  mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBound
  original_mask : OriginalMaskPrimeData s.mask maskIdeal
  first_profile : ∀ v D, (s.pools v D).weightBound ≤
    firstAmplitude * Z ^ (parentWidth - total v D + shift v D)
  first_kernel : ∀ v D, (firstTerminalFourierControl (W := W)).seminorms.sup
    (schwartzSeminormFamily ℝ W ℂ) (s.charts v D).kernel ≤ kernelBound

namespace SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

/-- The original main and 1/6/7 amplitudes. Every tag retains its
own fibre and norm charge; the uniform pool density is paid once. -/
structure CombinedZeroAmplitudeWindows
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (ε loss profileConstant Mmax : ℝ) (fiberCap : ℕ)
    (total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) where
  exponentL : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val),
      ((PUnit × PUnit) →* Circle) → PoolSourceTag P → ℝ
  exponentR : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val),
      ((PUnit × PUnit) →* Circle) → PoolSourceTag P → ℝ
  row_left : ∀ v D S, ((s.pools v D).divisorPools.leftData S).rowExponent ≤ Mmax
  row_right : ∀ v D S, ((s.pools v D).divisorPools.rightData S).rowExponent ≤ Mmax
  large_left : ∀ v D S,
    2 * (((s.pools v D).divisorPools.leftData S).rowExponent / (ell / 2) +
      ((s.pools v D).divisorPools.leftData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)
  large_right : ∀ v D S,
    2 * (((s.pools v D).divisorPools.rightData S).rowExponent / (ell / 2) +
      ((s.pools v D).divisorPools.rightData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)
  fiber_left : ∀ v D S χ tag, (((R v D).left S χ).tag tag).fiber ≤ fiberCap
  fiber_right : ∀ v D S χ tag, (((R v D).right S χ).tag tag).fiber ≤ fiberCap
  tuples_left : ∀ v D S χ tag, (((T v D).left S χ).tag tag).windows.multiplicity ≤
    idealDivisorCount (v.val.1 ^ 2) ^ k * 15 ^ k
  tuples_right : ∀ v D S χ tag, (((T v D).right S χ).tag tag).windows.multiplicity ≤
    idealDivisorCount (v.val.2 ^ 2) ^ k * 15 ^ k
  amplitude_left : ∀ v D S χ tag, (((R v D).left S χ).tag tag).fiber ≠ 0 →
    (((T v D).left S χ).tag tag).zeroAmplitude ≤
      (profileConstant * poolTagNormCharge P tag / (Ideal.absNorm S.val : ℝ)) *
        Z ^ exponentL v D S χ tag
  amplitude_right : ∀ v D S χ tag, (((R v D).right S χ).tag tag).fiber ≠ 0 →
    (((T v D).right S χ).tag tag).zeroAmplitude ≤
      (profileConstant * poolTagNormCharge P tag / (Ideal.absNorm S.val : ℝ)) *
        Z ^ exponentR v D S χ tag
  exponent_left : ∀ v D S χ tag, (((R v D).left S χ).tag tag).fiber ≠ 0 →
    exponentL v D S χ tag + (((T v D).left S χ).tag tag).zeroProductExponent * ε ≤
      (total v D - idealLogLength Z v.val.1 + firstAllowance
        (idealLogLength Z v.val.1) (idealLogLength Z v.val.2)
        (idealLogLength Z (firstActiveRadical v.val.1 v.val.2))) + loss - shift v D - eps
  exponent_right : ∀ v D S χ tag, (((R v D).right S χ).tag tag).fiber ≠ 0 →
    exponentR v D S χ tag + (((T v D).right S χ).tag tag).zeroProductExponent * ε ≤
      (total v D - idealLogLength Z v.val.2 + firstAllowance
        (idealLogLength Z v.val.2) (idealLogLength Z v.val.1)
        (idealLogLength Z (firstActiveRadical v.val.1 v.val.2))) + loss - shift v D - eps

/-- The original main and 1/6/7 amplitudes. Every tag retains its
own fibre and norm charge; the uniform pool density is paid once. -/
structure CombinedTailAmplitudeWindows
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (loss profileConstant Mmax : ℝ) (fiberCap : ℕ)
    (total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) where
  exponentL : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val),
      ((PUnit × PUnit) →* Circle) → PoolSourceTag P → ℝ
  exponentR : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val),
      ((PUnit × PUnit) →* Circle) → PoolSourceTag P → ℝ
  row_left : ∀ v D S, ((s.pools v D).divisorPools.leftData S).rowExponent ≤ Mmax
  row_right : ∀ v D S, ((s.pools v D).divisorPools.rightData S).rowExponent ≤ Mmax
  large_left : ∀ v D S,
    2 * (((s.pools v D).divisorPools.leftData S).rowExponent / (ell / 2) +
      ((s.pools v D).divisorPools.leftData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)
  large_right : ∀ v D S,
    2 * (((s.pools v D).divisorPools.rightData S).rowExponent / (ell / 2) +
      ((s.pools v D).divisorPools.rightData S).frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)
  fiber_left : ∀ v D S χ tag, (((R v D).left S χ).tag tag).fiber ≤ fiberCap
  fiber_right : ∀ v D S χ tag, (((R v D).right S χ).tag tag).fiber ≤ fiberCap
  tuples_left : ∀ v D S χ tag, (((T v D).left S χ).tag tag).windows.multiplicity ≤
    idealDivisorCount (v.val.1 ^ 2) ^ k * 15 ^ k
  tuples_right : ∀ v D S χ tag, (((T v D).right S χ).tag tag).windows.multiplicity ≤
    idealDivisorCount (v.val.2 ^ 2) ^ k * 15 ^ k
  amplitude_left : ∀ v D S χ tag, (((R v D).left S χ).tag tag).fiber ≠ 0 →
    (((T v D).left S χ).tag tag).tailAmplitude ≤
      (profileConstant * poolTagNormCharge P tag / (Ideal.absNorm S.val : ℝ)) *
        Z ^ exponentL v D S χ tag
  amplitude_right : ∀ v D S χ tag, (((R v D).right S χ).tag tag).fiber ≠ 0 →
    (((T v D).right S χ).tag tag).tailAmplitude ≤
      (profileConstant * poolTagNormCharge P tag / (Ideal.absNorm S.val : ℝ)) *
        Z ^ exponentR v D S χ tag
  exponent_left : ∀ v D S χ tag, (((R v D).left S χ).tag tag).fiber ≠ 0 →
    exponentL v D S χ tag - Nsave ≤
      (total v D - idealLogLength Z v.val.1 + firstAllowance
        (idealLogLength Z v.val.1) (idealLogLength Z v.val.2)
        (idealLogLength Z (firstActiveRadical v.val.1 v.val.2))) + loss - shift v D - eps
  exponent_right : ∀ v D S χ tag, (((R v D).right S χ).tag tag).fiber ≠ 0 →
    exponentR v D S χ tag - Nsave ≤
      (total v D - idealLogLength Z v.val.2 + firstAllowance
        (idealLogLength Z v.val.2) (idealLogLength Z v.val.1)
        (idealLogLength Z (firstActiveRadical v.val.1 v.val.2))) + loss - shift v D - eps

end SecondStages
end ActualFirstSource

/-- The finite summation step only. The actual terminal entries below
derive its class inequality from their raw amplitude windows. -/
theorem combined_pool_class_sum_from_original_windows
    (k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Csum : ℝ, 0 < Csum ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ (Cterminal parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
      (fiberCap : ℕ), 0 ≤ Cterminal → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant → 0 ≤ Mmax →
    ∀ total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ O : s.CombinedTerminalOriginalWindows normBound parentWidth firstAmplitude kernelBound total shift,
    ∀ cost : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
      ∀ S : divisorPool (s.pools v D).rightData.columns
        (fun j => ((s.pools v D).rightData.ideal j).val), ((PUnit × PUnit) →* Circle) → ℝ,
    (∀ v D S χ, cost v D S χ / Z ^ parentWidth ≤
      (firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
        ((poolTerminalConstant K ell Mmax * ((fiberCap : ℝ) * Cterminal * (idealDivisorCount (v.val.1 ^ 2) ^ k * 15 ^ k : ℕ) * profileConstant) +
          poolTerminalConstant K ell Mmax * ((fiberCap : ℝ) * Cterminal * (idealDivisorCount (v.val.2 ^ 2) ^ k * 15 ^ k : ℕ) * profileConstant)) / 2)) *
        (firstCommonWeight Z v.val.1 v.val.2 *
          (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
            ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss) →
      ((s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pools v D).rightData.columns
          (fun j => ((s.pools v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle, cost v D S χ) / Z ^ parentWidth ≤
      (s.fiber : ℝ) * poolTerminalConstant K ell Mmax * fiberCap * Cterminal * firstAmplitude * kernelBound *
        profileConstant * Csum * Z ^ (loss + ε) / (Ideal.absNorm O.oldMask : ℝ) := by
  sorry

/-- Uniform complete pool zero budget. Every class inequality is
constructed here from the actual amplitudes after its first-profile
shift cancels. The first arithmetic carrier is unchanged. -/
theorem actual_pool_second_dual_zero_from_combined_windows
    (k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Csum : ℝ, 0 < Csum ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ (sTail sZero : Finset (ℕ × ℕ)) (Lmax Nsave decay : ℝ),
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ (εzero Czero parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
      (fiberCap : ℕ), 0 ≤ Czero → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant → 0 ≤ Mmax →
    ∀ total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ O : s.CombinedTerminalOriginalWindows normBound parentWidth firstAmplitude kernelBound total shift,
    ∀ U : R.CombinedZeroAmplitudeWindows T εzero loss profileConstant Mmax fiberCap total shift,
      R.dualSecondZeroBudget T (s.canonicalNormalization P.base_gt_one total) εzero Czero / Z ^ parentWidth ≤
        (s.fiber : ℝ) * poolTerminalConstant K ell Mmax * fiberCap * Czero * firstAmplitude * kernelBound *
          profileConstant * Csum * Z ^ (loss + ε) / (Ideal.absNorm O.oldMask : ℝ) := by
  sorry

/-- The complete pool tail uses the same finite arithmetic mass
and original Fourier kernel. Its additional pre-pool degree remains
in the supplied individual decay ledgers, before this summation. -/
theorem actual_pool_second_dual_tail_from_combined_windows
    (k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Csum : ℝ, 0 < Csum ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ (sTail sZero : Finset (ℕ × ℕ)) (Lmax Nsave decay : ℝ),
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ (Cerror parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
      (fiberCap : ℕ), 0 ≤ Cerror → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant → 0 ≤ Mmax →
    ∀ total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ O : s.CombinedTerminalOriginalWindows normBound parentWidth firstAmplitude kernelBound total shift,
    ∀ U : R.CombinedTailAmplitudeWindows T loss profileConstant Mmax fiberCap total shift,
      R.dualSecondTailBudget T (s.canonicalNormalization P.base_gt_one total) Cerror / Z ^ parentWidth ≤
        (s.fiber : ℝ) * poolTerminalConstant K ell Mmax * fiberCap * Cerror * firstAmplitude * kernelBound *
          profileConstant * Csum * Z ^ (loss + ε) / (Ideal.absNorm O.oldMask : ℝ) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.combined_pool_class_sum_from_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_pool_second_dual_zero_from_combined_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_pool_second_dual_tail_from_combined_windows
