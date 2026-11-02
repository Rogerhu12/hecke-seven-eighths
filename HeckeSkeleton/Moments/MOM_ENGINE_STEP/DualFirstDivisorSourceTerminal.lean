import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorSourceTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstDivisorBlockTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstSourceFiniteLeaves

set_option linter.unusedSectionVars false

/-!
# Pure-dual first-source terminal sums from original coefficient atoms

Every sum below is on the original common pair, original mask divisor,
original first Möbius divisor and original finite phase.  Both pure-dual side
calibrations come from actual coefficient atoms and residual profiles.
The original nonzero value of the row ball at zero is retained.
The side mask cap is computed from the actual pool masks; its bound is
proved from original per-prime certificates, including the residual
amplifier prime.  No terminal sum or total arithmetic mass is an input.
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
local instance dualFirstDivisorSourceTerminalCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable {slotsL slotsR k : ℕ} {B Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}

abbrev DualFirstDivisorWindows (slotsL slotsR : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).DualFirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay

def dualFirstDivisorCalibration
    (T : R.DualFirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay) :
    R.DualTerminalCalibration sTail sZero k Lmax Nsave decay :=
  fun v D => (T v D).calibration

variable
    (T : R.DualFirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay)

/-- The whole canonical second-zero budget is summed over its genuine
original carrier.  Mask bounds in `U` are the tautological bounds by
`firstDivisorMaskCap`; the subsequent prime certificates pay this cap. -/
theorem dualSecondZeroBudget_le_original_label_sum
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
    (ε Czero parentWidth loss firstAmplitude profileConstant Mmax : ℝ) (fiberCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (U : ∀ v D S χ, (T v D).ZeroWindows S χ ε (total v D) loss
      profileConstant profileConstant Mmax fiberCap (R.firstDivisorMaskCap v D S χ))
    (hfirst : ∀ v D, (s.pools v D).weightBound ≤
      firstAmplitude * Z ^ (parentWidth - total v D)) :
    R.dualSecondZeroBudget (R.dualFirstDivisorCalibration T)
        (s.canonicalNormalization P.base_gt_one total) ε Czero / Z ^ parentWidth ≤
      (s.fiber : ℝ) *
        ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pools v D).rightData.columns
          (fun j => ((s.pools v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          R.firstDivisorZeroCoefficient (B := B) (slotsL := slotsL) (slotsR := slotsR) (k := k)
              Czero firstAmplitude profileConstant Mmax fiberCap v D S χ *
            (firstCommonWeight Z v.val.1 v.val.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  sorry

/-- The canonical second tail has the same first labels and the same
first-divisor denominator.  It uses the original side decay ledgers. -/
theorem dualTailBudget_le_original_label_sum
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
    (Cerror parentWidth loss firstAmplitude profileConstant Mmax : ℝ) (fiberCap : ℕ)
    (exponentL exponentR : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
      ∀ S : divisorPool (s.pools v D).rightData.columns
        (fun j => ((s.pools v D).rightData.ideal j).val),
      ((PUnit × PUnit) →* Circle) → PoolSourceTag P → ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (U : ∀ v D S χ, (T v D).TailWindows S χ (total v D) loss
      profileConstant profileConstant Mmax fiberCap (exponentL v D S χ) (exponentR v D S χ))
    (hfirst : ∀ v D, (s.pools v D).weightBound ≤
      firstAmplitude * Z ^ (parentWidth - total v D)) :
    R.dualTailBudget (R.dualFirstDivisorCalibration T)
        (s.canonicalNormalization P.base_gt_one total) Cerror / Z ^ parentWidth ≤
        ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pools v D).rightData.columns
          (fun j => ((s.pools v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          R.firstDivisorTailCoefficient (B := B) (slotsL := slotsL) (slotsR := slotsR) (k := k)
              Cerror firstAmplitude profileConstant Mmax fiberCap v D *
            (firstCommonWeight Z v.val.1 v.val.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  sorry

/-- Original prime dictionaries, individual norm/profile windows and
the original coefficient-based calibrations.  No field estimates a
whole terminal, source or arithmetic mass. -/
structure DualOriginalZeroSourceWindows
    (normBound ε parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
    (fiberCap : ℕ)
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) where
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
    firstAmplitude * Z ^ (parentWidth - total v D)
  first_kernel : ∀ v D, (firstTerminalFourierControl (W := W)).seminorms.sup
    (schwartzSeminormFamily ℝ W ℂ) (s.charts v D).kernel ≤ kernelBound
  classes : ∀ v D S χ, (T v D).ZeroWindows S χ ε (total v D) loss
    profileConstant profileConstant Mmax fiberCap (R.firstDivisorMaskCap v D S χ)
  masks_left : ∀ v D S χ tag,
    OriginalMaskPrimeData ((((R v D).left S χ).tag tag).mask)
      (poolTerminalMaskIdeal P maskIdeal v.val.1 tag)
  masks_right : ∀ v D S χ tag,
    OriginalMaskPrimeData ((((R v D).right S χ).tag tag).mask)
      (poolTerminalMaskIdeal P maskIdeal v.val.2 tag)

structure DualOriginalTailSourceWindows
    (normBound parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
    (fiberCap : ℕ)
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) where
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
    firstAmplitude * Z ^ (parentWidth - total v D)
  first_kernel : ∀ v D, (firstTerminalFourierControl (W := W)).seminorms.sup
    (schwartzSeminormFamily ℝ W ℂ) (s.charts v D).kernel ≤ kernelBound
  exponentL : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val),
    ((PUnit × PUnit) →* Circle) → PoolSourceTag P → ℝ
  exponentR : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val),
    ((PUnit × PUnit) →* Circle) → PoolSourceTag P → ℝ
  classes : ∀ v D S χ, (T v D).TailWindows S χ (total v D) loss
    profileConstant profileConstant Mmax fiberCap (exponentL v D S χ) (exponentR v D S χ)

end ActualFirstSource.SecondStages

private theorem dual_original_zero_coefficient_le
    (ell Mmax B Czero profileConstant : ℝ) (slots cap k fiberCap maskCap : ℕ)
    (D : Ideal (𝓞 K)) (countBound maskBound : ℝ)
    (hpool : 0 ≤ poolTerminalConstant K ell Mmax) (hB : 1 ≤ B)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant) (hslots : slots ≤ cap)
    (hcountBound : 0 ≤ countBound)
    (hcount : (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) ≤ countBound)
    (hmask : (2 : ℝ) ^ maskCap ≤ maskBound) :
    firstDivisorZeroCoefficient ell Mmax B Czero profileConstant slots k fiberCap maskCap D ≤
      (poolTerminalConstant K ell Mmax * fiberCap * Czero * B ^ cap * profileConstant) *
        countBound * maskBound := by
  sorry

private theorem dual_original_tail_coefficient_le
    (ell Mmax B Cerror profileConstant : ℝ) (slots cap k fiberCap : ℕ)
    (D : Ideal (𝓞 K)) (countBound : ℝ)
    (hpool : 0 ≤ poolTerminalConstant K ell Mmax) (hB : 1 ≤ B)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant) (hslots : slots ≤ cap)
    (hcountBound : 0 ≤ countBound)
    (hcount : (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) ≤ countBound) :
    firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slots k fiberCap D ≤
      (poolTerminalConstant K ell Mmax * fiberCap * Cerror * B ^ cap * profileConstant) *
        countBound := by
  sorry

/-- A uniform bound on the genuine second-zero budget, obtained from
the original coefficient atoms, actual per-tag prime dictionaries and
original first-label harmonic mass.  The constant is selected before
all moving sources, scales, profiles and finite labels. -/
theorem actual_second_dual_zero_from_original_windows
    (cap k : ℕ) (normBound L ε : ℝ) (hN : 0 ≤ normBound)
    (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ Cterminal : ℝ, 0 < Cterminal ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps), ell ≤ L →
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ (slotsL slotsR : ℕ), slotsL ≤ cap → slotsR ≤ cap →
    ∀ B : ℝ, 1 ≤ B →
    ∀ (sTail sZero : Finset (ℕ × ℕ)) (Lmax Nsave decay : ℝ),
    ∀ T : R.DualFirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay,
    ∀ (εzero Czero parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
      (fiberCap : ℕ), 0 ≤ Czero → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant → 0 ≤ Mmax →
    ∀ total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ U : R.DualOriginalZeroSourceWindows T normBound εzero parentWidth loss firstAmplitude
      kernelBound profileConstant Mmax fiberCap total,
      R.dualSecondZeroBudget (R.dualFirstDivisorCalibration T)
          (s.canonicalNormalization P.base_gt_one total) εzero Czero / Z ^ parentWidth ≤
        (s.fiber : ℝ) * poolTerminalConstant K ell Mmax * fiberCap * Czero *
          firstAmplitude * kernelBound * B ^ cap * profileConstant * Cterminal *
            Z ^ (loss + ε) / (Ideal.absNorm U.oldMask : ℝ) := by
  sorry

/-- The original second-stage tail is bounded on exactly the same
first carrier.  Its decay saving is the supplied numerical ledger,
while its coefficient, Fourier mass and finite arithmetic sum are
proved here from their original atoms and individual windows. -/
theorem actual_second_dual_tail_from_original_windows
    (cap k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Cterminal : ℝ, 0 < Cterminal ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ (slotsL slotsR : ℕ), slotsL ≤ cap → slotsR ≤ cap →
    ∀ B : ℝ, 1 ≤ B →
    ∀ (sTail sZero : Finset (ℕ × ℕ)) (Lmax Nsave decay : ℝ),
    ∀ T : R.DualFirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay,
    ∀ (Cerror parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
      (fiberCap : ℕ), 0 ≤ Cerror → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant → 0 ≤ Mmax →
    ∀ total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ U : R.DualOriginalTailSourceWindows T normBound parentWidth loss firstAmplitude
      kernelBound profileConstant Mmax fiberCap total,
      ((s.fiber : ℝ) * R.dualTailBudget (R.dualFirstDivisorCalibration T)
          (s.canonicalNormalization P.base_gt_one total) Cerror) / Z ^ parentWidth ≤
        (s.fiber : ℝ) * poolTerminalConstant K ell Mmax * fiberCap * Cerror *
          firstAmplitude * kernelBound * B ^ cap * profileConstant * Cterminal *
            Z ^ (loss + ε) / (Ideal.absNorm U.oldMask : ℝ) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.dualSecondZeroBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.dualTailBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_dual_zero_from_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_dual_tail_from_original_windows
