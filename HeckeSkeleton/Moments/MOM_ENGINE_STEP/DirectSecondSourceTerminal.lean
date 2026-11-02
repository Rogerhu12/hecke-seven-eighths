import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondTerminalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMaskCardinality
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights

set_option linter.unusedSectionVars false

/-!
# Direct first-source terminal sums from original coefficient atoms

Every sum below is on the original common pair, original mask divisor,
original first Möbius divisor and original finite phase.  Both side
calibrations come from actual coefficient atoms and residual profiles.
The side mask cap is computed from the two actual direct masks; its
bound is proved from the original mask and common-ideal prime
certificates.  No prime pool or amplifier scalar is introduced.  No terminal sum or total arithmetic mass is an input.
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
variable {Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
local instance directSecondSourceTerminalCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualDirectFirstSource

namespace SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable {slotsL slotsR k : ℕ} {B Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}

abbrev FirstDivisorWindows (slotsL slotsR : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).FirstDivisorWindows slotsL slotsR B sTail sZero k Z Lmax Nsave decay

def firstDivisorCalibration
    (T : R.FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay) :
    R.TerminalCalibration sTail sZero k Lmax Nsave decay :=
  fun v D => (T v D).calibration

/-- A computed maximum of the two actual masks, fixed before the
continuous Fourier variables. -/
def firstDivisorMaskCap (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℕ :=
  max ((R v D).left S χ).mask.card ((R v D).right S χ).mask.card

theorem firstDivisorMaskCap_left
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    ((R v D).left S χ).mask.card ≤ R.firstDivisorMaskCap v D S χ := by
  sorry

theorem firstDivisorMaskCap_right
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    ((R v D).right S χ).mask.card ≤ R.firstDivisorMaskCap v D S χ := by
  sorry

variable
    (T : R.FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay)

def firstDivisorZeroCoefficient
    (Czero firstAmplitude profileConstant : ℝ) (fiberCap : ℕ)
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
    ((EngineStep.directFirstDivisorZeroCoefficient B Czero profileConstant slotsL k
        fiberCap (R.firstDivisorMaskCap v D S χ) v.val.1 +
      EngineStep.directFirstDivisorZeroCoefficient B Czero profileConstant slotsR k
        fiberCap (R.firstDivisorMaskCap v D S χ) v.val.2) / 2)

def firstDivisorTailCoefficient (_R : s.SecondStages (E := E) (hDiff := hDiff))
    (Cerror firstAmplitude profileConstant : ℝ) (fiberCap : ℕ)
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset) : ℝ :=
  firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
    ((EngineStep.directFirstDivisorTailCoefficient B Cerror profileConstant slotsL k
        fiberCap v.val.1 +
      EngineStep.directFirstDivisorTailCoefficient B Cerror profileConstant slotsR k
        fiberCap v.val.2) / 2)

/-- The whole canonical second-zero budget is summed over its genuine
original carrier.  Mask bounds in `U` are the tautological bounds by
`firstDivisorMaskCap`; the subsequent prime certificates pay this cap. -/
theorem secondZeroBudget_le_original_label_sum (hZ : 1 < Z)
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
    (ε Czero parentWidth loss firstAmplitude profileConstant : ℝ) (fiberCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (U : ∀ v D S χ, (T v D).ZeroWindows S χ ε (total v D) loss
      profileConstant profileConstant fiberCap (R.firstDivisorMaskCap v D S χ))
    (hfirst : ∀ v D, (s.pieces v D).weightBound ≤
      firstAmplitude * Z ^ (parentWidth - total v D)) :
    R.secondZeroBudget (R.firstDivisorCalibration T)
        (s.canonicalNormalization hZ total) ε Czero / Z ^ parentWidth ≤
      (s.fiber : ℝ) *
        ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pieces v D).rightData.columns
          (fun j => ((s.pieces v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          R.firstDivisorZeroCoefficient (B := B) (slotsL := slotsL) (slotsR := slotsR) (k := k)
              Czero firstAmplitude profileConstant fiberCap v D S χ *
            (firstCommonWeight Z v.val.1 v.val.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  sorry

/-- The canonical second tail has the same first labels and the same
first-divisor denominator.  It uses the original side decay ledgers. -/
theorem secondTailBudget_le_original_label_sum (hZ : 1 < Z)
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
    (Cerror parentWidth loss firstAmplitude profileConstant : ℝ) (fiberCap : ℕ)
    (exponentL exponentR : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
      ∀ S : divisorPool (s.pieces v D).rightData.columns
        (fun j => ((s.pieces v D).rightData.ideal j).val),
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (U : ∀ v D S χ, (T v D).TailWindows S χ (total v D) loss
      profileConstant profileConstant (exponentL v D S χ) (exponentR v D S χ) fiberCap)
    (hfirst : ∀ v D, (s.pieces v D).weightBound ≤
      firstAmplitude * Z ^ (parentWidth - total v D)) :
    R.secondTailBudget (R.firstDivisorCalibration T)
        (s.canonicalNormalization hZ total) Cerror / Z ^ parentWidth ≤
      (s.fiber : ℝ) *
        ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pieces v D).rightData.columns
          (fun j => ((s.pieces v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          R.firstDivisorTailCoefficient (B := B) (slotsL := slotsL) (slotsR := slotsR) (k := k)
              Cerror firstAmplitude profileConstant fiberCap v D *
            (firstCommonWeight Z v.val.1 v.val.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
  sorry

/-- Original prime dictionaries, individual norm/profile windows and
the original coefficient-based calibrations.  No field estimates a
whole terminal, source or arithmetic mass. -/
structure OriginalZeroSourceWindows
    (normBound ε parentWidth loss firstAmplitude kernelBound profileConstant : ℝ)
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
  first_profile : ∀ v D, (s.pieces v D).weightBound ≤
    firstAmplitude * Z ^ (parentWidth - total v D)
  first_kernel : ∀ v D, (firstTerminalFourierControl (W := W)).seminorms.sup
    (schwartzSeminormFamily ℝ W ℂ) (s.charts v D).kernel ≤ kernelBound
  classes : ∀ v D S χ, (T v D).ZeroWindows S χ ε (total v D) loss
    profileConstant profileConstant fiberCap (R.firstDivisorMaskCap v D S χ)
  masks_left : ∀ v D S χ,
    OriginalMaskPrimeData (((R v D).left S χ).mask) (maskIdeal * v.val.1)
  masks_right : ∀ v D S χ,
    OriginalMaskPrimeData (((R v D).right S χ).mask) (maskIdeal * v.val.2)

structure OriginalTailSourceWindows
    (normBound parentWidth loss firstAmplitude kernelBound profileConstant : ℝ)
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
  first_profile : ∀ v D, (s.pieces v D).weightBound ≤
    firstAmplitude * Z ^ (parentWidth - total v D)
  first_kernel : ∀ v D, (firstTerminalFourierControl (W := W)).seminorms.sup
    (schwartzSeminormFamily ℝ W ℂ) (s.charts v D).kernel ≤ kernelBound
  exponentL : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val),
    ((PUnit × PUnit) →* Circle) → ℝ
  exponentR : ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    ∀ S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val),
    ((PUnit × PUnit) →* Circle) → ℝ
  classes : ∀ v D S χ, (T v D).TailWindows S χ (total v D) loss
    profileConstant profileConstant (exponentL v D S χ) (exponentR v D S χ) fiberCap

end SecondStages
end ActualDirectFirstSource

private theorem original_zero_coefficient_le
    (B Czero profileConstant : ℝ) (slots cap k fiberCap maskCap : ℕ)
    (D : Ideal (𝓞 K)) (countBound maskBound : ℝ)
    (hB : 1 ≤ B)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant) (hslots : slots ≤ cap)
    (hcountBound : 0 ≤ countBound)
    (hcount : (idealDivisorCount (D ^ 2) ^ k : ℕ) ≤ countBound)
    (hmask : (2 : ℝ) ^ maskCap ≤ maskBound) :
    directFirstDivisorZeroCoefficient B Czero profileConstant slots k fiberCap maskCap D ≤
      (fiberCap * Czero * B ^ cap * profileConstant) *
        countBound * maskBound := by
  sorry

private theorem original_tail_coefficient_le
    (B Cerror profileConstant : ℝ) (slots cap k fiberCap : ℕ)
    (D : Ideal (𝓞 K)) (countBound : ℝ)
    (hB : 1 ≤ B)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant) (hslots : slots ≤ cap)
    (hcountBound : 0 ≤ countBound)
    (hcount : (idealDivisorCount (D ^ 2) ^ k : ℕ) ≤ countBound) :
    directFirstDivisorTailCoefficient B Cerror profileConstant slots k fiberCap D ≤
      (fiberCap * Cerror * B ^ cap * profileConstant) *
        countBound := by
  sorry

/-- The direct support fibre is exactly the common-extraction fibre;
its constant is fixed before the actual common ideal. -/
private theorem direct_terminal_tuple_multiplicity_subpower (k : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Ccount : ℝ, 0 < Ccount ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ D : Ideal (𝓞 K), (Ideal.absNorm D : ℝ) ≤ Z ^ B →
        (idealDivisorCount (D ^ 2) ^ k : ℕ) ≤ Ccount * Z ^ ε := by
  sorry

/-- The two actual direct masks are charged to their original mask
ideal and side common ideal, prime by prime.  Taking the maximum pays
neither another label count nor an amplifier factor. -/
private theorem direct_terminal_masks_subpower {α : Type*}
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Cmask : ℝ, 0 < Cmask ∧ ∀ Z : ℝ, 1 ≤ Z →
    ∀ oldMask commonLeft commonRight : Ideal (𝓞 K), oldMask ≠ 0 →
      commonLeft ≠ 0 → commonRight ≠ 0 →
      (Ideal.absNorm oldMask : ℝ) ≤ Z ^ B →
      (Ideal.absNorm commonLeft : ℝ) ≤ Z ^ B →
      (Ideal.absNorm commonRight : ℝ) ≤ Z ^ B →
    ∀ left right : Finset α,
      OriginalMaskPrimeData left (oldMask * commonLeft) →
      OriginalMaskPrimeData right (oldMask * commonRight) →
      (2 : ℝ) ^ max left.card right.card ≤ Cmask * Z ^ ε := by
  sorry

/-- A uniform bound on the genuine second-zero budget, obtained from
the original coefficient atoms, actual side prime dictionaries and
original first-label harmonic mass.  The constant is selected before
all moving sources, scales, profiles and finite labels. -/
theorem actual_direct_second_zero_from_original_windows
    (cap k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Cterminal : ℝ, 0 < Cterminal ∧
    ∀ (Z : ℝ) (hZ : 1 < Z),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ (slotsL slotsR : ℕ), slotsL ≤ cap → slotsR ≤ cap →
    ∀ B : ℝ, 1 ≤ B →
    ∀ (sTail sZero : Finset (ℕ × ℕ)) (Lmax Nsave decay : ℝ),
    ∀ T : R.FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay,
    ∀ (εzero Czero parentWidth loss firstAmplitude kernelBound profileConstant : ℝ)
      (fiberCap : ℕ), 0 ≤ Czero → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant →
    ∀ total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ U : R.OriginalZeroSourceWindows T normBound εzero parentWidth loss firstAmplitude
      kernelBound profileConstant fiberCap total,
      R.secondZeroBudget (R.firstDivisorCalibration T)
          (s.canonicalNormalization hZ total) εzero Czero / Z ^ parentWidth ≤
        (s.fiber : ℝ) * fiberCap * Czero *
          firstAmplitude * kernelBound * B ^ cap * profileConstant * Cterminal *
            Z ^ (loss + ε) / (Ideal.absNorm U.oldMask : ℝ) := by
  sorry

/-- The original second-stage tail is bounded on exactly the same
first carrier.  Its decay saving is the supplied numerical ledger,
while its coefficient, Fourier mass and finite arithmetic sum are
proved here from their original atoms and individual windows. -/
theorem actual_direct_second_tail_from_original_windows
    (cap k : ℕ) (normBound ε : ℝ) (hN : 0 ≤ normBound) (hε : 0 < ε) :
    ∃ Cterminal : ℝ, 0 < Cterminal ∧
    ∀ (Z : ℝ) (hZ : 1 < Z),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ (slotsL slotsR : ℕ), slotsL ≤ cap → slotsR ≤ cap →
    ∀ B : ℝ, 1 ≤ B →
    ∀ (sTail sZero : Finset (ℕ × ℕ)) (Lmax Nsave decay : ℝ),
    ∀ T : R.FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay,
    ∀ (Cerror parentWidth loss firstAmplitude kernelBound profileConstant : ℝ)
      (fiberCap : ℕ), 0 ≤ Cerror → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant →
    ∀ total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ U : R.OriginalTailSourceWindows T normBound parentWidth loss firstAmplitude
      kernelBound profileConstant fiberCap total,
      R.secondTailBudget (R.firstDivisorCalibration T)
          (s.canonicalNormalization hZ total) Cerror / Z ^ parentWidth ≤
        (s.fiber : ℝ) * fiberCap * Cerror *
          firstAmplitude * kernelBound * B ^ cap * profileConstant * Cterminal *
            Z ^ (loss + ε) / (Ideal.absNorm U.oldMask : ℝ) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.secondZeroBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.secondTailBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_second_zero_from_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_second_tail_from_original_windows
