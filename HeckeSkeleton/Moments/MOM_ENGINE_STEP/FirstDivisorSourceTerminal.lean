import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorBlockTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolTerminalMasks

/-!
# True first-source terminal sums from original coefficient atoms

Every sum below is on the original common pair, original mask divisor,
original first Möbius divisor and original finite phase.  Both side
calibrations come from actual coefficient atoms and residual profiles.
The side mask cap is computed from the actual pool masks; its bound is
proved from original per-prime certificates, including the residual
amplifier prime.  No terminal sum or total arithmetic mass is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
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
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable {slotsL slotsR k : ℕ} {B Lmax Nsave decay : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)}

abbrev FirstDivisorWindows (slotsL slotsR : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay

def firstDivisorCalibration
    (T : R.FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay) :
    R.TerminalCalibration sTail sZero k Lmax Nsave decay :=
  fun v D => (T v D).calibration

/-- This cap is a computed maximum of the actual masks and is fixed
before either continuous Fourier variable. -/
def firstDivisorMaskCap (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℕ :=
  poolTerminalMaskCap P (fun b => (((R v D).left S χ).tag b).mask)
    (fun b => (((R v D).right S χ).tag b).mask)

theorem firstDivisorMaskCap_left
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (tag : PoolSourceTag P) :
    (((R v D).left S χ).tag tag).mask.card ≤ R.firstDivisorMaskCap v D S χ :=
  poolTerminalMaskCap_left P _ _ tag

theorem firstDivisorMaskCap_right
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (tag : PoolSourceTag P) :
    (((R v D).right S χ).tag tag).mask.card ≤ R.firstDivisorMaskCap v D S χ :=
  poolTerminalMaskCap_right P _ _ tag

variable
    (T : R.FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay)

def firstDivisorZeroCoefficient
    (Czero firstAmplitude profileConstant Mmax : ℝ) (fiberCap : ℕ)
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pools v D).rightData.columns
      (fun j => ((s.pools v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
    ((EngineStep.firstDivisorZeroCoefficient ell Mmax B Czero profileConstant slotsL k
        fiberCap (R.firstDivisorMaskCap v D S χ) v.val.1 +
      EngineStep.firstDivisorZeroCoefficient ell Mmax B Czero profileConstant slotsR k
        fiberCap (R.firstDivisorMaskCap v D S χ) v.val.2) / 2)

def firstDivisorTailCoefficient (_R : s.SecondStages (E := E) (hDiff := hDiff))
    (Cerror firstAmplitude profileConstant Mmax : ℝ) (fiberCap : ℕ)
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset) : ℝ :=
  firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
    ((EngineStep.firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slotsL k
        fiberCap v.val.1 +
      EngineStep.firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slotsR k
        fiberCap v.val.2) / 2)

/-- The whole canonical second-zero budget is summed over its genuine
original carrier.  Mask bounds in `U` are the tautological bounds by
`firstDivisorMaskCap`; the subsequent prime certificates pay this cap. -/
theorem secondZeroBudget_le_original_label_sum
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
    (ε Czero parentWidth loss firstAmplitude profileConstant Mmax : ℝ) (fiberCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (U : ∀ v D S χ, (T v D).ZeroWindows S χ ε (total v D) loss
      profileConstant profileConstant Mmax fiberCap (R.firstDivisorMaskCap v D S χ))
    (hfirst : ∀ v D, (s.pools v D).weightBound ≤
      firstAmplitude * Z ^ (parentWidth - total v D)) :
    R.secondZeroBudget (R.firstDivisorCalibration T)
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
  unfold secondZeroBudget
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  simp only [zeroBudget, FirstBlockPoolData.SecondStages.TerminalCalibration.zeroBudget,
    firstDivisorCalibration, ActualFirstSource.canonicalNormalization, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro χ _
  exact (T v D).classZeroBudget_le_original_profiles S χ ε Czero (total v D) parentWidth loss
    firstAmplitude profileConstant profileConstant Mmax fiberCap (R.firstDivisorMaskCap v D S χ)
    (U v D S χ) hC hprofile hprofile (hfirst v D)

/-- The canonical second tail has the same first labels and the same
first-divisor denominator.  It uses the original side decay ledgers. -/
theorem tailBudget_le_original_label_sum
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
    R.tailBudget (R.firstDivisorCalibration T)
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
  simp only [tailBudget, FirstBlockPoolData.SecondStages.TerminalCalibration.tailBudget,
    firstDivisorCalibration, ActualFirstSource.canonicalNormalization, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro χ _
  exact (T v D).classTailBudget_le_original_profiles S χ Cerror (total v D) parentWidth loss
    firstAmplitude profileConstant profileConstant Mmax fiberCap
    (exponentL v D S χ) (exponentR v D S χ) (U v D S χ) hC hprofile hprofile (hfirst v D)

/-- Original prime dictionaries, individual norm/profile windows and
the original coefficient-based calibrations.  No field estimates a
whole terminal, source or arithmetic mass. -/
structure OriginalZeroSourceWindows
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

structure OriginalTailSourceWindows
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

private theorem original_zero_coefficient_le
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
  have hbase : 0 ≤ poolTerminalConstant K ell Mmax * fiberCap * Czero * profileConstant :=
    mul_nonneg (mul_nonneg (mul_nonneg hpool (Nat.cast_nonneg _)) hC) hprofile
  have hpow : B ^ slots ≤ B ^ cap := pow_le_pow_right₀ hB hslots
  calc
    _ = (poolTerminalConstant K ell Mmax * fiberCap * Czero * profileConstant) * B ^ slots *
        (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) * (2 : ℝ) ^ maskCap := by
      unfold firstDivisorZeroCoefficient
      ring
    _ ≤ (poolTerminalConstant K ell Mmax * fiberCap * Czero * profileConstant) * B ^ cap *
        countBound * maskBound :=
      mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hpow hbase) hcount (Nat.cast_nonneg _)
          (mul_nonneg hbase (pow_nonneg (zero_le_one.trans hB) _)))
        hmask (pow_nonneg (by norm_num) _)
        (mul_nonneg (mul_nonneg hbase (pow_nonneg (zero_le_one.trans hB) _)) hcountBound)
    _ = _ := by ring

private theorem original_tail_coefficient_le
    (ell Mmax B Cerror profileConstant : ℝ) (slots cap k fiberCap : ℕ)
    (D : Ideal (𝓞 K)) (countBound : ℝ)
    (hpool : 0 ≤ poolTerminalConstant K ell Mmax) (hB : 1 ≤ B)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant) (hslots : slots ≤ cap)
    (hcountBound : 0 ≤ countBound)
    (hcount : (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) ≤ countBound) :
    firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slots k fiberCap D ≤
      (poolTerminalConstant K ell Mmax * fiberCap * Cerror * B ^ cap * profileConstant) *
        countBound := by
  simpa only [firstDivisorZeroCoefficient, firstDivisorTailCoefficient, pow_zero, mul_one] using
    original_zero_coefficient_le ell Mmax B Cerror profileConstant slots cap k fiberCap 0 D
      countBound 1 hpool hB hC hprofile hslots hcountBound hcount (by simp)

/-- A uniform bound on the genuine second-zero budget, obtained from
the original coefficient atoms, actual per-tag prime dictionaries and
original first-label harmonic mass.  The constant is selected before
all moving sources, scales, profiles and finite labels. -/
theorem actual_second_zero_from_original_windows
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
    ∀ T : R.FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay,
    ∀ (εzero Czero parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
      (fiberCap : ℕ), 0 ≤ Czero → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant → 0 ≤ Mmax →
    ∀ total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ U : R.OriginalZeroSourceWindows T normBound εzero parentWidth loss firstAmplitude
      kernelBound profileConstant Mmax fiberCap total,
      R.secondZeroBudget (R.firstDivisorCalibration T)
          (s.canonicalNormalization P.base_gt_one total) εzero Czero / Z ^ parentWidth ≤
        (s.fiber : ℝ) * poolTerminalConstant K ell Mmax * fiberCap * Czero *
          firstAmplitude * kernelBound * B ^ cap * profileConstant * Cterminal *
            Z ^ (loss + ε) / (Ideal.absNorm U.oldMask : ℝ) := by
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Ccount, hCcount, hcount⟩ :=
    first_terminal_tuple_multiplicity_subpower (K := K) k normBound δ hN hδ
  obtain ⟨Cmask, hCmask, hmask⟩ := pool_terminal_masks_subpower (A := A)
    (α := HeightOneSpectrum A.R) normBound L δ hN hL hδ
  obtain ⟨Cmass, hCmass, hmass⟩ := actual_first_terminal_mass_from_original_windows
    (U := W) (C := C) (hΓ := hΓ) (μv := μv) (finiteTest := finiteTest)
    normBound (ε / 2) hN hhalf
  let CF := (firstTerminalFourierControl (W := W)).constant
  have hCF : 0 < CF := (firstTerminalFourierControl (W := W)).constant_pos
  refine ⟨CF * (Ccount * (15 ^ k : ℕ)) * Cmask * Cmass, by positivity, ?_⟩
  intro Z ell eps bad P hell ω ψ centered d a t Y₁ Y₂ X hX s R slotsL slotsR hslotsL hslotsR
    B hB sTail sZero Lmax Nsave decay T εzero Czero parentWidth loss firstAmplitude kernelBound
    profileConstant Mmax fiberCap hC hfirst hkernel hprofile hMmax total U
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hpool : 0 ≤ poolTerminalConstant K ell Mmax :=
    (poolTerminalConstant_pos (K := K) ell Mmax P.exponent_pos hMmax).le
  let H : ℝ := firstAmplitude * (CF * kernelBound) *
    (poolTerminalConstant K ell Mmax * fiberCap * Czero * B ^ cap * profileConstant) *
      (Ccount * (15 ^ k : ℕ)) * Cmask
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hnorm (v : s.CommonLabel) :
      (Ideal.absNorm v.val.1 : ℝ) ≤ Z ^ normBound ∧
        (Ideal.absNorm v.val.2 : ℝ) ≤ Z ^ normBound :=
    actualCommonLabels_norm s.columns s.columns _ _
      (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1)
      (Z ^ normBound) U.column_norm U.column_norm (v.val, ∅)
      ((mem_actualCommonLabels _ _ _ _ _).mpr ⟨v.property, Finset.empty_subset _⟩)
  have hnonzero (v : s.CommonLabel) : v.val.1 ≠ 0 ∧ v.val.2 ≠ 0 := by
    constructor
    · rw [← (s.block v).common_left]
      exact (primePowerProduct (s.block v).primes (s.block v).leftMultiplicity).property.1
    · rw [← (s.block v).common_right]
      exact (primePowerProduct (s.block v).primes (s.block v).rightMultiplicity).property.1
  have hcoefficient (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
      (S : divisorPool (s.pools v D).rightData.columns
        (fun j => ((s.pools v D).rightData.ideal j).val))
      (χ : (PUnit × PUnit) →* Circle) :
      R.firstDivisorZeroCoefficient (B := B) (slotsL := slotsL) (slotsR := slotsR) (k := k)
          Czero firstAmplitude profileConstant Mmax fiberCap v D S χ ≤ H * Z ^ (2 * δ) := by
    have hcap : (2 : ℝ) ^ R.firstDivisorMaskCap v D S χ ≤ Cmask * Z ^ δ :=
      hmask Z ell eps bad P hell U.maskIdeal v.val.1 v.val.2 U.mask_ne_zero
        (hnonzero v).1 (hnonzero v).2 U.mask_norm (hnorm v).1 (hnorm v).2 _ _
        (U.masks_left v D S χ) (U.masks_right v D S χ)
    let Q : ℝ := (poolTerminalConstant K ell Mmax * fiberCap * Czero * B ^ cap *
      profileConstant) * (Ccount * (15 ^ k : ℕ)) * Cmask
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hside (slots : ℕ) (hs : slots ≤ cap) (common : Ideal (𝓞 K))
        (hcommon : (Ideal.absNorm common : ℝ) ≤ Z ^ normBound) :
        firstDivisorZeroCoefficient ell Mmax B Czero profileConstant slots k fiberCap
          (R.firstDivisorMaskCap v D S χ) common ≤ Q * Z ^ (2 * δ) := by
      apply (original_zero_coefficient_le ell Mmax B Czero profileConstant slots cap k fiberCap
        (R.firstDivisorMaskCap v D S χ) common ((Ccount * (15 ^ k : ℕ)) * Z ^ δ)
        (Cmask * Z ^ δ) hpool hB hC hprofile hs (by positivity)
        (hcount Z P.base_gt_one.le common hcommon) hcap).trans_eq
      dsimp [Q]
      rw [show 2 * δ = δ + δ by ring, Real.rpow_add hz]
      ring
    have hmean := div_le_div_of_nonneg_right
      (add_le_add (hside slotsL hslotsL v.val.1 (hnorm v).1)
        (hside slotsR hslotsR v.val.2 (hnorm v).2)) (by norm_num : (0 : ℝ) ≤ 2)
    have hmean' :
        (firstDivisorZeroCoefficient ell Mmax B Czero profileConstant slotsL k fiberCap
            (R.firstDivisorMaskCap v D S χ) v.val.1 +
          firstDivisorZeroCoefficient ell Mmax B Czero profileConstant slotsR k fiberCap
            (R.firstDivisorMaskCap v D S χ) v.val.2) / 2 ≤ Q * Z ^ (2 * δ) :=
      hmean.trans_eq (by ring)
    have hF : firstTerminalFourierCost (s.charts v D).kernel ≤ CF * kernelBound :=
      mul_le_mul_of_nonneg_left (U.first_kernel v D) hCF.le
    unfold ActualFirstSource.SecondStages.firstDivisorZeroCoefficient
    calc
      _ ≤ firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
          (Q * Z ^ (2 * δ)) :=
        mul_le_mul_of_nonneg_left hmean'
          (mul_nonneg hfirst (firstTerminalFourierCost_nonneg _))
      _ ≤ firstAmplitude * (CF * kernelBound) * (Q * Z ^ (2 * δ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hfirst)
          (mul_nonneg hQ (Real.rpow_nonneg hz.le _))
      _ = _ := by dsimp [Q, H]; ring
  have hm := hmass Z ell eps bad P centered d a t Y₁ Y₂ X hX s U.oldMask
    U.old_squarefree U.old_ne_zero U.old_divides U.column_norm U.maskIdeal
    U.mask_ne_zero U.mask_norm U.original_mask
  have hraw := R.secondZeroBudget_le_original_label_sum T total εzero Czero parentWidth loss
    firstAmplitude profileConstant Mmax fiberCap hC hprofile U.classes U.first_profile
  apply hraw.trans
  calc
    _ ≤ (s.fiber : ℝ) *
        ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pools v D).rightData.columns
          (fun j => ((s.pools v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          (H * Z ^ (2 * δ)) *
            (firstCommonWeight Z v.val.1 v.val.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro S _
      apply Finset.sum_le_sum
      intro χ _
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_right (hcoefficient v D S χ)
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hz.le _)
            (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))) (norm_nonneg _))
    _ = ((s.fiber : ℝ) * H * Z ^ (2 * δ) * Z ^ loss) * s.firstTerminalArithmeticMass := by
      simp only [ActualFirstSource.firstTerminalArithmeticMass, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]
    _ ≤ ((s.fiber : ℝ) * H * Z ^ (2 * δ) * Z ^ loss) *
        (Cmass * Z ^ (ε / 2) / (Ideal.absNorm U.oldMask : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by
      have he : loss + ε = 2 * δ + loss + ε / 2 := by dsimp [δ]; ring
      rw [he, Real.rpow_add hz, Real.rpow_add hz]
      dsimp [H]
      ring

/-- The original second-stage tail is bounded on exactly the same
first carrier.  Its decay saving is the supplied numerical ledger,
while its coefficient, Fourier mass and finite arithmetic sum are
proved here from their original atoms and individual windows. -/
theorem actual_second_tail_from_original_windows
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
    ∀ T : R.FirstDivisorWindows slotsL slotsR B sTail sZero k Lmax Nsave decay,
    ∀ (Cerror parentWidth loss firstAmplitude kernelBound profileConstant Mmax : ℝ)
      (fiberCap : ℕ), 0 ≤ Cerror → 0 ≤ firstAmplitude → 0 ≤ kernelBound →
      0 ≤ profileConstant → 0 ≤ Mmax →
    ∀ total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ,
    ∀ U : R.OriginalTailSourceWindows T normBound parentWidth loss firstAmplitude
      kernelBound profileConstant Mmax fiberCap total,
      ((s.fiber : ℝ) * R.tailBudget (R.firstDivisorCalibration T)
          (s.canonicalNormalization P.base_gt_one total) Cerror) / Z ^ parentWidth ≤
        (s.fiber : ℝ) * poolTerminalConstant K ell Mmax * fiberCap * Cerror *
          firstAmplitude * kernelBound * B ^ cap * profileConstant * Cterminal *
            Z ^ (loss + ε) / (Ideal.absNorm U.oldMask : ℝ) := by
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Ccount, hCcount, hcount⟩ :=
    first_terminal_tuple_multiplicity_subpower (K := K) k normBound δ hN hδ
  obtain ⟨Cmass, hCmass, hmass⟩ := actual_first_terminal_mass_from_original_windows
    (U := W) (C := C) (hΓ := hΓ) (μv := μv) (finiteTest := finiteTest)
    normBound δ hN hδ
  let CF := (firstTerminalFourierControl (W := W)).constant
  have hCF : 0 < CF := (firstTerminalFourierControl (W := W)).constant_pos
  refine ⟨CF * (Ccount * (15 ^ k : ℕ)) * Cmass, by positivity, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s R slotsL slotsR hslotsL hslotsR
    B hB sTail sZero Lmax Nsave decay T Cerror parentWidth loss firstAmplitude kernelBound
    profileConstant Mmax fiberCap hC hfirst hkernel hprofile hMmax total U
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hpool : 0 ≤ poolTerminalConstant K ell Mmax :=
    (poolTerminalConstant_pos (K := K) ell Mmax P.exponent_pos hMmax).le
  let H : ℝ := firstAmplitude * (CF * kernelBound) *
    (poolTerminalConstant K ell Mmax * fiberCap * Cerror * B ^ cap * profileConstant) *
      (Ccount * (15 ^ k : ℕ))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hnorm (v : s.CommonLabel) :
      (Ideal.absNorm v.val.1 : ℝ) ≤ Z ^ normBound ∧
        (Ideal.absNorm v.val.2 : ℝ) ≤ Z ^ normBound :=
    actualCommonLabels_norm s.columns s.columns _ _
      (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1)
      (Z ^ normBound) U.column_norm U.column_norm (v.val, ∅)
      ((mem_actualCommonLabels _ _ _ _ _).mpr ⟨v.property, Finset.empty_subset _⟩)
  have hcoefficient (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset) :
      R.firstDivisorTailCoefficient (B := B) (slotsL := slotsL) (slotsR := slotsR) (k := k)
          Cerror firstAmplitude profileConstant Mmax fiberCap v D ≤ H * Z ^ δ := by
    let Q : ℝ := (poolTerminalConstant K ell Mmax * fiberCap * Cerror * B ^ cap *
      profileConstant) * (Ccount * (15 ^ k : ℕ))
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hside (slots : ℕ) (hs : slots ≤ cap) (common : Ideal (𝓞 K))
        (hcommon : (Ideal.absNorm common : ℝ) ≤ Z ^ normBound) :
        firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slots k fiberCap common ≤
          Q * Z ^ δ := by
      apply (original_tail_coefficient_le ell Mmax B Cerror profileConstant slots cap k fiberCap
        common ((Ccount * (15 ^ k : ℕ)) * Z ^ δ) hpool hB hC hprofile hs (by positivity)
        (hcount Z P.base_gt_one.le common hcommon)).trans_eq
      dsimp [Q]
      ring
    have hmean := div_le_div_of_nonneg_right
      (add_le_add (hside slotsL hslotsL v.val.1 (hnorm v).1)
        (hside slotsR hslotsR v.val.2 (hnorm v).2)) (by norm_num : (0 : ℝ) ≤ 2)
    have hmean' :
        (firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slotsL k fiberCap v.val.1 +
          firstDivisorTailCoefficient ell Mmax B Cerror profileConstant slotsR k fiberCap v.val.2) / 2 ≤
            Q * Z ^ δ := hmean.trans_eq (by ring)
    have hF : firstTerminalFourierCost (s.charts v D).kernel ≤ CF * kernelBound :=
      mul_le_mul_of_nonneg_left (U.first_kernel v D) hCF.le
    unfold ActualFirstSource.SecondStages.firstDivisorTailCoefficient
    calc
      _ ≤ firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel * (Q * Z ^ δ) :=
        mul_le_mul_of_nonneg_left hmean'
          (mul_nonneg hfirst (firstTerminalFourierCost_nonneg _))
      _ ≤ firstAmplitude * (CF * kernelBound) * (Q * Z ^ δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hfirst)
          (mul_nonneg hQ (Real.rpow_nonneg hz.le _))
      _ = _ := by dsimp [Q, H]; ring
  have hm := hmass Z ell eps bad P centered d a t Y₁ Y₂ X hX s U.oldMask
    U.old_squarefree U.old_ne_zero U.old_divides U.column_norm U.maskIdeal
    U.mask_ne_zero U.mask_norm U.original_mask
  have hraw := mul_le_mul_of_nonneg_left
    (R.tailBudget_le_original_label_sum T total Cerror parentWidth loss
      firstAmplitude profileConstant Mmax fiberCap U.exponentL U.exponentR
      hC hprofile U.classes U.first_profile) (Nat.cast_nonneg s.fiber : (0 : ℝ) ≤ s.fiber)
  rw [mul_div_assoc]
  apply hraw.trans
  calc
    _ ≤ (s.fiber : ℝ) *
        ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pools v D).rightData.columns
          (fun j => ((s.pools v D).rightData.ideal j).val),
        ∑ χ : (PUnit × PUnit) →* Circle,
          (H * Z ^ δ) *
            (firstCommonWeight Z v.val.1 v.val.2 *
              (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
                ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖) * Z ^ loss := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro S _
      apply Finset.sum_le_sum
      intro χ _
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_right (hcoefficient v D)
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hz.le _)
            (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))) (norm_nonneg _))
    _ = ((s.fiber : ℝ) * H * Z ^ δ * Z ^ loss) * s.firstTerminalArithmeticMass := by
      simp only [ActualFirstSource.firstTerminalArithmeticMass, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]
    _ ≤ ((s.fiber : ℝ) * H * Z ^ δ * Z ^ loss) *
        (Cmass * Z ^ δ / (Ideal.absNorm U.oldMask : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by
      have he : loss + ε = δ + loss + δ := by dsimp [δ]; ring
      rw [he, Real.rpow_add hz, Real.rpow_add hz]
      dsimp [H]
      ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.secondZeroBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.tailBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_zero_from_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_tail_from_original_windows
