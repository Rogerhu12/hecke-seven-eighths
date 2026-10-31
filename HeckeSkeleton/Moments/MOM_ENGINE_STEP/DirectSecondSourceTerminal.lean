import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondTerminalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMaskCardinality
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights

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
    ((R v D).left S χ).mask.card ≤ R.firstDivisorMaskCap v D S χ :=
  le_max_left _ _

theorem firstDivisorMaskCap_right
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    ((R v D).right S χ).mask.card ≤ R.firstDivisorMaskCap v D S χ :=
  le_max_right _ _

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
  unfold secondZeroBudget
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  simp only [FirstBlockDirectData.SecondStages.TerminalCalibration.zeroBudget,
    firstDivisorCalibration, ActualDirectFirstSource.canonicalNormalization, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro χ _
  exact (T v D).classZeroBudget_le_original_profiles hZ S χ ε Czero (total v D) parentWidth loss
    firstAmplitude profileConstant profileConstant fiberCap (R.firstDivisorMaskCap v D S χ)
    (U v D S χ) hC hprofile hprofile (hfirst v D)

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
  unfold secondTailBudget
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  simp only [FirstBlockDirectData.SecondStages.TerminalCalibration.tailBudget,
    firstDivisorCalibration, ActualDirectFirstSource.canonicalNormalization, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro χ _
  exact (T v D).classTailBudget_le_original_profiles hZ S χ Cerror (total v D) parentWidth loss
    firstAmplitude profileConstant profileConstant
    (exponentL v D S χ) (exponentR v D S χ) fiberCap (U v D S χ) hC hprofile hprofile (hfirst v D)

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
  have hbase : 0 ≤ fiberCap * Czero * profileConstant :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) hprofile
  have hpow : B ^ slots ≤ B ^ cap := pow_le_pow_right₀ hB hslots
  calc
    _ = (fiberCap * Czero * profileConstant) * B ^ slots *
        (idealDivisorCount (D ^ 2) ^ k : ℕ) * (2 : ℝ) ^ maskCap := by
      unfold directFirstDivisorZeroCoefficient
      ring
    _ ≤ (fiberCap * Czero * profileConstant) * B ^ cap *
        countBound * maskBound :=
      mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hpow hbase) hcount (Nat.cast_nonneg _)
          (mul_nonneg hbase (pow_nonneg (zero_le_one.trans hB) _)))
        hmask (pow_nonneg (by norm_num) _)
        (mul_nonneg (mul_nonneg hbase (pow_nonneg (zero_le_one.trans hB) _)) hcountBound)
    _ = _ := by ring

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
  simpa only [directFirstDivisorZeroCoefficient, directFirstDivisorTailCoefficient, pow_zero, mul_one] using
    original_zero_coefficient_le B Cerror profileConstant slots cap k fiberCap 0 D
      countBound 1 hB hC hprofile hslots hcountBound hcount (by simp)

/-- The direct support fibre is exactly the common-extraction fibre;
its constant is fixed before the actual common ideal. -/
private theorem direct_terminal_tuple_multiplicity_subpower (k : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Ccount : ℝ, 0 < Ccount ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ D : Ideal (𝓞 K), (Ideal.absNorm D : ℝ) ≤ Z ^ B →
        (idealDivisorCount (D ^ 2) ^ k : ℕ) ≤ Ccount * Z ^ ε := by
  obtain ⟨Ccount, hC, hcount⟩ :=
    support_tuple_multiplicity_subpower (K := K) k (2 * B) ε (by positivity) hε
  refine ⟨Ccount, hC, ?_⟩
  intro Z hZ D hD
  have hz : 0 ≤ Z := zero_le_one.trans hZ
  have hD2 : (Ideal.absNorm (D ^ 2) : ℝ) ≤ Z ^ (2 * B) := by
    calc
      _ = (Ideal.absNorm D : ℝ) ^ 2 := by simp only [map_pow, Nat.cast_pow]
      _ ≤ (Z ^ B) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hD 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hz]; congr 1; ring
  exact hcount Z hZ (D ^ 2) hD2

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
  obtain ⟨Cmask, hC, hmask⟩ := original_mask_labels_subpower (K := K)
    (2 * B) ε (by positivity) hε
  refine ⟨Cmask, hC, ?_⟩
  intro Z hZ oldMask commonLeft commonRight hM0 hL0 hR0 hMN hLN hRN left right ML MR
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hproduct (common : Ideal (𝓞 K)) (hcommon : (Ideal.absNorm common : ℝ) ≤ Z ^ B) :
      (Ideal.absNorm (oldMask * common) : ℝ) ≤ Z ^ (2 * B) := by
    simp only [map_mul, Nat.cast_mul]
    calc
      _ ≤ Z ^ B * Z ^ B :=
        mul_le_mul hMN hcommon (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
      _ = _ := by rw [← Real.rpow_add hz]; congr 1; ring
  have hl : (2 : ℝ) ^ left.card ≤ Cmask * Z ^ ε := by
    simpa only [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] using
      hmask Z hZ left (oldMask * commonLeft) (mul_ne_zero hM0 hL0)
        (hproduct commonLeft hLN) ML
  have hr : (2 : ℝ) ^ right.card ≤ Cmask * Z ^ ε := by
    simpa only [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] using
      hmask Z hZ right (oldMask * commonRight) (mul_ne_zero hM0 hR0)
        (hproduct commonRight hRN) MR
  rcases le_total left.card right.card with h | h
  · simpa only [max_eq_right h] using hr
  · simpa only [max_eq_left h] using hl

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
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Ccount, hCcount, hcount⟩ :=
    direct_terminal_tuple_multiplicity_subpower (K := K) k normBound δ hN hδ
  obtain ⟨Cmask, hCmask, hmask⟩ := direct_terminal_masks_subpower (K := K)
    (α := HeightOneSpectrum A.R) normBound δ hN hδ
  obtain ⟨Cmass, hCmass, hmass⟩ := actual_direct_first_terminal_mass_from_original_windows
    (U := W) (C := C) (hΓ := hΓ) (μv := μv) (finiteTest := finiteTest)
    normBound (ε / 2) hN hhalf
  let CF := (firstTerminalFourierControl (W := W)).constant
  have hCF : 0 < CF := (firstTerminalFourierControl (W := W)).constant_pos
  refine ⟨CF * Ccount * Cmask * Cmass, by positivity, ?_⟩
  intro Z hZ ω ψ centered d a t Y₁ Y₂ X hX s R slotsL slotsR hslotsL hslotsR
    B hB sTail sZero Lmax Nsave decay T εzero Czero parentWidth loss firstAmplitude kernelBound
    profileConstant fiberCap hC hfirst hkernel hprofile total U
  have hz : 0 < Z := zero_lt_one.trans hZ
  let H : ℝ := firstAmplitude * (CF * kernelBound) *
    (fiberCap * Czero * B ^ cap * profileConstant) *
      Ccount * Cmask
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
      (S : divisorPool (s.pieces v D).rightData.columns
        (fun j => ((s.pieces v D).rightData.ideal j).val))
      (χ : (PUnit × PUnit) →* Circle) :
      R.firstDivisorZeroCoefficient (B := B) (slotsL := slotsL) (slotsR := slotsR) (k := k)
          Czero firstAmplitude profileConstant fiberCap v D S χ ≤ H * Z ^ (2 * δ) := by
    have hcap : (2 : ℝ) ^ R.firstDivisorMaskCap v D S χ ≤ Cmask * Z ^ δ :=
      hmask Z hZ.le U.maskIdeal v.val.1 v.val.2 U.mask_ne_zero
        (hnonzero v).1 (hnonzero v).2 U.mask_norm (hnorm v).1 (hnorm v).2 _ _
        (U.masks_left v D S χ) (U.masks_right v D S χ)
    let Q : ℝ := (fiberCap * Czero * B ^ cap *
      profileConstant) * Ccount * Cmask
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hside (slots : ℕ) (hs : slots ≤ cap) (common : Ideal (𝓞 K))
        (hcommon : (Ideal.absNorm common : ℝ) ≤ Z ^ normBound) :
        directFirstDivisorZeroCoefficient B Czero profileConstant slots k fiberCap
          (R.firstDivisorMaskCap v D S χ) common ≤ Q * Z ^ (2 * δ) := by
      apply (original_zero_coefficient_le B Czero profileConstant slots cap k fiberCap
        (R.firstDivisorMaskCap v D S χ) common (Ccount * Z ^ δ)
        (Cmask * Z ^ δ) hB hC hprofile hs (by positivity)
        (hcount Z hZ.le common hcommon) hcap).trans_eq
      dsimp [Q]
      rw [show 2 * δ = δ + δ by ring, Real.rpow_add hz]
      ring
    have hmean := div_le_div_of_nonneg_right
      (add_le_add (hside slotsL hslotsL v.val.1 (hnorm v).1)
        (hside slotsR hslotsR v.val.2 (hnorm v).2)) (by norm_num : (0 : ℝ) ≤ 2)
    have hmean' :
        (directFirstDivisorZeroCoefficient B Czero profileConstant slotsL k fiberCap
            (R.firstDivisorMaskCap v D S χ) v.val.1 +
          directFirstDivisorZeroCoefficient B Czero profileConstant slotsR k fiberCap
            (R.firstDivisorMaskCap v D S χ) v.val.2) / 2 ≤ Q * Z ^ (2 * δ) :=
      hmean.trans_eq (by ring)
    have hF : firstTerminalFourierCost (s.charts v D).kernel ≤ CF * kernelBound :=
      mul_le_mul_of_nonneg_left (U.first_kernel v D) hCF.le
    unfold ActualDirectFirstSource.SecondStages.firstDivisorZeroCoefficient
    calc
      _ ≤ firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel *
          (Q * Z ^ (2 * δ)) :=
        mul_le_mul_of_nonneg_left hmean'
          (mul_nonneg hfirst (firstTerminalFourierCost_nonneg _))
      _ ≤ firstAmplitude * (CF * kernelBound) * (Q * Z ^ (2 * δ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hfirst)
          (mul_nonneg hQ (Real.rpow_nonneg hz.le _))
      _ = _ := by dsimp [Q, H]; ring
  have hm := hmass Z hZ centered d a t Y₁ Y₂ X hX s U.oldMask
    U.old_squarefree U.old_ne_zero U.old_divides U.column_norm U.maskIdeal
    U.mask_ne_zero U.mask_norm U.original_mask
  have hraw := R.secondZeroBudget_le_original_label_sum T hZ total εzero Czero parentWidth loss
    firstAmplitude profileConstant fiberCap hC hprofile U.classes U.first_profile
  apply hraw.trans
  calc
    _ ≤ (s.fiber : ℝ) *
        ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pieces v D).rightData.columns
          (fun j => ((s.pieces v D).rightData.ideal j).val),
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
      simp only [ActualDirectFirstSource.firstTerminalArithmeticMass, Finset.mul_sum,
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
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Ccount, hCcount, hcount⟩ :=
    direct_terminal_tuple_multiplicity_subpower (K := K) k normBound δ hN hδ
  obtain ⟨Cmass, hCmass, hmass⟩ := actual_direct_first_terminal_mass_from_original_windows
    (U := W) (C := C) (hΓ := hΓ) (μv := μv) (finiteTest := finiteTest)
    normBound δ hN hδ
  let CF := (firstTerminalFourierControl (W := W)).constant
  have hCF : 0 < CF := (firstTerminalFourierControl (W := W)).constant_pos
  refine ⟨CF * Ccount * Cmass, by positivity, ?_⟩
  intro Z hZ ω ψ centered d a t Y₁ Y₂ X hX s R slotsL slotsR hslotsL hslotsR
    B hB sTail sZero Lmax Nsave decay T Cerror parentWidth loss firstAmplitude kernelBound
    profileConstant fiberCap hC hfirst hkernel hprofile total U
  have hz : 0 < Z := zero_lt_one.trans hZ
  let H : ℝ := firstAmplitude * (CF * kernelBound) *
    (fiberCap * Cerror * B ^ cap * profileConstant) *
      Ccount
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
          Cerror firstAmplitude profileConstant fiberCap v D ≤ H * Z ^ δ := by
    let Q : ℝ := (fiberCap * Cerror * B ^ cap *
      profileConstant) * Ccount
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hside (slots : ℕ) (hs : slots ≤ cap) (common : Ideal (𝓞 K))
        (hcommon : (Ideal.absNorm common : ℝ) ≤ Z ^ normBound) :
        directFirstDivisorTailCoefficient B Cerror profileConstant slots k fiberCap common ≤
          Q * Z ^ δ := by
      apply (original_tail_coefficient_le B Cerror profileConstant slots cap k fiberCap
        common (Ccount * Z ^ δ) hB hC hprofile hs (by positivity)
        (hcount Z hZ.le common hcommon)).trans_eq
      dsimp [Q]
      ring
    have hmean := div_le_div_of_nonneg_right
      (add_le_add (hside slotsL hslotsL v.val.1 (hnorm v).1)
        (hside slotsR hslotsR v.val.2 (hnorm v).2)) (by norm_num : (0 : ℝ) ≤ 2)
    have hmean' :
        (directFirstDivisorTailCoefficient B Cerror profileConstant slotsL k fiberCap v.val.1 +
          directFirstDivisorTailCoefficient B Cerror profileConstant slotsR k fiberCap v.val.2) / 2 ≤
            Q * Z ^ δ := hmean.trans_eq (by ring)
    have hF : firstTerminalFourierCost (s.charts v D).kernel ≤ CF * kernelBound :=
      mul_le_mul_of_nonneg_left (U.first_kernel v D) hCF.le
    unfold ActualDirectFirstSource.SecondStages.firstDivisorTailCoefficient
    calc
      _ ≤ firstAmplitude * firstTerminalFourierCost (s.charts v D).kernel * (Q * Z ^ δ) :=
        mul_le_mul_of_nonneg_left hmean'
          (mul_nonneg hfirst (firstTerminalFourierCost_nonneg _))
      _ ≤ firstAmplitude * (CF * kernelBound) * (Q * Z ^ δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hfirst)
          (mul_nonneg hQ (Real.rpow_nonneg hz.le _))
      _ = _ := by dsimp [Q, H]; ring
  have hm := hmass Z hZ centered d a t Y₁ Y₂ X hX s U.oldMask
    U.old_squarefree U.old_ne_zero U.old_divides U.column_norm U.maskIdeal
    U.mask_ne_zero U.mask_norm U.original_mask
  have hraw := R.secondTailBudget_le_original_label_sum T hZ total Cerror parentWidth loss
    firstAmplitude profileConstant fiberCap U.exponentL U.exponentR
    hC hprofile U.classes U.first_profile
  apply hraw.trans
  calc
    _ ≤ (s.fiber : ℝ) *
        ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ∑ S : divisorPool (s.pieces v D).rightData.columns
          (fun j => ((s.pieces v D).rightData.ideal j).val),
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
      simp only [ActualDirectFirstSource.firstTerminalArithmeticMass, Finset.mul_sum,
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

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.secondZeroBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.secondTailBudget_le_original_label_sum
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_second_zero_from_original_windows
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_second_tail_from_original_windows
