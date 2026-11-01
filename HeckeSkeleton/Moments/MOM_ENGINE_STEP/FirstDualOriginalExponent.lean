import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstDualCalibration

/-!
# The sharp first zero is paid from the original lengths

The coefficient contributes minus the original total length, while the
active pair count contributes that same length. The actual inverse
radius contributes the parent width minus the full support length.
These terms cancel before the independent small losses are allocated.

The powerful-counting loss is selected from a fixed upper length bound
and the desired final loss, before the actual source. The remaining
profile factor has an explicit degree fixed by the original slot cap.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

/-- This loss precedes the actual original length and moving source. -/
def firstDualCountingLoss (bound ε : ℝ) : ℝ := ε / (4 * (bound + 1))

theorem firstDualCountingLoss_pos (bound ε : ℝ) (hbound : 0 ≤ bound) (hε : 0 < ε) :
    0 < firstDualCountingLoss bound ε :=
  div_pos hε (mul_pos (by norm_num) (by linarith))

/-- The full support length is paid with its actual sign. Only the
annulus, mask-counting and powerful-counting losses remain after the
original central normalization. -/
theorem first_dual_original_length_ledger
    (total bound parentWidth supportLength loss δ ε : ℝ)
    (hbound : 0 ≤ bound) (htotal : total ≤ bound) (hsupport : 0 ≤ supportLength)
    (hlossOne : loss ≤ 1) (hloss : loss ≤ ε / 4) (hδ : δ ≤ ε / 4) (hε : 0 < ε) :
    -total + (parentWidth - supportLength) + δ + 2 * (total + loss) / 2 +
        2 * (total + loss) * firstDualCountingLoss bound ε - parentWidth ≤ ε := by
  have hden : bound + 1 ≠ 0 := ne_of_gt (by linarith)
  have hcount : 2 * (total + loss) * firstDualCountingLoss bound ε ≤ ε / 2 := by
    calc
      _ ≤ 2 * (bound + 1) * firstDualCountingLoss bound ε :=
        mul_le_mul_of_nonneg_right (by linarith)
          (firstDualCountingLoss_pos bound ε hbound hε).le
      _ = _ := by
        unfold firstDualCountingLoss
        field_simp [hden] <;> ring
  linarith

/-- The degree uses the original occurrence cap, including the two
plain profiles, before any child slots are removed. -/
def firstDualOriginalProfileDegree (cap degree : ℕ) : ℕ := 2 * (cap + 2) * degree

theorem first_dual_original_profile_constant_le
    (cap degree : ℕ) (amplitude control rowSeminorm : ℝ)
    (hamplitude : 0 ≤ amplitude) (hcontrol : 1 ≤ control) (hrow : 0 ≤ rowSeminorm)
    (hprofile : amplitude ≤ control ^ degree) :
    (2 * amplitude ^ (cap + 2)) ^ 2 * rowSeminorm ≤
      (4 * rowSeminorm) * control ^ firstDualOriginalProfileDegree cap degree := by
  have hpow := pow_le_pow_left₀ hamplitude hprofile (cap + 2)
  have hsquare := pow_le_pow_left₀ (pow_nonneg hamplitude _) hpow 2
  calc
    _ = (4 * rowSeminorm) * (amplitude ^ (cap + 2)) ^ 2 := by ring
    _ ≤ (4 * rowSeminorm) * ((control ^ degree) ^ (cap + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (mul_nonneg (by norm_num) hrow)
    _ = _ := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      congr 1
      unfold firstDualOriginalProfileDegree
      ring

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

/-- The normalized first zero follows from the literal coefficient,
active-support and radius formulas. There is no final exponent-ledger
or terminal-cost bound among the original inputs. -/
theorem normalized_zero_le_original_lengths
    (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (fiber : ℕ) (parentWidth Czero total bound supportLength loss ε : ℝ)
    (hC : 0 ≤ Czero) (hbound : 0 ≤ bound) (htotal : total ≤ bound)
    (hsupport : 0 ≤ supportLength) (hlossOne : loss ≤ 1)
    (hloss : loss ≤ ε / 4) (hδbudget : δ ≤ ε / 4) (hε : 0 < ε)
    (hcoefficient : T.zeroProfileExponent = -total)
    (hproduct : T.zeroProductExponent = 2 * (total + loss))
    (hradius : T.zeroInverseRadiusExponent ≤ parentWidth - supportLength) :
    ((fiber : ℝ) * Czero * T.zeroAmplitude hB δ hδ *
        Z ^ (T.zeroProductExponent * firstDualCountingLoss bound ε)) / Z ^ parentWidth ≤
      (fiber : ℝ) * Czero * originalFirstMaskConstant (K := K) normBound δ hB hδ *
        T.zeroProfileConstant * Z ^ ε := by
  apply T.normalized_zero_le hB δ hδ fiber parentWidth
    (firstDualCountingLoss bound ε) Czero ε hC
  have hledger := first_dual_original_length_ledger total bound parentWidth supportLength loss δ ε
    hbound htotal hsupport hlossOne hloss hδbudget hε
  unfold zeroExponent
  rw [hcoefficient, hproduct]
  linarith

end FirstDualOriginalWindows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_dual_original_length_ledger
#print axioms HeckeSkeleton.Moments.EngineStep.first_dual_original_profile_constant_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstDualOriginalWindows.normalized_zero_le_original_lengths
