import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSup
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceFourierControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerDivisorIdentity

/-!
# The literal independent source profile in the common scale majorant

Multiplication by the square root of the profile coordinate shifts its
real logarithmic exponent by one half.  This moves the normalization of
every smaller inverse scale into the fixed ideal coefficient N(I)^(-1/2).
The original independent scales U,D, cutoff coordinate, and rowwise
real/imaginary parameters remain unchanged.

The Fourier majorant is constructed from the proved pointwise decay of
the actual profile.  It is continuous, positive, and integrable, and its
constant is selected before both independent scales and all row data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualScale

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open _root_.ExpansionRecipe.LogProfile
open scoped Classical BigOperators FourierTransform ContDiff

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

def weightedLogProfile (U D a ν ξ : ℝ) : SchwartzMap ℝ ℂ :=
  actualInverseLogProfile U D (a + 1 / 2) ν ξ

theorem weightedLogProfile_eq (U D a ν ξ x : ℝ) :
    weightedLogProfile U D a ν ξ x =
      (Real.exp (x / 2) : ℂ) * actualInverseLogProfile U D a ν ξ x := by
  simp only [weightedLogProfile, actualInverseLogProfile, scaledCompactExpTwist_apply,
    linearExp, Complex.ofReal_exp]
  have he : (((a + 1 / 2 : ℝ) : ℂ) + (ν : ℂ) * Complex.I) * (x : ℂ) =
      ((x / 2 : ℝ) : ℂ) + ((a : ℂ) + (ν : ℂ) * Complex.I) * (x : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

/-- The normalization identity is evaluated on the actual positive
ideal norm coordinate; it is not an abstract profile assumption. -/
theorem weightedLogProfile_apply (u : NonzeroIdeal K) (U D a ν ξ y : ℝ)
    (hU : 0 < U) (hD : 0 ≤ D) (hy : 0 < y) :
    weightedLogProfile U D a ν ξ (Real.log y) =
      (Real.sqrt y : ℂ) * actualInverseScalarProfile K c u U D a ν ξ y := by
  rw [weightedLogProfile_eq,
    actualInverseLogProfile_apply K c u U D a ν ξ hU hD, Real.exp_log hy]
  have he : Real.exp (Real.log y / 2) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]
    congr 1
    ring
  rw [he]

theorem profile_support (u : NonzeroIdeal K) (U D a ν ξ y : ℝ)
    (hy : actualInverseScalarProfile K c u U D a ν ξ y ≠ 0) :
    1 / 2 ≤ y ∧ y ≤ 2 := by
  rw [actualInverseScalarProfile_eq] at hy
  exact annularCutoffNormTwist_support dyadicSmoothAnnularTest
    Expansion.Dyadic.cutoffProfile (D / U ^ (2 * ξ))
    ((a : ℂ) + (ν : ℂ) * Complex.I) hy

theorem weightedLogProfile_live (u : NonzeroIdeal K) (U D a ν ξ N D' : ℝ)
    (hU : 0 < U) (hD : 0 ≤ D) (hN : 0 < N) (hD' : 0 < D')
    (hF : weightedLogProfile U D a ν ξ (Real.log N - Real.log D') ≠ 0) :
    N ≤ 2 * D' := by
  rw [← Real.log_div hN.ne' hD'.ne',
    weightedLogProfile_apply K c u U D a ν ξ (N / D') hU hD (div_pos hN hD')] at hF
  have hp : actualInverseScalarProfile K c u U D a ν ξ (N / D') ≠ 0 :=
    fun hz => hF (by rw [hz, mul_zero])
  exact (div_le_iff₀ hD').mp (profile_support K c u U D a ν ξ (N / D') hp).2

theorem profileFourierTail_continuous (J : ℕ) : Continuous (profileFourierTail J) := by
  unfold profileFourierTail
  exact (continuous_const.add continuous_norm).rpow_const
    (fun t => Or.inl (by positivity : (1 + ‖t‖ : ℝ) ≠ 0))

/-- A single continuous positive kernel, with finite weighted mass, is
selected before every rowwise parameter and both original scales. -/
theorem exists_common_majorant (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T → ∃ W : ℝ → ℝ,
      (∀ t, 0 ≤ W t) ∧ Continuous W ∧ Integrable W ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * W t) ∧
      (∫ t : ℝ, (1 + ‖t‖) ^ J * W t) ≤ C * (1 + T) ^ (J + 2 : ℕ) ∧
      ∀ U : ℝ, 0 < U → ∀ D : ℝ, 0 ≤ D → ∀ a ν ξ : ℝ,
        |a| ≤ 8 → |ν| ≤ |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T) →
        ∀ t : ℝ, ‖(𝓕 (weightedLogProfile U D a ν ξ)) t‖ ≤ W t := by
  obtain ⟨C, hC, hb⟩ := scaled_common_profile_fourier_decay
    (profileLogPullback dyadicSmoothAnnularTest.toFun)
    (cutoffSchwartz Expansion.Dyadic.cutoffProfile Expansion.Dyadic.cutoffProfile_smooth
      Expansion.Dyadic.cutoffProfile_zero)
    (annular_log_compact dyadicSmoothAnnularTest) (annular_log_smooth dyadicSmoothAnnularTest)
    9 (annularLogRadius dyadicSmoothAnnularTest) |(expansionRecipeRaw K c).family.frequencyScale|
    (by norm_num) (annularLogRadius_nonneg _) (abs_nonneg _) (annular_log_support _) (J + 2)
  let mass := ∫ t : ℝ, profileFourierTail 2 t
  refine ⟨C * mass, mul_nonneg hC (integral_nonneg (profileFourierTail_nonneg 2)), ?_⟩
  intro T hT
  let W : ℝ → ℝ := fun t => (C * (1 + T) ^ (J + 2 : ℕ)) * profileFourierTail (J + 2) t
  have hweighted : (fun t : ℝ => (1 + ‖t‖) ^ J * W t) =
      fun t => (C * (1 + T) ^ (J + 2 : ℕ)) * profileFourierTail 2 t := by
    funext t
    dsimp [W]
    rw [← mul_assoc, mul_comm ((1 + ‖t‖) ^ J), mul_assoc, profileFourierTail_weighted]
  refine ⟨W, fun t => mul_nonneg (by positivity) (profileFourierTail_nonneg _ _),
    (profileFourierTail_continuous (J + 2)).const_mul _,
    (profileFourierTail_integrable (J + 2) (by omega)).const_mul _, ?_, ?_, ?_⟩
  · rw [hweighted]
    exact (profileFourierTail_integrable 2 (by norm_num)).const_mul _
  · rw [hweighted, integral_const_mul]
    exact le_of_eq (by dsimp [mass]; ring)
  · intro U hU D hD a ν ξ ha hν t
    have ha' : |a + 1 / 2| ≤ 9 := by
      have hab := abs_add_le a (1 / 2 : ℝ)
      norm_num at hab
      linarith
    simpa only [weightedLogProfile, actualInverseLogProfile, Real.rpow_natCast] using
      hb T hT (D / U ^ (2 * ξ)) (div_nonneg hD (Real.rpow_pos_of_pos hU _).le)
        (((a + 1 / 2 : ℝ) : ℂ) + (ν : ℂ) * Complex.I)
        (by simpa using ha') (by simpa using hν) t

variable {K c} {ω ψ : HeckeCharacter K}

def normWeightedCoefficient (d : MomentData K ω ψ) (u I : NonzeroIdeal K) : ℂ :=
  inverseRowCoefficient d u I * (Real.sqrt (idealNorm K I) : ℂ)⁻¹

/-- Exact transfer of the inverse square-root factor.  The real shifts
and cutoff coordinate belong to the original source and stay fixed. -/
theorem normalized_term (d : MomentData K ω ψ) (u I : NonzeroIdeal K)
    (U D a ν ξ D' : ℝ) (hU : 0 < U) (hD : 0 ≤ D) (hD' : 0 < D') :
    (Real.sqrt D' : ℂ)⁻¹ *
        (inverseRowCoefficient d u I *
          actualInverseScalarProfile K c u U D a ν ξ (idealNorm K I / D')) =
      normWeightedCoefficient d u I *
        weightedLogProfile U D a ν ξ (Real.log (idealNorm K I) - Real.log D') := by
  have hN := idealNorm_pos K I
  rw [← Real.log_div hN.ne' hD'.ne',
    weightedLogProfile_apply K c u U D a ν ξ _ hU hD (div_pos hN hD'),
    Real.sqrt_div hN.le, Complex.ofReal_div]
  unfold normWeightedCoefficient
  have hsn : (Real.sqrt (idealNorm K I) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hN).ne'
  have hsd : (Real.sqrt D' : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hD').ne'
  field_simp

/-- The genuine ideal polynomial is the fixed-prefix integral.  Its
support is enlarged only to the explicit ideal-norm ball; all added
terms vanish by the original exact support specification. -/
theorem inversePolynomial_eq_prefix_integral (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (U D a ν ξ D' : ℝ) (L : ℕ)
    (hU : 0 < U) (hD : 0 ≤ D) (hD' : 0 < D')
    (hscale : 2 * D' ≤ (2 : ℝ) ^ L)
    (hprofile : d.inverseTest.profile u 0 = actualInverseScalarProfile K c u U D a ν ξ) :
    inversePolynomial d u D' 0 =
      ∫ t : ℝ, (𝓕 (weightedLogProfile U D a ν ξ)) t *
        HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel.columnPhase t (-Real.log D') *
        SourceScaleSup.prefixColumn (dyadicIdealSupport K (8 * (2 : ℝ) ^ L))
          (normWeightedCoefficient d u) (idealNorm K) L t := by
  let T := dyadicIdealSupport K (8 * (2 : ℝ) ^ L)
  let F := weightedLogProfile U D a ν ξ
  have hs : d.inverseTest.support u 0 D' ⊆ T := by
    intro I hI
    have hp := (d.inverseTest.support_spec u 0 D' I).mp hI
    rw [hprofile] at hp
    have hn := (div_le_iff₀ hD').mp (profile_support K c u U D a ν ξ _ hp).2
    apply (mem_dyadicIdealSupport_iff K (by positivity) I).mpr
    exact (hn.trans hscale).trans (by have : (0 : ℝ) ≤ 2 ^ L := by positivity; linarith)
  calc
    _ = ∑ I ∈ d.inverseTest.support u 0 D', normWeightedCoefficient d u I *
        F (Real.log (idealNorm K I) - Real.log D') := by
      rw [inversePolynomial_sum_coeff, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      rw [hprofile]
      exact normalized_term d u I U D a ν ξ D' hU hD hD'
    _ = ∑ I ∈ T, normWeightedCoefficient d u I *
        F (Real.log (idealNorm K I) - Real.log D') := by
      apply Finset.sum_subset hs
      intro I hI hnot
      have hp : actualInverseScalarProfile K c u U D a ν ξ (idealNorm K I / D') = 0 := by
        by_contra hp
        apply hnot
        apply (d.inverseTest.support_spec u 0 D' I).mpr
        simpa only [hprofile] using hp
      dsimp only [F]
      rw [← Real.log_div (idealNorm_pos K I).ne' hD'.ne',
        weightedLogProfile_apply K c u U D a ν ξ _ hU hD
          (div_pos (idealNorm_pos K I) hD'), hp, mul_zero, mul_zero]
    _ = _ := SourceScaleSup.shifted_profile_eq_prefix_integral
      T (normWeightedCoefficient d u) (idealNorm K) F L D'
      (fun I hI hF => (weightedLogProfile_live K c u U D a ν ξ
        (idealNorm K I) D' hU hD (idealNorm_pos K I) hD' hF).trans hscale)

/-- The same constructed row bound controls all positive smaller scales
simultaneously.  The independent original scales and row profile are fixed
before D' varies. -/
theorem inversePolynomial_sq_le_rowMajorant (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (U D a ν ξ : ℝ) (L : ℕ)
    (hU : 0 < U) (hD : 0 ≤ D)
    (hprofile : d.inverseTest.profile u 0 = actualInverseScalarProfile K c u U D a ν ξ)
    (W : ℝ → ℝ) (hW0 : ∀ t, 0 ≤ W t) (cW : Continuous W) (iW : Integrable W)
    (hF : ∀ t, ‖(𝓕 (weightedLogProfile U D a ν ξ)) t‖ ≤ W t) :
    ∀ D' : ℝ, 0 < D' → 2 * D' ≤ (2 : ℝ) ^ L →
      ‖inversePolynomial d u D' 0‖ ^ 2 ≤
        SourceScaleSup.rowMajorant (dyadicIdealSupport K (8 * (2 : ℝ) ^ L))
          (normWeightedCoefficient d u) (idealNorm K) L W := by
  intro D' hD' hscale
  rw [inversePolynomial_eq_prefix_integral d u U D a ν ξ D' L hU hD hD' hscale hprofile]
  let T := dyadicIdealSupport K (8 * (2 : ℝ) ^ L)
  have hkeep : ∀ I ∈ T,
      weightedLogProfile U D a ν ξ (Real.log (idealNorm K I) - Real.log D') ≠ 0 →
        idealNorm K I ≤ (2 : ℝ) ^ L := by
    intro I hI hlive
    exact (weightedLogProfile_live K c u U D a ν ξ
      (idealNorm K I) D' hU hD (idealNorm_pos K I) hD' hlive).trans hscale
  have hb := SourceScaleSup.shifted_profile_sq_le T (normWeightedCoefficient d u)
    (idealNorm K) (weightedLogProfile U D a ν ξ) L D' hkeep W hW0 cW iW hF
  rw [SourceScaleSup.shifted_profile_eq_prefix_integral T (normWeightedCoefficient d u)
    (idealNorm K) (weightedLogProfile U D a ν ξ) L D' hkeep] at hb
  exact hb

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualScale

end
