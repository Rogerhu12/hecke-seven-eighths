import ThetaGlobal.FiniteActualProfiles
import ThetaGlobal.NormSheetTensorBounds
import ThetaGlobal.PositiveAxisLog
import HeckeSkeleton.SixthLocalFinite

/-!
# The actual normalized sheet pair supplies annular-transfer profiles

All fields are derived from the same source's literal tensor and Haar
integrals.  In particular global continuity and uniform logarithmic
quadratic tails are conclusions of the one-coordinate norm-sheet bound.
The only analytic inputs are the displayed per-place high K-type data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.ActualAnnularProfiles

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FiniteLocalHighK ThetaGlobal.FiniteSheetMellin
open ThetaGlobal.ProjectedFiniteIntegral ThetaGlobal.PositiveAxisLog
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (θ : HeckeCharacter F)
variable (C : FiniteFixedSource.Source R θ) (L : Input R θ C)

local notation "Sf" => (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local notation "D" => C.projected.base.factorization
local notation "MT" => finiteMellinData R θ C L

local instance : Finite (SixthLocalClasses F Sf) := by
  letI := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  exact HeckeSkeleton.SixthLocalFinite.sixthLocalClasses_finite F Sf

private theorem weighted_bound {E : Type*} [NormedField E]
    (a : Eˣ → ℂ) (B : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ B * (‖z.val‖ ^ 2 : ℝ) ^ (-(2 : ℝ))) :
    ∀ z, ‖a z * ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ (2 : ℂ)‖ ≤ B := by
  intro z
  have hz : 0 < ‖z.val‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr z.ne_zero)
  rw [norm_mul, Complex.cpow_ofNat, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hz.le]
  calc
    _ ≤ (B * (‖z.val‖ ^ 2 : ℝ) ^ (-(2 : ℝ))) * (‖z.val‖ ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (ha z) (sq_nonneg _)
    _ = B := by
      rw [Real.rpow_neg hz.le, Real.rpow_two, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 2 hz.ne'), mul_one]

private theorem direct_finite_weight :
    NormSheetTensorBounds.weightedFinite R
      (FiniteDirectMellin.cutoffProduct R C.projected.cutoffs) 2 =
      FiniteDirectMellin.cutoffProduct R C.projected.cutoffs := by
  funext z
  exact Eq.trans (mul_comm _ _)
    (FiniteDirectMellin.cutoffProduct_norm_power R C.projected.cutoffs 2 z)

private theorem reflected_finite_weight (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F Sf) :
    NormSheetTensorBounds.weightedFinite R
      (finiteMellinIntegrand R D θ u κ 0) 2 =
      finiteMellinIntegrand R D θ u κ 2 := by
  funext z
  simp only [NormSheetTensorBounds.weightedFinite, finiteMellinIntegrand,
    Complex.cpow_zero, mul_one]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  ring

theorem direct_continuous_and_bound (v₀ : InfinitePlace F) :
    Continuous (FiniteNormalizedMellin.direct R θ C L v₀) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t : PositiveAxis,
        ‖FiniteNormalizedMellin.direct R θ C L v₀ t‖ ≤ B * (t.val ^ 2)⁻¹ := by
  obtain ⟨B, hB, hb⟩ := L.direct_bound v₀ 2 (by norm_num)
  have hfi : Integrable (NormSheetTensorBounds.weightedFinite R
      (FiniteDirectMellin.cutoffProduct R C.projected.cutoffs) 2)
      (Measure.pi C.transport.finiteMultHaar) := by
    rw [direct_finite_weight]
    exact FiniteDirectMellin.cutoffProduct_integrable R C.transport C.projected.cutoffs
  exact NormSheetTensorBounds.sheet_continuous_and_bound R C.transport
    (reflectedConstant R θ C L)⁻¹ (FiniteNormalizedMellin.archProfile R θ C L false)
    (FiniteDirectMellin.cutoffProduct R C.projected.cutoffs) v₀
    (fun w => localProfile_continuous R θ (L.functional w) (L.vector w) w false)
    (FiniteDirectMellin.cutoffProduct_continuous R C.projected.cutoffs)
    (fun w => L.direct_integrable w 2 (by norm_num)) hfi B hB (weighted_bound _ B hb)

theorem reflected_continuous_and_bound (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F Sf) (v₀ : InfinitePlace F) :
    Continuous (FiniteNormalizedMellin.reflected R θ C L u κ v₀) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t : PositiveAxis,
        ‖FiniteNormalizedMellin.reflected R θ C L u κ v₀ t‖ ≤ B * (t.val ^ 2)⁻¹ := by
  obtain ⟨B, hB, hb⟩ := L.reflected_bound v₀ 2 (by norm_num)
  have hfi : Integrable (NormSheetTensorBounds.weightedFinite R
      (finiteMellinIntegrand R D θ u κ 0) 2)
      (Measure.pi C.transport.finiteMultHaar) := by
    rw [reflected_finite_weight]
    exact (class_series_integral R D C.transport θ C.projected.cutoffs u κ 2
      (by norm_num)).1
  exact NormSheetTensorBounds.sheet_continuous_and_bound R C.transport
    (reflectedConstant R θ C L)⁻¹ (FiniteNormalizedMellin.archProfile R θ C L true)
    (finiteMellinIntegrand R D θ u κ 0) v₀
    (fun w => localProfile_continuous R θ (L.functional w) (L.vector w) w true)
    (finiteMellinIntegrand_continuous R D θ C.projected.cutoffs u κ 0)
    (fun w => L.reflected_integrable w 2 (by norm_num)) hfi B hB (weighted_bound _ B hb)

def directLog (v₀ : InfinitePlace F) (x : ℝ) : ℂ :=
  FiniteNormalizedMellin.direct R θ C L v₀ (logEquiv.symm x)

def reflectedLog (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (v₀ : InfinitePlace F) (x : ℝ) : ℂ :=
  FiniteNormalizedMellin.reflected R θ C L u κ v₀ (logEquiv.symm x)

def directSpectrum (t : ℝ) : ℂ :=
  GammaDeconvolver.directGamma (GammaDeconvolverProject.actualProfile F Sf MT θ)
    ((t : ℂ) * Complex.I)

theorem directLog_mellin (v₀ : InfinitePlace F) (t : ℝ) :
    ScalarMellinConvolution.positiveSpectrum (directLog R θ C L v₀) t =
      directSpectrum R θ C L t := by
  show ScalarMellinConvolution.positiveSpectrum
    (fun x => FiniteNormalizedMellin.direct R θ C L v₀ (logEquiv.symm x)) t = _
  rw [positiveSpectrum_eq_mellin]
  exact FiniteActualProfiles.direct_mellin_eq_gamma R θ C L v₀
    ((t : ℂ) * Complex.I) (by first | norm_num | simp)

theorem directSpectrum_ne_zero (t : ℝ) : directSpectrum R θ C L t ≠ 0 :=
  GammaDeconvolver.directGamma_imaginary_ne_zero _ t

theorem reflectedLog_mellin (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F Sf) (v₀ : InfinitePlace F) (t : ℝ) :
    ScalarMellinConvolution.positiveSpectrum (reflectedLog R θ C L u κ v₀) t =
      directSpectrum R θ C L (-t) * reflectionMultiplier F Sf MT θ u κ
        ((t : ℂ) * Complex.I) := by
  show ScalarMellinConvolution.positiveSpectrum
    (fun x => FiniteNormalizedMellin.reflected R θ C L u κ v₀ (logEquiv.symm x)) t = _
  rw [positiveSpectrum_eq_mellin]
  have h := FiniteNormalizedMellin.mellin_ratio R θ C L u κ v₀
    ((t : ℂ) * Complex.I) (by first | norm_num | simp) (by first | norm_num | simp)
  rw [FiniteActualProfiles.direct_mellin_eq_gamma R θ C L v₀
    (-((t : ℂ) * Complex.I)) (by first | norm_num | simp)] at h
  have he : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by simp
  rw [he] at h
  exact ((div_eq_iff (directSpectrum_ne_zero R θ C L (-t))).mp h).trans (mul_comm _ _)

/-- Every scalar-transfer field is now attached to the actual source and
its actual finite table.  No global theta identity is a field or input. -/
def localProfiles (u : R.A.UnitQuotient) (v₀ : InfinitePlace F) :
    AnnularTransfer.LocalProfiles (SixthLocalClasses F Sf) := by
  classical
  letI : Fintype (SixthLocalClasses F Sf) := Fintype.ofFinite _
  have hd := direct_continuous_and_bound R θ C L v₀
  let Bd : ℝ := Classical.choose hd.2
  have hBd : 0 ≤ Bd := (Classical.choose_spec hd.2).1
  have hdb : ∀ t : PositiveAxis,
      ‖FiniteNormalizedMellin.direct R θ C L v₀ t‖ ≤ Bd * (t.val ^ 2)⁻¹ :=
    (Classical.choose_spec hd.2).2
  have hr := reflected_continuous_and_bound R θ C L u
  let Br : SixthLocalClasses F Sf → ℝ := fun κ => Classical.choose (hr κ v₀).2
  have hBr (κ : SixthLocalClasses F Sf) : 0 ≤ Br κ :=
    (Classical.choose_spec (hr κ v₀).2).1
  have hrb (κ : SixthLocalClasses F Sf) : ∀ t : PositiveAxis,
      ‖FiniteNormalizedMellin.reflected R θ C L u κ v₀ t‖ ≤ Br κ * (t.val ^ 2)⁻¹ :=
    (Classical.choose_spec (hr κ v₀).2).2
  have hdi : Integrable (FiniteNormalizedMellin.direct R θ C L v₀) positiveHaar := by
    simpa only [Complex.cpow_zero, one_mul] using
      FiniteActualProfiles.direct_weighted_integrable R θ C L v₀ 0 (by norm_num)
  have hri (κ : SixthLocalClasses F Sf) :
      Integrable (FiniteNormalizedMellin.reflected R θ C L u κ v₀) positiveHaar := by
    simpa only [Complex.cpow_zero, one_mul] using
      FiniteActualProfiles.reflected_weighted_integrable R θ C L u κ v₀ 0 (by norm_num)
  refine
    { direct := directLog R θ C L v₀
      reflected := fun κ => reflectedLog R θ C L u κ v₀
      M := directSpectrum R θ C L
      R := fun κ (t : ℝ) => reflectionMultiplier F Sf MT θ u κ ((t : ℂ) * Complex.I)
      direct_continuous := hd.1.comp logEquiv.symm.continuous
      reflected_continuous := fun κ => (hr κ v₀).1.comp logEquiv.symm.continuous
      direct_integrable := (integrable_exp_iff _).mpr hdi
      reflected_integrable := fun κ => (integrable_exp_iff _).mpr (hri κ)
      direct_mellin := directLog_mellin R θ C L v₀
      reflected_mellin := (reflectedLog_mellin R θ C L u · v₀)
      M_ne_zero := directSpectrum_ne_zero R θ C L
      exponent := 2
      directBound := Bd
      reflectedBound := ∑ κ, Br κ
      direct_tail := ?_
      reflected_tail := ?_ }
  · intro x
    have hb := hdb (logEquiv.symm x)
    change ‖directLog R θ C L v₀ x‖ ≤ Bd * ((Real.exp x) ^ 2)⁻¹ at hb
    simpa only [exp_inverse_sq] using hb
  · intro κ x
    have hb := hrb κ (logEquiv.symm x)
    have hBr' : Br κ ≤ ∑ κ', Br κ' :=
      Finset.single_le_sum (fun κ' _ => hBr κ') (Finset.mem_univ κ)
    exact hb.trans (by
      change Br κ * ((Real.exp x) ^ 2)⁻¹ ≤ _
      rw [exp_inverse_sq]
      exact mul_le_mul_of_nonneg_right hBr' (Real.exp_pos _).le)

@[simp] theorem localProfiles_direct (u : R.A.UnitQuotient) (v₀ : InfinitePlace F) :
    (localProfiles R θ C L u v₀).direct = directLog R θ C L v₀ := rfl

@[simp] theorem localProfiles_reflected (u : R.A.UnitQuotient) (v₀ : InfinitePlace F) :
    (localProfiles R θ C L u v₀).reflected =
      fun κ => reflectedLog R θ C L u κ v₀ := rfl

@[simp] theorem localProfiles_M (u : R.A.UnitQuotient) (v₀ : InfinitePlace F) :
    (localProfiles R θ C L u v₀).M = directSpectrum R θ C L := rfl

@[simp] theorem localProfiles_R (u : R.A.UnitQuotient) (v₀ : InfinitePlace F) :
    (localProfiles R θ C L u v₀).R =
      fun κ (t : ℝ) => reflectionMultiplier F Sf MT θ u κ ((t : ℂ) * Complex.I) := rfl

@[simp] theorem localProfiles_exponent (u : R.A.UnitQuotient) (v₀ : InfinitePlace F) :
    (localProfiles R θ C L u v₀).exponent = 2 := rfl

end ThetaGlobal.ActualAnnularProfiles

#print axioms ThetaGlobal.ActualAnnularProfiles.direct_continuous_and_bound
#print axioms ThetaGlobal.ActualAnnularProfiles.reflected_continuous_and_bound
#print axioms ThetaGlobal.ActualAnnularProfiles.localProfiles
