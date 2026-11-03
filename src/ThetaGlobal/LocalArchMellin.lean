import ThetaGlobal.LocalArchProfile
import ThetaGlobal.LocalArchHaar

/-!
# Mellin formulas for the actual normalized high K-type coefficient

The inverse-character root vector is evaluated by the actual Jacquet
functional. Its normalization and the source's angular Haar mass appear
explicitly in the two local Mellin constants.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace ThetaGlobal.LocalArchMellin

open MeasureTheory NumberField DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open KPCplxJacquetFunctional KPCplxBessel FourierContinuation.ComplexLines
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ThetaLocal ThetaPositiveSheetMellin
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (θ : HeckeCharacter F)
variable (N : TraceHaarTransport R)

def directConstant (w : InfinitePlace F) : ℂ :=
  ((N.angularHaar w Set.univ).toReal : ℂ) *
    archDirectConstant (4 * Real.pi)
      (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)
      (heckeComplexParameter F w (R.A.complex_place w) θ⁻¹) /
    (besselKThird (4 * Real.pi) : ℂ)

def reflectedConstant (w : InfinitePlace F) : ℂ :=
  ((N.angularHaar w Set.univ).toReal : ℂ) *
    archReflectedConstant (4 * Real.pi)
      (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)
      (heckeComplexParameter F w (R.A.complex_place w) θ⁻¹) /
    (besselKThird (4 * Real.pi) : ℂ)

theorem angular_mass_pos (w : InfinitePlace F) :
    0 < (N.angularHaar w Set.univ).toReal := by
  letI := N.angularHaar_isHaar
  exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ Set.univ_nonempty)
    isCompact_univ.measure_ne_top

theorem directConstant_nonzero (w : InfinitePlace F) : directConstant R θ N w ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (angular_mass_pos R N w).ne')
      (archDirectConstant_ne_zero _ (by positivity) _ _))
    (Complex.ofReal_ne_zero.mpr (besselKThird_pos _ (by positivity)).ne')

theorem reflectedConstant_nonzero (w : InfinitePlace F) :
    reflectedConstant R θ N w ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (angular_mass_pos R N w).ne')
      (archReflectedConstant_ne_zero _ (by positivity) _ _))
    (Complex.ofReal_ne_zero.mpr (besselKThird_pos _ (by positivity)).ne')

theorem localGamma_inv_eq_directGammaPair (w : InfinitePlace F) (s : ℂ) :
    HeckeSkeleton.ThetaLocal.Project.localGamma F θ⁻¹ ⟨w, R.A.complex_place w⟩ s =
      FiniteLocalHighK.directGammaPair R θ w s := by
  simp only [HeckeSkeleton.ThetaLocal.Project.localGamma, archGammaPair,
    FiniteLocalHighK.directGammaPair,
    HeckeSkeleton.ThetaLocal.Project.archShift_inv,
    HeckeSkeleton.ThetaLocal.Project.archRadial_inv,
    Complex.ofReal_neg, mul_neg, sub_eq_add_neg]
  ring

theorem localGamma_eq_gammaPair (w : InfinitePlace F) (s : ℂ) :
    HeckeSkeleton.ThetaLocal.Project.localGamma F θ ⟨w, R.A.complex_place w⟩ s =
      FiniteLocalHighK.gammaPair R θ w s := by
  unfold HeckeSkeleton.ThetaLocal.Project.localGamma archGammaPair FiniteLocalHighK.gammaPair
  ring

private theorem hasMellin_div_const (f : ℝ → ℂ) (s a m : ℂ)
    (hf : HasMellin f s m) : HasMellin (fun t => f t / a) s (m / a) := by
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hf.1.const_smul a⁻¹
  · rw [mellin_div_const, hf.2]

theorem direct_mellin (w : InfinitePlace F) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Integrable (fun z : w.Completionˣ =>
      FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
        (LocalArchProfile.vector R θ w) w false z * ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s)
      (archHaar R.A w (N.angularHaar w)) ∧
    (∫ z : w.Completionˣ,
      FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
        (LocalArchProfile.vector R θ w) w false z * ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s
      ∂archHaar R.A w (N.angularHaar w)) =
      directConstant R θ N w * (archScale (4 * Real.pi) : ℂ) ^ s *
        FiniteLocalHighK.directGammaPair R θ w s := by
  letI := N.angularHaar_isHaar
  have hm := HeckeSkeleton.ThetaLocal.Project.directProfile_hasMellin F θ⁻¹
    ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (by positivity) s hs
  rw [localGamma_inv_eq_directGammaPair R θ w s] at hm
  have hd := hasMellin_div_const _ s (besselKThird (4 * Real.pi) : ℂ) _ hm
  have hh := LocalArchHaar.radial_hasMellin R.A w (N.angularHaar w) _ s _ hd
  simp only [LocalArchHaar.normSq] at hh
  simp_rw [LocalArchProfile.direct_profile]
  refine ⟨hh.1, hh.2.trans ?_⟩
  unfold directConstant
  ring

theorem reflected_mellin (w : InfinitePlace F) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Integrable (fun z : w.Completionˣ =>
      FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
        (LocalArchProfile.vector R θ w) w true z * ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s)
      (archHaar R.A w (N.angularHaar w)) ∧
    (∫ z : w.Completionˣ,
      FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
        (LocalArchProfile.vector R θ w) w true z * ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s
      ∂archHaar R.A w (N.angularHaar w)) =
      reflectedConstant R θ N w * (archScale (4 * Real.pi) : ℂ) ^ s *
        FiniteLocalHighK.gammaPair R θ w s := by
  letI := N.angularHaar_isHaar
  have hm := HeckeSkeleton.ThetaLocal.Project.reflectedProfile_hasMellin F θ⁻¹
    ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (by positivity) s hs
  rw [inv_inv, localGamma_eq_gammaPair R θ w s] at hm
  have hd := hasMellin_div_const _ s (besselKThird (4 * Real.pi) : ℂ) _ hm
  have hh := LocalArchHaar.radial_hasMellin R.A w (N.angularHaar w) _ s _ hd
  simp only [LocalArchHaar.normSq] at hh
  simp_rw [LocalArchProfile.reflected_profile]
  refine ⟨hh.1, hh.2.trans ?_⟩
  unfold reflectedConstant
  ring

end ThetaGlobal.LocalArchMellin

#print axioms ThetaGlobal.LocalArchMellin.directConstant_nonzero
#print axioms ThetaGlobal.LocalArchMellin.reflectedConstant_nonzero
#print axioms ThetaGlobal.LocalArchMellin.direct_mellin
#print axioms ThetaGlobal.LocalArchMellin.reflected_mellin
