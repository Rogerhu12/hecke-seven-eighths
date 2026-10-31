import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionDecay

/-!
# A common reflected-profile bound for actual finite-order row characters

The reflected Gamma/Mellin profile depends only on the infinity type.
Over a totally complex field a finite-order row character contributes zero
radial parameters and zero angular weights.  Thus the exact reflected
profile of background times row equals the background's profile, and the
decay constant and finite Euler order are selected before every row.

The row's finite conductor occurs only in the physical dual scale of the
reflection identity; it is absent from the constants proved here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

theorem ordinaryGammaRatio_eq_of_type (χ η : HeckeCharacter K)
    (hτ : (fun v => heckeRadialParameter K v χ) = (fun v => heckeRadialParameter K v η))
    (hm : heckeArchWeight K χ = heckeArchWeight K η) (s : ℂ) :
    ordinaryGammaRatio K χ s = ordinaryGammaRatio K η s := by
  unfold ordinaryGammaRatio
  rw [canonicalHeckeGammaProfile_inv K χ (1 - s),
    canonicalHeckeGammaProfile_inv K η (1 - s)]
  simp only [canonicalHeckeGammaProfile, hτ, hm]

theorem ordinaryReflectedProfile_eq_of_type (χ η : HeckeCharacter K)
    (hτ : (fun v => heckeRadialParameter K v χ) = (fun v => heckeRadialParameter K v η))
    (hm : heckeArchWeight K χ = heckeArchWeight K η)
    (V : SmoothAnnularTest) (δ y : ℝ) :
    ordinaryReflectedProfile K χ V δ y = ordinaryReflectedProfile K η V δ y := by
  have hk : ordinaryReflectionKernel K χ V δ = ordinaryReflectionKernel K η V δ := by
    funext t
    change mellin V.toFun (1 - idealVerticalPoint (1 + δ) t) *
        ordinaryGammaRatio K χ (1 - idealVerticalPoint (1 + δ) t) =
      mellin V.toFun (1 - idealVerticalPoint (1 + δ) t) *
        ordinaryGammaRatio K η (1 - idealVerticalPoint (1 + δ) t)
    rw [ordinaryGammaRatio_eq_of_type K χ η hτ hm]
  simp only [ordinaryReflectedProfile, hk]

/-- Actual finite-order rows preserve the entire reflected profile,
not merely a bound on that profile. -/
theorem ordinaryReflectedProfile_mul_finiteOrder
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (β χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (V : SmoothAnnularTest) (δ y : ℝ) :
    ordinaryReflectedProfile K (β * χ) V δ y = ordinaryReflectedProfile K β V δ y := by
  apply ordinaryReflectedProfile_eq_of_type K (β * χ) β
  · funext v
    rw [heckeRadialParameter_mul, heckeRadialParameter_finiteOrder K v hχ, add_zero]
  · funext v
    rw [heckeArchWeight_of_complex K (β * χ) v (hcomplex v),
      heckeArchWeight_of_complex K β v (hcomplex v), heckeComplexWeight_mul,
      heckeComplexWeight_finiteOrder K v (hcomplex v) hχ, add_zero]

/-- C and J precede every moving arithmetic row, profile and dual norm
ratio.  In particular no per-row constant is selected after the row sum. -/
theorem ordinaryReflectedProfile_finiteRow_uniform_decay
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (β : HeckeCharacter K) {δ A : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : HeckeCharacter K, FiniteOrder χ →
      ∀ V : SmoothAnnularTest, ∀ y : ℝ, 0 < y →
      ‖ordinaryReflectedProfile K (β * χ) V δ y‖ ≤
        C * testSeminorm V.toFun J A * y ^ (-(1 + A)) := by
  obtain ⟨J, C, hC, hbound⟩ := ordinaryReflectedProfile_decay_seminorm K hcomplex β hδ hδA
  refine ⟨J, C, hC, ?_⟩
  intro χ hχ V y hy
  rw [ordinaryReflectedProfile_mul_finiteOrder K hcomplex β χ hχ]
  exact hbound V y hy

end HeckeSkeleton.Moments.EngineInduction
