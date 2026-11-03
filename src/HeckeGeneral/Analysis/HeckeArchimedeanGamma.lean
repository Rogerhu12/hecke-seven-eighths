import HeckeGeneral.Analysis.ArchimedeanGamma
import HeckeGeneral.Characters.InfinityPacket

/-!+# Gamma multipliers with actual Hecke infinity parameters

This specializes the explicit Gamma product to the integer weights and real
frequencies extracted from an actual Hecke character. Finite-order children
have the same multiplier; a global norm twist gives the exact vertical shift.
This identifies the local expression without assuming its occurrence in a
theta-period identity.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Characters
open scoped BigOperators Classical

theorem angularGammaArgument_frequency_shift (m : ℤ) (τ t : ℝ) (b : Bool) (s : ℂ) :
    angularGammaArgument m (τ - t) b s = angularGammaArgument m τ b (s - (t : ℂ) * Complex.I) := by
  unfold angularGammaArgument
  push_cast
  ring

theorem localGammaRatio_frequency_shift (m : ℤ) (τ t : ℝ) (b : Bool) (s : ℂ) :
    localGammaRatio m (τ - t) b s = localGammaRatio m τ b (s - (t : ℂ) * Complex.I) := by
  unfold localGammaRatio
  rw [angularGammaArgument_frequency_shift]
  congr 2
  unfold angularGammaArgument
  push_cast
  ring

theorem complexPlaceGammaRatio_frequency_shift (m : ℤ) (τ t : ℝ) (s : ℂ) :
    complexPlaceGammaRatio m (τ - t) s =
      complexPlaceGammaRatio m τ (s - (t : ℂ) * Complex.I) := by
  unfold complexPlaceGammaRatio
  simp only [localGammaRatio_frequency_shift]

theorem archimedeanGammaRatio_frequency_shift {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (τ : ι → ℝ) (t : ℝ) (s : ℂ) :
    archimedeanGammaRatio m (fun v => τ v - t) s =
      archimedeanGammaRatio m τ (s - (t : ℂ) * Complex.I) := by
  unfold archimedeanGammaRatio
  simp only [complexPlaceGammaRatio_frequency_shift]

variable (K : Type*) [Field K] [NumberField K]

/-- Only the actual complex places are indexed; no totally complex hypothesis is inserted. -/
def heckeArchimedeanGammaRatio (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  archimedeanGammaRatio
    (fun v : {v : InfinitePlace K // v.IsComplex} => heckeComplexWeight K v.val v.property χ)
    (fun v : {v : InfinitePlace K // v.IsComplex} => heckeComplexParameter K v.val v.property χ) s

theorem analyticAt_heckeArchimedeanGammaRatio (χ : HeckeCharacter K) {s : ℂ}
    (hs : -(1 / 3) < s.re) : AnalyticAt ℂ (heckeArchimedeanGammaRatio K χ) s :=
  analyticAt_archimedeanGammaRatio _ _ hs

theorem heckeArchimedeanGammaRatio_ne_zero (χ : HeckeCharacter K) {s : ℂ}
    (hl : -(1 / 3) < s.re) (hr : s.re < 1 / 3) :
    heckeArchimedeanGammaRatio K χ s ≠ 0 := archimedeanGammaRatio_ne_zero _ _ hl hr

theorem norm_heckeArchimedeanGammaRatio_imaginary (χ : HeckeCharacter K) (t : ℝ) :
    ‖heckeArchimedeanGammaRatio K χ ((t : ℂ) * Complex.I)‖ = 1 :=
  norm_archimedeanGammaRatio_imaginary _ _ t

/-- Finite-order twisting leaves every factor in this actual infinity-type product unchanged. -/
theorem heckeArchimedeanGammaRatio_finiteOrder_twist (χ θ : HeckeCharacter K)
    (hθ : FiniteOrder θ) (s : ℂ) :
    heckeArchimedeanGammaRatio K (θ * χ) s = heckeArchimedeanGammaRatio K χ s := by
  unfold heckeArchimedeanGammaRatio archimedeanGammaRatio
  apply Finset.prod_congr rfl
  intro v _
  dsimp only
  rw [heckeComplexWeight_mul, heckeComplexParameter_mul,
    heckeComplexWeight_finiteOrder K v.val v.property hθ,
    heckeComplexParameter_finiteOrder K v.val v.property hθ, zero_add, zero_add]

/-- The vertical shift follows from the actual normalized idelic norm at each place. -/
theorem heckeArchimedeanGammaRatio_normTwist (χ : HeckeCharacter K) (t : ℝ) (s : ℂ) :
    heckeArchimedeanGammaRatio K (χ * heckeNormTwist K t) s =
      heckeArchimedeanGammaRatio K χ (s - (t : ℂ) * Complex.I) := by
  unfold heckeArchimedeanGammaRatio archimedeanGammaRatio
  apply Finset.prod_congr rfl
  intro v _
  dsimp only
  rw [heckeComplexWeight_mul, heckeComplexParameter_mul,
    heckeComplexWeight_normTwist, heckeComplexParameter_normTwist, add_zero]
  exact complexPlaceGammaRatio_frequency_shift _ _ t s

/-- Later finite-order children and norm heights share one fixed local Gamma expression. -/
theorem heckeArchimedeanGammaRatio_child (χ θ : HeckeCharacter K) (hθ : FiniteOrder θ)
    (t : ℝ) (s : ℂ) :
    heckeArchimedeanGammaRatio K (θ * χ * heckeNormTwist K t) s =
      heckeArchimedeanGammaRatio K χ (s - (t : ℂ) * Complex.I) := by
  rw [heckeArchimedeanGammaRatio_normTwist, heckeArchimedeanGammaRatio_finiteOrder_twist K χ θ hθ]

end HeckeGeneral.Analysis
