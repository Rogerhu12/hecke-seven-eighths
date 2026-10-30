module

public import ThetaGlobal.GammaProfileGrowth
public import ThetaGlobal.RegularizedTestProject

/-!
# Concrete archimedean parameters for the scalar deconvolver

This adapter uses the actual period character's archShift and archRadial,
and the actual finite table's normalization constants. Its normalized direct
Gamma expression has the negative radial parameter, as required by the
denominator of reflectionMultiplier. Identifying it with a measured direct
profile remains the separate local Mellin-pair specification: if F.C₀ is
the ratio vol(U) * Cdirect / Creflected, both actual seed profiles are first
divided by the common nonzero scalar W_x(1) * Creflected. No equality with
an unnormalized sheet integral is asserted
by this adapter. The annular Mellin transform's entire nature and
boundedness on every fixed strip are proved from the existing test estimates.
The reciprocal-Gamma strip bound is proved by Euler reflection and compactness.

This imports the original project and is outside the Mathlib-only bundle.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaDeconvolverProject

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open GammaDeconvolver GaussianStripDecay DeconvolverMoments
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (F : FiniteMellinData K S) (θ : HeckeCharacter K)

/-- Both sixth offsets at each actual complex place, with the finite table's
normalized direct constant. The radial sign is the opposite of the numerator
sign in reflectionMultiplier. -/
def actualProfile : GammaProfile ({v : InfinitePlace K // v.IsComplex} × Bool) where
  C₀ := F.C₀
  C₀_ne_zero := F.C₀_ne_zero
  A₀ := F.A₀
  A₀_pos := F.A₀_pos
  shift := fun j => archShift K θ j.1 + if j.2 then 1 / 6 else -(1 / 6)
  shift_pos := by
    rintro ⟨v, b⟩
    have ha := archShift_ge θ v
    cases b <;> dsimp <;> linarith
  radial := fun j => -archRadial K θ j.1

theorem directGamma_actual (s : ℂ) :
    directGamma (actualProfile K S F θ) s =
      F.C₀ * (F.A₀ : ℂ) ^ s *
        ∏ v : {v : InfinitePlace K // v.IsComplex},
          Complex.Gamma ((archShift K θ v : ℂ) + s -
            Complex.I * archRadial K θ v + 1 / 6) *
          Complex.Gamma ((archShift K θ v : ℂ) + s -
            Complex.I * archRadial K θ v - 1 / 6) := by
  rw [directGamma_eq_positive_cpow]
  congr 1
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro v _
  rw [Fintype.prod_bool]
  dsimp [actualProfile]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The actual smooth annular test supplies the scalar bounded-strip input;
no estimate is required of a nonannular Gaussian-smoothed test. -/
theorem annular_mellin_bounded_strips (V : SmoothAnnularTest) :
    BoundedOnVerticalStrips (mellin V.toFun) := by
  intro a b _
  obtain ⟨C, hC, hbound⟩ :=
    RegularizedTestProject.integrand_strip_bound V
      (a := a) (b := b) (y := 1) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro c hc t
  have hb := hbound c hc t
  simp only [VerticalInverseBounds.powerPhase, Complex.ofReal_one,
    Complex.one_cpow, mul_one] at hb
  exact hb.trans (mul_le_of_le_one_right hC
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)))

/-- A deconvolver for every actual annular test and every positive epsilon.
The reciprocal finite Gamma product's strip growth is a theorem. -/
def actualDeconvolver (V : SmoothAnnularTest)
    (ε : ℝ) (hε : 0 < ε) :
    AnnularTransfer.DeconvolverData
      (fun t : ℝ => directGamma (actualProfile K S F θ) ((t : ℂ) * Complex.I))
      (fun t : ℝ => mellin V.toFun ((t : ℂ) * Complex.I)) ε :=
  GammaProfileGrowth.canonicalDeconvolver (actualProfile K S F θ) (mellin V.toFun)
    (RegularizedTestProject.mellin_differentiable V)
    (annular_mellin_bounded_strips V) ε hε

theorem actualDeconvolver_all_power_moments (V : SmoothAnnularTest)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    IntegrableOn
      (fun t => ‖multiplicativeInverse
        (actualDeconvolver K S F θ V ε hε).spectrum t‖ * t ^ q / t)
      (Ioi 0) :=
  GammaProfileGrowth.canonicalDeconvolver_all_power_moments
    (actualProfile K S F θ) (mellin V.toFun)
    (RegularizedTestProject.mellin_differentiable V)
    (annular_mellin_bounded_strips V) ε hε q

end ThetaGlobal.GammaDeconvolverProject

