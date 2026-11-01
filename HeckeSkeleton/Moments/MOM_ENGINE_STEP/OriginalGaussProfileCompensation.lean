import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfiles
import HeckeGeneral.Analysis.IdealDirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The original inverse norm pays the additional Gauss square root

The first transform contributes its actual inverse ideal norm. The
extra frame normalizer is therefore paid by that inverse norm, using
the original positive compact support. Its compensation does not turn
the moving square root into an assumed original profile seminorm.

After this exact cancellation only a fixed signed power of the original
profile argument remains. Both Fourier phases retain the actual norm
offsets, but their modulus is one. The bound below uses only that the
original nonzero residual ideal has norm at least one and that its
original profile argument lies below the fixed annular upper endpoint.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.OriginalGaussProfileCompensation

open HeckeGeneral.Analysis

/-- The coefficient left after the exact scale reparametrization. -/
def scalar (G D δ₁ δ₂ : ℝ) : ℝ :=
  D ^ (δ₁ - 1) * G ^ (δ₁ + δ₂ - 1 / 2)

theorem scalar_pos (G D δ₁ δ₂ : ℝ) (hG : 0 < G) (hD : 0 < D) :
    0 < scalar G D δ₁ δ₂ :=
  mul_pos (Real.rpow_pos_of_pos hD _) (Real.rpow_pos_of_pos hG _)

/-- Both original norm powers and the genuine square-root normalizer
are accounted for before taking an absolute value. -/
theorem coefficient_factor (G D y δ₁ δ₂ : ℝ)
    (hG : 0 < G) (hD : 0 < D) (hy : 0 < y) :
    Real.sqrt G * (D * (G * y)) ^ (δ₁ - 1) * (G * y) ^ δ₂ =
      scalar G D δ₁ δ₂ * y ^ (δ₁ + δ₂ - 1) := by
  rw [Real.sqrt_eq_rpow]
  simp only [Real.mul_rpow hD.le (mul_pos hG hy).le,
    Real.mul_rpow hG.le hy.le, scalar]
  rw [show δ₁ + δ₂ - 1 / 2 = (1 / 2 + (δ₁ - 1)) + δ₂ by ring,
    show δ₁ + δ₂ - 1 = (δ₁ - 1) + δ₂ by ring]
  simp only [Real.rpow_add hG, Real.rpow_add hy]
  ring

theorem coefficient_factor_ratio (G D N δ₁ δ₂ : ℝ)
    (hG : 0 < G) (hD : 0 < D) (hN : 0 < N) :
    Real.sqrt G * (D * N) ^ (δ₁ - 1) * N ^ δ₂ =
      scalar G D δ₁ δ₂ * (N / G) ^ (δ₁ + δ₂ - 1) := by
  have h := coefficient_factor G D (N / G) δ₁ δ₂ hG hD (div_pos hN hG)
  have he : G * (N / G) = N := by
    rw [mul_comm, div_mul_cancel₀ _ hG.ne']
  simpa only [he] using h

/-- The original annulus pays the full additional square root. In
particular the right-hand side is independent of the moving scale. -/
theorem scalar_le_sqrt_annulus (G D N B δ₁ δ₂ : ℝ)
    (hG : 0 < G) (hD : 1 ≤ D) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hprofile : N / G ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2) :
    scalar G D δ₁ δ₂ ≤ Real.sqrt B := by
  have hdinv : D ^ (δ₁ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hD (by linarith)
  have hinv : G⁻¹ ≤ B := by
    have h : (1 : ℝ) / G ≤ B :=
      (div_le_iff₀ hG).mpr (hN.trans ((div_le_iff₀ hG).mp hprofile))
    simpa only [one_div] using h
  have hgpow : G ^ (δ₁ + δ₂ - 1 / 2) ≤ Real.sqrt B := by
    calc
      _ = (G⁻¹) ^ (1 / 2 - δ₁ - δ₂) := by
        rw [show δ₁ + δ₂ - 1 / 2 = -(1 / 2 - δ₁ - δ₂) by ring,
          Real.rpow_neg_eq_inv_rpow]
      _ ≤ B ^ (1 / 2 - δ₁ - δ₂) :=
        Real.rpow_le_rpow (inv_nonneg.mpr hG.le) hinv (by linarith)
      _ ≤ B ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hB (by linarith)
      _ = Real.sqrt B := (Real.sqrt_eq_rpow B).symm
  simpa only [scalar, one_mul] using
    (mul_le_mul hdinv hgpow (Real.rpow_nonneg hG.le _) (by norm_num : (0 : ℝ) ≤ 1))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The compensated profile uses scale one. The actual moving scale
and the actual earlier common ideal occur only in the phase offset. -/
def atom (G D δ₁ δ₂ : ℝ) (firstDirection secondDirection : V) :
    CanonicalLogProfiles.Atom V where
  scale := 1
  scale_pos := zero_lt_one
  exponent := δ₁ + δ₂ - 1
  offset := Real.log (D * G) • firstDirection + Real.log G • secondDirection
  direction := firstDirection + secondDirection

/-- The two original Fourier coordinates are preserved exactly. This
identity can be applied after the common row translation is removed. -/
theorem multiplier_identity (G D N δ₁ δ₂ : ℝ)
    (hG : 0 < G) (hD : 0 < D) (hN : 0 < N)
    (firstDirection secondDirection ξ : V) :
    ((Real.sqrt G * (D * N) ^ (δ₁ - 1) * N ^ δ₂ : ℝ) : ℂ) *
        jointPhase ξ (Real.log (D * N) • firstDirection + Real.log N • secondDirection) =
      ((scalar G D δ₁ δ₂ : ℝ) : ℂ) *
        (atom G D δ₁ δ₂ firstDirection secondDirection).multiplier ξ (N / G) := by
  have hlogN : Real.log N = Real.log G + Real.log (N / G) := by
    rw [Real.log_div hN.ne' hG.ne']
    ring
  have hlocation :
      (atom G D δ₁ δ₂ firstDirection secondDirection).location (N / G) =
        Real.log (D * N) • firstDirection + Real.log N • secondDirection := by
    simp only [CanonicalLogProfiles.Atom.location, atom, one_mul,
      Real.log_mul hD.ne' hG.ne', Real.log_mul hD.ne' hN.ne', hlogN,
      add_smul, smul_add]
    abel
  rw [coefficient_factor_ratio G D N δ₁ δ₂ hG hD hN, Complex.ofReal_mul,
    CanonicalLogProfiles.Atom.multiplier, hlocation]
  simp only [atom, one_mul]
  ring

section OriginalIdeals

variable {K : Type} [Field K] [NumberField K]

/-- The actual nonzero common and residual ideals supply the two
lower norm bounds. Only the original support annulus remains to check. -/
theorem original_ideal_scalar_bound
    (G B δ₁ δ₂ : ℝ) (D I : NonzeroIdeal K)
    (hG : 0 < G) (hB : 1 ≤ B)
    (hprofile : idealNorm K I / G ≤ B)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2) :
    scalar G (idealNorm K D) δ₁ δ₂ ≤ Real.sqrt B :=
  scalar_le_sqrt_annulus G (idealNorm K D) (idealNorm K I) B δ₁ δ₂ hG
    (one_le_idealNorm K D) (one_le_idealNorm K I) hB hprofile hδ₁ hδ₂ hδ

end OriginalIdeals

end HeckeSkeleton.Moments.EngineStep.OriginalGaussProfileCompensation

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalGaussProfileCompensation.coefficient_factor_ratio
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalGaussProfileCompensation.scalar_le_sqrt_annulus
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalGaussProfileCompensation.multiplier_identity
