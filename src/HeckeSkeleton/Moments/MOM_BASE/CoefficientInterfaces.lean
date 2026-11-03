import HeckeSkeleton.Moments.MOM_BASE.ThetaBridge
import HeckePort.Moments.ReflectionDeletion

/-!
# Actual coefficients in the deletion interfaces

The explicit `IdealCoeff` premise in the ported deletion formulas is proved
for the original Hecke coefficient, sextic symbol, and puncture. This
includes the excluded primes and the zero ideal, so the interface does not
silently extend a coprime-only multiplicativity statement.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem norm_canonicalTau_le_one (θ : HeckeCharacter K) (m : S.integer K)
    (r I : Ideal (𝓞 K)) : ‖canonicalTau K S D θ m r I‖ ≤ 1 := by
  by_cases hI : IsExterior K S I
  · let J : ExteriorIdeal K S := toExterior K S I hI
    change ‖canonicalTau K S D θ m r J.val.val‖ ≤ 1
    rw [canonicalTau_apply, norm_mul, norm_mul]
    have hc := norm_heckeIdealCoefficient_le_one K θ J.val
    have hs := norm_idealSymbol_le_one K S D J m
    have hm : ‖(if IsCoprime J.val.val r then 1 else 0 : ℂ)‖ ≤ 1 := by
      split_ifs <;> norm_num
    have hp := mul_le_mul hc hs (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have ht := mul_le_mul hp hm (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)
    simpa using ht
  · rw [canonicalTau_eq_zero_of_not_exterior K S D θ m r I hI]
    simp

/-- The port's explicit coefficient premise, discharged by actual arithmetic. -/
theorem canonicalTau_idealCoeff (θ : HeckeCharacter K) (m : S.integer K)
    (r : Ideal (𝓞 K)) :
    HeckePort.Moments.IdealCoeff (canonicalTau K S D θ m r) where
  map_one := map_one (canonicalTau K S D θ m r)
  mul := map_mul (canonicalTau K S D θ m r)
  norm_le_one := norm_canonicalTau_le_one K S D θ m r

/-- Summability of the actual plain polynomial with a quadratic-decay test. -/
theorem actual_plain_summable (θ : HeckeCharacter K) (m : S.integer K)
    (r : Ideal (𝓞 K)) (F : ℝ → ℂ) (hF : HeckePort.Moments.DecayTwo F)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun I : HeckePort.Moments.NI K =>
      canonicalTau K S D θ m r I.val * F (HeckePort.Moments.inorm I / X)) :=
  HeckePort.Moments.plain_summable (canonicalTau_idealCoeff K S D θ m r) F hF X hX

/-- Finite deletion with its exact ideal Möbius and norm factors. -/
theorem actual_normalized_finite_deletion (θ : HeckeCharacter K) (m : S.integer K)
    (r : Ideal (𝓞 K)) (P : Finset (Ideal (𝓞 K)))
    (hP : ∀ p ∈ P, Prime p) (F : ℝ → ℂ) (hF : HeckePort.Moments.DecayTwo F)
    (X : ℝ) (hX : 0 < X) :
    HeckePort.Moments.plainPoly
      (HeckePort.Moments.excl P (canonicalTau K S D θ m r)) F X =
      ∑ T ∈ P.powerset, (moebius (∏ p ∈ T, p) : ℂ) *
        (canonicalTau K S D θ m r (∏ p ∈ T, p) /
          (Real.sqrt (Ideal.absNorm (∏ p ∈ T, p) : ℝ) : ℂ)) *
        HeckePort.Moments.plainPoly (canonicalTau K S D θ m r) F
          (X / (Ideal.absNorm (∏ p ∈ T, p) : ℝ)) :=
  HeckePort.Moments.normalized_finite_deletion_moebius
    (canonicalTau_idealCoeff K S D θ m r) P hP F hF X hX

end HeckeSkeleton.Moments.MOM_BASE
