import HeckeSkeleton.Moments.MOM_BASE.CanonicalCalibration
import HeckeSkeleton.Moments.MOM_BASE.FiniteCoefficients
import HeckeSkeleton.Moments.MOM_BASE.Marks
import HeckeSkeleton.Moments.MOM_BASE.PairedFiniteRay
import HeckeSkeleton.Moments.MOM_BASE.CoefficientInterfaces
import HeckeSkeleton.Moments.MOM_BASE.SupportedCorrelation
import HeckeSkeleton.Moments.MOM_BASE.FiniteBackground

/-! Importable actual-context entry point for the shared MOM_BASE foundation. -/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)
local notation "S" => places K c
local notation "D" => arithmeticData K c

/-- Lemma 4.3 on the single arithmetic context of the project. The left
side is the canonical squarefree polynomial; the right side uses the
literal completed theta sum with its original puncture and shifted whole
weight. The live period remains conjugate(Lambda) times nu. -/
theorem targetCanonicalThetaBridge_of_support (ν : HeckeCharacter K) (k : S.integer K)
    (f r : ExteriorIdeal K S) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    (∑' C : ExteriorIdeal K S,
      if Squarefree C.val.val ∧ IsCoprime C.val.val r.val.val then
        canonicalCoefficient K c C * heckeIdealCoefficient K ν C.val *
          idealSymbol K S D C k * idealSymbol K S D C (D.generator f) ^ 4 /
            (Real.sqrt (exteriorNorm K S C) : ℂ) *
              d C.val.val * V (exteriorNorm K S C / X)
      else 0) =
      ∑' H : ExteriorIdeal K S,
        (moebius H.val.val : ℂ) *
          canonicalTau K S D (canonicalPeriod K c ν)
            (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
          (exteriorNorm K S H : ℂ) *
          weightedCompletedTheta K S D (canonicalPeriod K c ν)
            (k * D.generator f ^ 4) r ∅
            (fun A => d (H.val.val ^ 3 * A)) V (X / exteriorNorm K S H ^ 3) := by
  have h := canonicalThetaBridge K S D (canonicalPeriod K c ν)
    (k * D.generator f ^ 4) r d V X U hX hV
  refine Eq.trans ?_ h
  apply tsum_congr
  intro C
  rw [canonicalTau_label, canonicalPeriod_coefficient]
  by_cases hC : Squarefree C.val.val <;> by_cases hr : IsCoprime C.val.val r.val.val <;>
    simp only [hC, hr, and_true, and_false, if_true, if_false,
      mul_one, mul_zero, zero_mul, zero_div]
  unfold canonicalCoefficient
  ring

/-- The canonical bridge for the annular tests used in the moments. -/
theorem targetCanonicalThetaBridge (ν : HeckeCharacter K) (k : S.integer K)
    (f r : ExteriorIdeal K S) (d : Ideal (𝓞 K) → ℂ)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    (∑' C : ExteriorIdeal K S,
      if Squarefree C.val.val ∧ IsCoprime C.val.val r.val.val then
        canonicalCoefficient K c C * heckeIdealCoefficient K ν C.val *
          idealSymbol K S D C k * idealSymbol K S D C (D.generator f) ^ 4 /
            (Real.sqrt (exteriorNorm K S C) : ℂ) *
              d C.val.val * V.toFun (exteriorNorm K S C / X)
      else 0) =
      ∑' H : ExteriorIdeal K S,
        (moebius H.val.val : ℂ) *
          canonicalTau K S D (canonicalPeriod K c ν)
            (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
          (exteriorNorm K S H : ℂ) *
          weightedCompletedTheta K S D (canonicalPeriod K c ν)
            (k * D.generator f ^ 4) r ∅
            (fun A => d (H.val.val ^ 3 * A)) V.toFun (X / exteriorNorm K S H ^ 3) :=
  targetCanonicalThetaBridge_of_support K c ν k f r d V.toFun X V.upper hX
    (fun y hy => (V.support hy).2)

/-- Central normalization is identified along with the actual coefficient:
the completed test is `sqrt(y) * W(y)`, and the live period is unchanged. -/
theorem targetCanonicalNormalizedThetaBridge (ν : HeckeCharacter K) (k : S.integer K)
    (f r : ExteriorIdeal K S) (d : Ideal (𝓞 K) → ℂ)
    (W : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' C : ExteriorIdeal K S,
        if Squarefree C.val.val ∧ IsCoprime C.val.val r.val.val then
          canonicalCoefficient K c C * heckeIdealCoefficient K ν C.val *
            idealSymbol K S D C k * idealSymbol K S D C (D.generator f) ^ 4 *
              d C.val.val * W.toFun (exteriorNorm K S C / X)
        else 0) =
      ∑' H : ExteriorIdeal K S,
        (moebius H.val.val : ℂ) *
          canonicalTau K S D (canonicalPeriod K c ν)
            (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
          (exteriorNorm K S H : ℂ) *
          weightedCompletedTheta K S D (canonicalPeriod K c ν)
            (k * D.generator f ^ 4) r ∅
            (fun A => d (H.val.val ^ 3 * A)) (canonicalVstar W.toFun)
            (X / exteriorNorm K S H ^ 3) := by
  have hV : Function.support (canonicalVstar W.toFun) ⊆ Set.Iic W.upper := by
    intro y hy
    have hW : y ∈ Function.support W.toFun := by
      intro hz
      exact hy (by simp [canonicalVstar, hz])
    exact (W.support hW).2
  have h := targetCanonicalThetaBridge_of_support K c ν k f r d
    (canonicalVstar W.toFun) X W.upper hX hV
  refine Eq.trans ?_ h
  rw [← tsum_mul_left]
  apply tsum_congr
  intro C
  by_cases hC : Squarefree C.val.val ∧ IsCoprime C.val.val r.val.val
  · simp only [hC, if_true]
    have hn := canonicalVstar_normalization W.toFun (exteriorNorm K S C) X
      (idealNorm_pos K C.val) hX
    linear_combination -(canonicalCoefficient K c C * heckeIdealCoefficient K ν C.val *
      idealSymbol K S D C k * idealSymbol K S D C (D.generator f) ^ 4 *
        d C.val.val) * hn
  · simp [hC]

end HeckeSkeleton.Moments.MOM_BASE
