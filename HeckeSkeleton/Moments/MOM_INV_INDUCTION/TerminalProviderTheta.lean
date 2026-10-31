import HeckeSkeleton.Moments.MOM_BASE.ThetaBridge
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

/-!
# Exact cube completion of the actual finite canonical column

The finite squarefree column is converted to the literal completed theta
sum by the proved ideal cube inversion. The normalization uses
`Vstar(y) = sqrt(y) W(y)`, and every puncture and whole-index mark survives
the equality. The background, row, and label are arbitrary fixed data.
This is the source identity preceding the general reflected block
estimate consumed in `TerminalProvider`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem canonicalVstar_support_upper (W : ℝ → ℂ) (U : ℝ)
    (hW : Function.support W ⊆ Set.Iic U) :
    Function.support (canonicalVstar W) ⊆ Set.Iic U := by
  intro y hy
  apply hW
  intro hw
  exact hy (by simp only [canonicalVstar, hw, mul_zero])

/-- The complete finite canonical column at the original scale. The
row and squarefree label enter only through their actual symbols. -/
def completeCanonicalColumn (θ : HeckeCharacter K) (k : S.integer K)
    (f r : ExteriorIdeal K S) (mark : Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ * ∑ n ∈ squarefreePool K S X,
    thetaGamma K S D n 2 *
      canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val n.val.val *
      mark n.val.val * W (exteriorNorm K S n / X)

/-- Termwise normalization before the ideal Möbius cube inversion. -/
theorem completeCanonicalColumn_term (θ : HeckeCharacter K) (m : S.integer K)
    (r n : ExteriorIdeal K S) (mark : Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X) :
    thetaGamma K S D n 2 * canonicalTau K S D θ m r.val.val n.val.val /
        (Real.sqrt (exteriorNorm K S n) : ℂ) * mark n.val.val *
          canonicalVstar W (exteriorNorm K S n / X) =
      (Real.sqrt X : ℂ)⁻¹ *
        (thetaGamma K S D n 2 * canonicalTau K S D θ m r.val.val n.val.val *
          mark n.val.val * W (exteriorNorm K S n / X)) := by
  have hN : 0 < exteriorNorm K S n := idealNorm_pos K n.val
  calc
    _ = (thetaGamma K S D n 2 * canonicalTau K S D θ m r.val.val n.val.val *
        mark n.val.val) *
        ((Real.sqrt (exteriorNorm K S n) : ℂ)⁻¹ *
          canonicalVstar W (exteriorNorm K S n / X)) := by ring
    _ = _ := by
      rw [canonicalVstar_normalization W (exteriorNorm K S n) X hN hX]
      ring

/-- Exact completion of the full finite squarefree column. No terminal
estimate, reconstruction equality, or moment bound is supplied as a
premise; this is the literal cube-Möbius identity over exterior ideals. -/
theorem completeCanonicalColumn_cube_completion
    (θ : HeckeCharacter K) (k : S.integer K) (f r : ExteriorIdeal K S)
    (mark : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ)
    (hX : 0 < X) (hW : Function.support W ⊆ Set.Iic 2) :
    completeCanonicalColumn K S D θ k f r mark W X =
      ∑' H : ExteriorIdeal K S,
        (moebius H.val.val : ℂ) *
          canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
          (exteriorNorm K S H : ℂ) *
          weightedCompletedTheta K S D θ (k * D.generator f ^ 4) r ∅
            (fun A => mark (H.val.val ^ 3 * A)) (canonicalVstar W)
            (X / exteriorNorm K S H ^ 3) := by
  have hV := canonicalVstar_support_upper W 2 hW
  have hbridge := canonicalThetaBridge K S D θ (k * D.generator f ^ 4)
    r mark (canonicalVstar W) X 2 hX hV
  apply Eq.trans _ hbridge
  symm
  rw [tsum_eq_sum (squarefreePool K S X)]
  · unfold completeCanonicalColumn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos ((mem_squarefreePool K S X n).mp hn).1]
    exact completeCanonicalColumn_term K S D θ (k * D.generator f ^ 4)
      r n mark W X hX
  · intro n hn
    by_cases hsf : Squarefree n.val.val
    · rw [if_pos hsf]
      have hlarge : ¬ exteriorNorm K S n ≤ 2 * X := by
        intro hnorm
        exact hn ((mem_squarefreePool K S X n).mpr ⟨hsf, hnorm⟩)
      have hzero : W (exteriorNorm K S n / X) = 0 := by
        by_contra hne
        exact hlarge ((div_le_iff₀ hX).mp (hW hne))
      simp only [canonicalVstar, hzero, mul_zero]
    · rw [if_neg hsf]

/-- The same finite column written with its row, label and puncture
factors separate. This is the literal canonical coefficient shape used
by both the induction and the one-step provider. -/
theorem completeCanonicalColumn_eq_symbols
    (θ : HeckeCharacter K) (k : S.integer K) (f r : ExteriorIdeal K S)
    (mark : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    completeCanonicalColumn K S D θ k f r mark W X =
      (Real.sqrt X : ℂ)⁻¹ * ∑ n ∈ squarefreePool K S X,
        thetaGamma K S D n 2 * heckeIdealCoefficient K θ n.val *
          idealSymbol K S D n k * idealSymbol K S D n (D.generator f) ^ 4 *
          (if IsCoprime n.val.val r.val.val then 1 else 0) *
          mark n.val.val * W (exteriorNorm K S n / X) := by
  unfold completeCanonicalColumn
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [canonicalTau_label]
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
