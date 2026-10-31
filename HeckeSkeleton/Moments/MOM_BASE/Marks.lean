import HeckeSkeleton.Moments.MOM_BASE.ThetaBridge
import HeckePort.Moments.Descent.MarkedTwists

/-!
# Whole-index marks and frozen cube phases

The existing mark-priority theorem is applied to the actual summand, with
finite support proved from the compact annulus. Frozen row/label phases
act by contractions on the genuine finite Hilbert sums.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.CenteredMomentGenerator
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Exact whole-index mark priority for the actual completed summand.
The residual lists retain their original exclusion at the frozen ideal. -/
theorem actual_mark_priority (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (V : ℝ → ℂ) (X U : ℝ)
    (hX : 0 < X) (hV : Function.support V ⊆ Set.Iic U)
    {σ : Type*} [DecidableEq σ] (slots : Finset σ)
    (L : σ → Finset (Ideal (𝓞 K))) (a : σ → Ideal (𝓞 K) → ℂ)
    (H : Ideal (𝓞 K)) (hH : H ≠ ⊥) :
    let s := fun C B => canonicalCompletedTerm (exteriorGamma K S D)
      (canonicalTau K S D θ m r.val.val) (fun _ => 1) V X (C, B)
    markedCompletedT s
      (fun A => primeMark slots L a (primeSupport (H ^ 3 * A))) =
      ∑ J ∈ slots.powerset,
        primeMark J L a (primeSupport H) *
          markedCompletedT s (fun A =>
            primeMark (slots \ J) (fun i => L i \ primeSupport H) a (primeSupport A)) := by
  exact markedCompletedT_prime_priority
    (actualCompletedSummand K S D θ m r V X U hX hV) slots L a H hH

/-- The label phase of the frozen cube equals its original coprimality mask. -/
theorem frozen_label_mask (H f : ExteriorIdeal K S) :
    idealSymbol K S D H (D.generator f) ^ 12 =
      if IsCoprime H.val.val f.val.val then 1 else 0 := by
  rw [idealSymbol_twelfth_power_mask,
    HeckeGeneral.Analysis.ActualSIntegerMoments.contraction_thetaGenerator]

/-- Freezing an extracted cube is a contraction in the joint row-label space. -/
theorem frozen_phase_joint_contraction {α β : Type*}
    (T : Finset α) (U : Finset β) (θ : HeckeCharacter K)
    (k : α → S.integer K) (f : β → ExteriorIdeal K S)
    (H : ExteriorIdeal K S) (r : Ideal (𝓞 K)) (F : α → β → ℂ) :
    (∑ i ∈ T, ∑ j ∈ U,
      ‖canonicalTau K S D θ (k i * D.generator (f j) ^ 4) r H.val.val ^ 3 *
        F i j‖ ^ 2) ≤ ∑ i ∈ T, ∑ j ∈ U, ‖F i j‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := norm_frozen_phase_le_one K S D θ (k i) (f j) H r
  have hmul := mul_le_mul_of_nonneg_right h (norm_nonneg (F i j))
  rw [one_mul] at hmul
  rw [norm_mul]
  exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmul 2

end HeckeSkeleton.Moments.MOM_BASE
