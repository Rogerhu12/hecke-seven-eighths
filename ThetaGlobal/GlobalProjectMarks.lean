import ThetaGlobal.GlobalMarks
import HeckeSkeleton.MarkedAnnularSupport
import HeckeGeneral.Analysis.SIntegerSexticAmplification

/-!
# Exact mark insertion for the project's literal completed theta sum

The proof in this file uses the original definitions of `completedTerm`
and `completedThetaSum`.  It replaces all whole-index divisibility
marks by finitely many enlarged punctures.  It introduces no KP,
reflection, or automorphic hypothesis.

Compilation status must be taken from the accompanying report.  Unlike
`GlobalMarks`, this file imports the supplied project, whose compiled
dependency tree is not part of the attachment.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectMarks

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The prime-product puncture has exactly the expected nondivisibility
mask.  No squarefreeness assumption on the tested ideal is necessary. -/
theorem primeSetIdeal_coprime_iff (A : ExteriorIdeal K S)
    (Q : Finset (ExteriorPrime K S)) :
    IsCoprime A.val.val (primeSetIdeal K S Q).val.val ↔
      ∀ p ∈ Q, ¬p.val.asIdeal ∣ A.val.val := by
  change IsCoprime A.val.val
    (∏ p ∈ Q.image Subtype.val, p.asIdeal) ↔ _
  rw [IsCoprime.prod_right_iff]
  constructor
  · intro h p hp
    have hc := h p.val (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    exact (primeIdeal_coprime_iff_not_dvd K p.val A.val.val).mp hc.symm
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ((primeIdeal_coprime_iff_not_dvd K q.val A.val.val).mpr (h q hq)).symm

theorem augmented_puncture_coprime_iff (A r : ExteriorIdeal K S)
    (Q : Finset (ExteriorPrime K S)) :
    IsCoprime A.val.val (exteriorMul K S r (primeSetIdeal K S Q)).val.val ↔
      IsCoprime A.val.val r.val.val ∧ ∀ p ∈ Q, ¬p.val.asIdeal ∣ A.val.val := by
  change IsCoprime A.val.val (r.val.val * (primeSetIdeal K S Q).val.val) ↔ _
  rw [IsCoprime.mul_right_iff, primeSetIdeal_coprime_iff K S]

variable (D : ThetaArithmeticData K S) (θ : HeckeCharacter K)
variable (m : S.integer K) (r : ExteriorIdeal K S)
variable (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ)

theorem completedTerm_marks_factor (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    completedTerm K S D θ m r Q V X cn =
      completedTerm K S D θ m r ∅ V X cn *
        (if ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S cn.1 cn.2).val.val
          then (1 : ℂ) else 0) := by
  by_cases hsf : Squarefree cn.1.val.val
  · by_cases hcop : IsCoprime (completedIdeal K S cn.1 cn.2).val.val r.val.val
    · by_cases hQ : ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S cn.1 cn.2).val.val
      · simp [completedTerm, wholeIndexMask, hsf, hcop, hQ]
      · simp [completedTerm, wholeIndexMask, hsf, hcop, hQ]
    · simp [completedTerm, wholeIndexMask, hsf, hcop]
  · simp [completedTerm, wholeIndexMask, hsf]

theorem completedTerm_add_punctures (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    completedTerm K S D θ m (exteriorMul K S r (primeSetIdeal K S Q)) ∅ V X cn =
      completedTerm K S D θ m r ∅ V X cn *
        (if ∀ p ∈ Q, ¬p.val.asIdeal ∣ (completedIdeal K S cn.1 cn.2).val.val
          then (1 : ℂ) else 0) := by
  by_cases hsf : Squarefree cn.1.val.val
  · by_cases hcop : IsCoprime (completedIdeal K S cn.1 cn.2).val.val r.val.val
    · by_cases hQ : ∀ p ∈ Q, ¬p.val.asIdeal ∣ (completedIdeal K S cn.1 cn.2).val.val
      · simp [completedTerm, wholeIndexMask, augmented_puncture_coprime_iff K S,
          hsf, hcop, hQ]
      · simp [completedTerm, wholeIndexMask, augmented_puncture_coprime_iff K S,
          hsf, hcop, hQ]
    · simp [completedTerm, wholeIndexMask, augmented_puncture_coprime_iff K S,
        hsf, hcop]
  · simp [completedTerm, wholeIndexMask, hsf]

/-- The exact termwise marked identity for the project's coefficients. -/
theorem completedTerm_marks_inclusion_exclusion
    (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    completedTerm K S D θ m r Q V X cn =
      ∑ J ∈ Q.powerset, (-1 : ℂ) ^ J.card *
        completedTerm K S D θ m (exteriorMul K S r (primeSetIdeal K S J)) ∅ V X cn := by
  rw [completedTerm_marks_factor K S D θ m r Q V X]
  rw [GlobalMarks.weighted_marks_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [completedTerm_add_punctures K S D θ m r J V X]

/-- Any summable unmarked completed coefficient admits exact mark insertion.
The only analytic hypothesis is summability of the original unmarked
series, never a reflection identity. -/
theorem completedThetaSum_marks_inclusion_exclusion_of_summable
    (hs : Summable (completedTerm K S D θ m r ∅ V X)) :
    completedThetaSum K S D θ m r Q V X =
      ∑ J ∈ Q.powerset, (-1 : ℂ) ^ J.card *
        completedThetaSum K S D θ m (exteriorMul K S r (primeSetIdeal K S J)) ∅ V X := by
  unfold completedThetaSum
  calc
    _ = ∑' cn, completedTerm K S D θ m r ∅ V X cn *
        (if ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S cn.1 cn.2).val.val
          then (1 : ℂ) else 0) := by
      apply tsum_congr
      intro cn
      exact completedTerm_marks_factor K S D θ m r Q V X cn
    _ = ∑ J ∈ Q.powerset, (-1 : ℂ) ^ J.card *
        ∑' cn, completedTerm K S D θ m r ∅ V X cn *
          (if ∀ p ∈ J, ¬p.val.asIdeal ∣ (completedIdeal K S cn.1 cn.2).val.val
            then (1 : ℂ) else 0) :=
      GlobalMarks.tsum_marked_eq_alternating_unmarked Q
        (fun p cn => p.val.asIdeal ∣ (completedIdeal K S cn.1 cn.2).val.val)
        (completedTerm K S D θ m r ∅ V X) hs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro J hJ
      congr 1
      apply tsum_congr
      intro cn
      exact (completedTerm_add_punctures K S D θ m r J V X cn).symm

/-- For annular smooth tests the convergence input is discharged by the
existing finite ideal-support theorem.  This statement has no analytic
or representation-theoretic assumptions beyond the original data. -/
theorem completedThetaSum_marks_inclusion_exclusion
    (W : SmoothAnnularTest) (hX : 0 < X) :
    completedThetaSum K S D θ m r Q W.toFun X =
      ∑ J ∈ Q.powerset, (-1 : ℂ) ^ J.card *
        completedThetaSum K S D θ m (exteriorMul K S r (primeSetIdeal K S J)) ∅ W.toFun X :=
  completedThetaSum_marks_inclusion_exclusion_of_summable K S D θ m r Q W.toFun X
    (HeckeSkeleton.MarkedAnnularSupport.completedTerm_summable_of_annular
      K S D θ m r ∅ W X hX)

end ThetaGlobal.GlobalProjectMarks
