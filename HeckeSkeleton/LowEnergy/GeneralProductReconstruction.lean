import HeckeSkeleton.LowEnergy.GeneralInactiveMass
import HeckeSkeleton.LowEnergy.GeneralRows
import HeckeSkeleton.LowEnergy.GeneralReconstruction
import HeckeSkeleton.LowEnergy.ActualRows

/-!
# Actual product marks, collisions and the canonical reflected series

The product mark is a finite sum of the literal whole-index mark masks.
Linearity is proved on the actual canonical completed sum using its
proved finite support.  Row, label and puncture collisions vanish on
the primal side before the supplied reflection is used.  Every remaining
tuple is reflected with its complete distinct-prime support.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralProductReconstruction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.LowEnergy.ActualSymbols
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSourceReindex
open HeckeSkeleton.LowEnergy.GeneralInactiveMass
open HeckeSkeleton.LowEnergy.GeneralRows
open HeckeSkeleton.LowEnergy.GeneralReconstruction
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The row and fourth-power label in the original canonical coefficient. -/
def canonicalRowElement (k label : ExteriorIdeal K S) (u : S.unit K) : S.integer K :=
  ((S.unitEquivUnitsInteger K u).val * D.generator k) * D.generator label ^ 4

/-- The ideal-product generator used by the actual marked reflection. -/
def reflectedRowElement (k label : ExteriorIdeal K S) (u : S.unit K) : S.integer K :=
  (S.unitEquivUnitsInteger K u).val *
    D.generator (exteriorMul K S k (ActualFrozenCube.exteriorPower K S label 4))

theorem canonicalRowElement_symbol (hD : AllowedGeneratorInput K S D)
    (I k label : ExteriorIdeal K S) (u : S.unit K) :
    idealSymbol K S D I (canonicalRowElement K S D k label u) =
      idealSymbol K S D I (reflectedRowElement K S D k label u) := by
  unfold canonicalRowElement reflectedRowElement
  simp only [idealSymbol_mul_numerator, idealSymbol_pow_numerator,
    actualSymbol_mul_right K S D hD, actualSymbol_fourth K S D hD]
  ring

/-- The canonical multiplicative coefficient is unchanged by the allowed
generator errors; nonexterior ideals retain their original zero. -/
theorem canonicalTau_rowElement (hD : AllowedGeneratorInput K S D)
    (θ : HeckeCharacter K) (k label puncture : ExteriorIdeal K S) (u : S.unit K) :
    canonicalTau K S D θ (canonicalRowElement K S D k label u) puncture.val.val =
      canonicalTau K S D θ (reflectedRowElement K S D k label u) puncture.val.val := by
  ext A
  by_cases hA : IsExterior K S A
  · let I := toExterior K S A hA
    change canonicalTau K S D θ (canonicalRowElement K S D k label u)
        puncture.val.val I.val.val =
      canonicalTau K S D θ (reflectedRowElement K S D k label u)
        puncture.val.val I.val.val
    rw [canonicalTau_apply, canonicalTau_apply, canonicalRowElement_symbol K S D hD]
  · rw [canonicalTau_eq_zero_of_not_exterior K S D θ _ _ A hA,
      canonicalTau_eq_zero_of_not_exterior K S D θ _ _ A hA]

theorem reflectedRowElement_contraction (k label : ExteriorIdeal K S) (u : S.unit K) :
    sIntegerModulusContraction K S (reflectedRowElement K S D k label u) =
      k.val.val * label.val.val ^ 4 := by
  unfold reflectedRowElement sIntegerModulusContraction
  rw [Ideal.span_singleton_mul_left_unit (S.unitEquivUnitsInteger K u).isUnit]
  exact generator_contraction K S D
    (exteriorMul K S k (ActualFrozenCube.exteriorPower K S label 4))

/-- Finite linearity of the actual canonical sum, with convergence proved
from the compact upper support of the annular test. -/
theorem canonicalCompletedSum_finite_linear {η : Type*} (s : Finset η)
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (coefficient : η → ℂ) (mark : η → Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    canonicalCompletedSum gamma tau (fun A => ∑ i ∈ s, coefficient i * mark i A) V X =
      ∑ i ∈ s, coefficient i * canonicalCompletedSum gamma tau (mark i) V X := by
  have hterm (CB : Ideal (𝓞 K) × Ideal (𝓞 K)) :
      canonicalCompletedTerm gamma tau (fun A => ∑ i ∈ s, coefficient i * mark i A)
        V X CB =
        ∑ i ∈ s, coefficient i * canonicalCompletedTerm gamma tau (mark i) V X CB := by
    unfold canonicalCompletedTerm
    by_cases hC : Squarefree CB.1
    · simp only [if_pos hC, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [if_neg hC, mul_zero, Finset.sum_const_zero]
  rw [canonicalCompletedSum_eq_tsum gamma tau _ V X U hX hV]
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun i _ =>
    (canonicalCompletedTerm_summable gamma tau (mark i) V X U hX hV).mul_left (coefficient i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left, ← canonicalCompletedSum_eq_tsum gamma tau (mark i) V X U hX hV]

section ProductTuples

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product-form coefficients with the actual whole-index support mask. -/
def productMark (s : Finset (ι → ExteriorPrime K S))
    (a : ι → ExteriorPrime K S → ℂ) (A : Ideal (𝓞 K)) : ℂ :=
  ∑ p ∈ s, slotProduct a p * wholeMarkWeight K S (tupleSupport p) A

/-- Repeated prime coordinates do not change the divisibility mask. -/
theorem productMark_piFinset (W : ι → Finset (ExteriorPrime K S))
    (a : ι → ExteriorPrime K S → ℂ) (A : Ideal (𝓞 K)) :
    productMark K S (Fintype.piFinset W) a A =
      ∏ i, ∑ q ∈ W i, if q.val.asIdeal ∣ A then a i q else 0 := by
  exact sum_slotProduct_support_mask W a (fun q => q.val.asIdeal ∣ A)

theorem canonicalCompletedSum_productMark (s : Finset (ι → ExteriorPrime K S))
    (a : ι → ExteriorPrime K S → ℂ)
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    canonicalCompletedSum gamma tau (productMark K S s a) V.toFun X =
      ∑ p ∈ s, slotProduct a p *
        canonicalCompletedSum gamma tau (wholeMarkWeight K S (tupleSupport p)) V.toFun X :=
  canonicalCompletedSum_finite_linear K s gamma tau (slotProduct a)
    (fun p => wholeMarkWeight K S (tupleSupport p)) V.toFun X V.upper hX
    (fun y hy => (V.support hy).2)

def TupleAdmissible (k label puncture : ExteriorIdeal K S)
    (p : ι → ExteriorPrime K S) : Prop :=
  ∀ q ∈ tupleSupport p, ¬q.val.asIdeal ∣ k.val.val ∧
    ¬q.val.asIdeal ∣ label.val.val ∧ ¬q.val.asIdeal ∣ puncture.val.val

theorem canonicalCompletedSum_wholeMark_eq_theta
    (θ : HeckeCharacter K) (m : S.integer K) (puncture : ExteriorIdeal K S)
    (Q : Finset (ExteriorPrime K S)) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    canonicalCompletedSum (exteriorGamma K S D) (canonicalTau K S D θ m puncture.val.val)
      (wholeMarkWeight K S Q) V.toFun X =
      completedThetaSum K S D θ m puncture Q V.toFun X := by
  have h := canonicalCompletedSum_eq_weightedTheta K S D θ m puncture Q (fun _ => 1)
    V.toFun X V.upper hX (fun y hy => (V.support hy).2)
  simpa only [mul_one, weightedCompletedTheta_one] using h

theorem completedThetaSum_zero_of_row_label_overlap
    (θ : HeckeCharacter K) (k label puncture : ExteriorIdeal K S) (u : S.unit K)
    (Q : Finset (ExteriorPrime K S)) (q : ExteriorPrime K S) (hq : q ∈ Q)
    (hoverlap : q.val.asIdeal ∣ k.val.val ∨ q.val.asIdeal ∣ label.val.val)
    (V : ℝ → ℂ) (X : ℝ) :
    completedThetaSum K S D θ (reflectedRowElement K S D k label u) puncture Q V X = 0 := by
  apply ActualRows.completedThetaSum_eq_zero_of_mark_overlap K S D θ _ puncture Q V X q hq
  rw [reflectedRowElement_contraction]
  rcases hoverlap with hk | hf
  · exact dvd_mul_of_dvd_left hk _
  · exact dvd_mul_of_dvd_right (dvd_trans hf (dvd_pow_self _ (by decide : 4 ≠ 0))) _

theorem completedTerm_zero_of_puncture_overlap
    (θ : HeckeCharacter K) (m : S.integer K) (puncture : ExteriorIdeal K S)
    (Q : Finset (ExteriorPrime K S)) (q : ExteriorPrime K S) (hq : q ∈ Q)
    (hpuncture : q.val.asIdeal ∣ puncture.val.val) (V : ℝ → ℂ) (X : ℝ)
    (CB : ExteriorIdeal K S × ExteriorIdeal K S) :
    completedTerm K S D θ m puncture Q V X CB = 0 := by
  dsimp only [completedTerm]
  split_ifs with h
  · exact (q.val.prime.not_unit (h.2.1.isUnit_of_dvd' (h.2.2 q hq) hpuncture)).elim
  · rfl

theorem completedThetaSum_zero_of_puncture_overlap
    (θ : HeckeCharacter K) (m : S.integer K) (puncture : ExteriorIdeal K S)
    (Q : Finset (ExteriorPrime K S)) (q : ExteriorPrime K S) (hq : q ∈ Q)
    (hpuncture : q.val.asIdeal ∣ puncture.val.val) (V : ℝ → ℂ) (X : ℝ) :
    completedThetaSum K S D θ m puncture Q V X = 0 := by
  simpa only [completedThetaSum, tsum_zero] using
    (tsum_congr (fun CB =>
      completedTerm_zero_of_puncture_overlap K S D θ m puncture Q q hq hpuncture V X CB))

/-- Every original collision is a proved primal zero, including a repeated
prime and a prime shared by the squarefree and cube variables. -/
theorem completedThetaSum_zero_of_not_admissible
    (θ : HeckeCharacter K) (k label puncture : ExteriorIdeal K S) (u : S.unit K)
    (p : ι → ExteriorPrime K S) (hp : ¬TupleAdmissible K S k label puncture p)
    (V : ℝ → ℂ) (X : ℝ) :
    completedThetaSum K S D θ (reflectedRowElement K S D k label u)
      puncture (tupleSupport p) V X = 0 := by
  by_contra hne
  apply hp
  intro q hq
  refine ⟨?_, ?_, ?_⟩
  · intro hk
    exact hne (completedThetaSum_zero_of_row_label_overlap K S D θ k label puncture u
      (tupleSupport p) q hq (Or.inl hk) V X)
  · intro hf
    exact hne (completedThetaSum_zero_of_row_label_overlap K S D θ k label puncture u
      (tupleSupport p) q hq (Or.inr hf) V X)
  · intro hr
    exact hne (completedThetaSum_zero_of_puncture_overlap K S D θ _ puncture
      (tupleSupport p) q hq hr V X)

theorem canonicalCompletedSum_productMark_eq_tupleTheta
    (hD : AllowedGeneratorInput K S D) (θ : HeckeCharacter K)
    (k label puncture : ExteriorIdeal K S) (u : S.unit K)
    (s : Finset (ι → ExteriorPrime K S)) (a : ι → ExteriorPrime K S → ℂ)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    canonicalCompletedSum (exteriorGamma K S D)
      (canonicalTau K S D θ (canonicalRowElement K S D k label u) puncture.val.val)
      (productMark K S s a) V.toFun X =
      ∑ p ∈ s, slotProduct a p *
        completedThetaSum K S D θ (reflectedRowElement K S D k label u)
          puncture (tupleSupport p) V.toFun X := by
  rw [canonicalTau_rowElement K S D hD,
    canonicalCompletedSum_productMark K S s a _ _ V X hX]
  apply Finset.sum_congr rfl
  intro p _
  rw [canonicalCompletedSum_wholeMark_eq_theta K S D θ _ puncture _ V X hX]

theorem canonicalCompletedSum_productMark_eq_noncolliding
    (hD : AllowedGeneratorInput K S D) (θ : HeckeCharacter K)
    (k label puncture : ExteriorIdeal K S) (u : S.unit K)
    (s : Finset (ι → ExteriorPrime K S)) (a : ι → ExteriorPrime K S → ℂ)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    canonicalCompletedSum (exteriorGamma K S D)
      (canonicalTau K S D θ (canonicalRowElement K S D k label u) puncture.val.val)
      (productMark K S s a) V.toFun X =
      ∑ p ∈ s.filter (TupleAdmissible K S k label puncture), slotProduct a p *
        completedThetaSum K S D θ (reflectedRowElement K S D k label u)
          puncture (tupleSupport p) V.toFun X := by
  rw [canonicalCompletedSum_productMark_eq_tupleTheta K S D hD θ k label puncture u s a V X hX,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : TupleAdmissible K S k label puncture p
  · rw [if_pos hp]
  · rw [if_neg hp, completedThetaSum_zero_of_not_admissible K S D θ k label puncture u p hp,
      mul_zero]

/-- One literal tuple reflection, with the full cube and every frozen and
unit sector retained.  Its datum uses the true row decomposition. -/
def reflectedTuple (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (k label puncture : ExteriorIdeal K S) (hpuncture : Squarefree puncture.val.val)
    (u : S.unit K) (p : ι → ExteriorPrime K S)
    (hp : TupleAdmissible K S k label puncture p) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  let d := markedDatum K S k label puncture hpuncture u (tupleSupport p) hp
  ∑' state : FrozenState K S d.frozen d.puncture,
    ∑' A : MarkChoice K S d,
      ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
        generalAtom K S D (splitFixed K S d A) state F θ (fun _ => 1) V X
          d.moving (primeSetIdeal K S A.val) cb.1 cb.2

theorem completedThetaSum_eq_reflectedTuple
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (k label puncture : ExteriorIdeal K S) (hpuncture : Squarefree puncture.val.val)
    (u : S.unit K) (p : ι → ExteriorPrime K S)
    (hp : TupleAdmissible K S k label puncture p)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    completedThetaSum K S D θ (reflectedRowElement K S D k label u)
      puncture (tupleSupport p) V.toFun X =
      reflectedTuple K S D F θ k label puncture hpuncture u p hp V.toFun X := by
  have h := completedThetaSum_eq_general_atoms K S D hD F θ hreflection
    (markedDatum K S k label puncture hpuncture u (tupleSupport p) hp) V X hX
  rw [GeneralRows.markedDatum_rowElement K S D k label puncture hpuncture u
    (tupleSupport p) hp] at h
  exact h

/-- Direct canonical bridge for one surviving tuple at the unchanged
completed scale, with the original row and fourth-power label. -/
theorem canonicalCompletedSum_wholeMark_eq_reflectedTuple
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (k label puncture : ExteriorIdeal K S) (hpuncture : Squarefree puncture.val.val)
    (u : S.unit K) (p : ι → ExteriorPrime K S)
    (hp : TupleAdmissible K S k label puncture p)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    canonicalCompletedSum (exteriorGamma K S D)
      (canonicalTau K S D θ (canonicalRowElement K S D k label u) puncture.val.val)
      (wholeMarkWeight K S (tupleSupport p)) V.toFun X =
      reflectedTuple K S D F θ k label puncture hpuncture u p hp V.toFun X := by
  rw [canonicalTau_rowElement K S D hD]
  have h := canonicalCompletedSum_eq_general_atoms K S D hD F θ hreflection
    (markedDatum K S k label puncture hpuncture u (tupleSupport p) hp) V X hX
  rw [GeneralRows.markedDatum_rowElement K S D k label puncture hpuncture u
    (tupleSupport p) hp] at h
  exact h

/-- The canonical product-mark sum is exactly the finite linear sum of
the genuine reflections of its surviving tuples.  The original tuple
coefficients remain outside each reflection, and no mask is discarded. -/
theorem canonicalCompletedSum_productMark_eq_reflectedTuples
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (k label puncture : ExteriorIdeal K S) (hpuncture : Squarefree puncture.val.val)
    (u : S.unit K) (s : Finset (ι → ExteriorPrime K S))
    (a : ι → ExteriorPrime K S → ℂ)
    (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    canonicalCompletedSum (exteriorGamma K S D)
      (canonicalTau K S D θ (canonicalRowElement K S D k label u) puncture.val.val)
      (productMark K S s a) V.toFun X =
      ∑ p ∈ (s.filter (TupleAdmissible K S k label puncture)).attach,
        slotProduct a p.val * reflectedTuple K S D F θ k label puncture hpuncture u p.val
          (Finset.mem_filter.mp p.property).2 V.toFun X := by
  rw [canonicalCompletedSum_productMark_eq_noncolliding K S D hD θ k label puncture u s a V X hX]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro p _
  rw [completedThetaSum_eq_reflectedTuple K S D hD F θ hreflection k label puncture
    hpuncture u p.val (Finset.mem_filter.mp p.property).2 V X hX]

end ProductTuples

#print axioms canonicalTau_rowElement
#print axioms canonicalCompletedSum_finite_linear
#print axioms productMark_piFinset
#print axioms canonicalCompletedSum_productMark
#print axioms completedThetaSum_zero_of_not_admissible
#print axioms canonicalCompletedSum_productMark_eq_noncolliding
#print axioms completedThetaSum_eq_reflectedTuple
#print axioms canonicalCompletedSum_wholeMark_eq_reflectedTuple
#print axioms canonicalCompletedSum_productMark_eq_reflectedTuples

end HeckeSkeleton.LowEnergy.GeneralProductReconstruction
