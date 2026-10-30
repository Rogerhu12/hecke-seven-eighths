import HeckeSkeleton.HighBinSupport.ActualEulerCRT

/-!
# Multiplicativity of the literal initial four-ideal term

The unmarked term is the original `initialRowEulerTerm` with `Q = ∅`.
The theorem below combines the actual CRT phase cancellation, the actual
Hecke ideal coefficient, positive ideal-norm complex powers, and the
squarefree indicator. The marked term is then related to this same term
by its literal completed-index divisibility mask; it is not asserted to
be multiplicative with the same nonempty mask in both factors.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualInitial

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeSkeleton.HighBinActualAbsolute HeckeSkeleton.HighBinActualCRT
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Componentwise multiplication of the four original exterior ideals. -/
def fourIdealMul (I J : FourIdealIndex K S) : FourIdealIndex K S :=
  ((exteriorMul K S I.1.1 J.1.1, exteriorMul K S I.1.2 J.1.2),
    (exteriorMul K S I.2.1 J.2.1, exteriorMul K S I.2.2 J.2.2))

/-- This ideal has exactly the prime support of the four original variables. -/
def fourIdealSupportIdeal (I : FourIdealIndex K S) : ExteriorIdeal K S :=
  exteriorMul K S (exteriorMul K S I.2.1 (completedIdeal K S I.1.1 I.1.2)) I.2.2

@[simp] theorem primeSetIdeal_empty_val :
    (primeSetIdeal K S ∅).val.val = (1 : Ideal (𝓞 K)) := by
  simp only [primeSetIdeal, Finset.image_empty, squarefreeIdeal, primeProduct, Finset.prod_empty]

/-- The complex power identity uses positivity of the actual ideal norms. -/
theorem exteriorNorm_cpow_mul (I J : ExteriorIdeal K S) (z : ℂ) :
    (exteriorNorm K S (exteriorMul K S I J) : ℂ) ^ z =
      (exteriorNorm K S I : ℂ) ^ z * (exteriorNorm K S J : ℂ) ^ z := by
  rw [exteriorNorm_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (idealNorm_pos K I.val).le
    (idealNorm_pos K J.val).le z

/-- The remaining actual Hecke coefficient and Mellin weights. -/
def rowEulerWeight (P : ProbeData K S) (ψ : HeckeCharacter K)
    (s w z : ℂ) (I : FourIdealIndex K S) : ℂ :=
  heckeIdealCoefficient K (thetaPeriod K S P ψ) (completedIdeal K S I.1.1 I.1.2).val *
    (exteriorNorm K S I.1.1 : ℂ) ^ (-(1 / 2 : ℂ) - s) *
    (exteriorNorm K S I.1.2 : ℂ) ^ (-1 - 3 * s) *
    (exteriorNorm K S I.2.1 : ℂ) ^ (-w) *
    (exteriorNorm K S I.2.2 : ℂ) ^ (-6 * z)

/-- The original summand before applying its squarefree and marked masks. -/
def rowEulerUnmaskedTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (I : FourIdealIndex K S) : ℂ :=
  (thetaGamma K S P.arithmetic I.1.1 2 *
    finitePoissonFactor K S P I.2.1 (completedIdeal K S I.1.1 I.1.2)
      (poissonFrequency K S P u I.2.2)) * rowEulerWeight K S P ψ s w z I

theorem rowEulerWeight_mul (P : ProbeData K S) (ψ : HeckeCharacter K)
    (s w z : ℂ) (I J : FourIdealIndex K S) :
    rowEulerWeight K S P ψ s w z (fourIdealMul K S I J) =
      rowEulerWeight K S P ψ s w z I * rowEulerWeight K S P ψ s w z J := by
  have hcoef : heckeIdealCoefficient K (thetaPeriod K S P ψ)
      (completedIdeal K S (exteriorMul K S I.1.1 J.1.1)
        (exteriorMul K S I.1.2 J.1.2)).val =
      heckeIdealCoefficient K (thetaPeriod K S P ψ) (completedIdeal K S I.1.1 I.1.2).val *
      heckeIdealCoefficient K (thetaPeriod K S P ψ) (completedIdeal K S J.1.1 J.1.2).val := by
    rw [completedIdeal_mul]
    exact heckeIdealCoefficient_mul K _ _ _
  simp only [rowEulerWeight, fourIdealMul]
  rw [hcoef, exteriorNorm_cpow_mul, exteriorNorm_cpow_mul,
    exteriorNorm_cpow_mul, exteriorNorm_cpow_mul]
  ring

theorem rowEulerUnmaskedTerm_coprime_mul (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (I J : FourIdealIndex K S)
    (hIJ : IsCoprime (fourIdealSupportIdeal K S I).val.val
      (fourIdealSupportIdeal K S J).val.val) :
    rowEulerUnmaskedTerm K S P ψ u s w z (fourIdealMul K S I J) =
      rowEulerUnmaskedTerm K S P ψ u s w z I * rowEulerUnmaskedTerm K S P ψ u s w z J := by
  have hfinite := fourIdeal_finite_coefficient_coprime_product K S P hP u
    I.1.1 J.1.1 I.1.2 J.1.2 I.2.1 J.2.1 I.2.2 J.2.2 hIJ
  unfold rowEulerUnmaskedTerm
  rw [rowEulerWeight_mul]
  change (thetaGamma K S P.arithmetic (exteriorMul K S I.1.1 J.1.1) 2 *
    finitePoissonFactor K S P (exteriorMul K S I.2.1 J.2.1)
      (completedIdeal K S (exteriorMul K S I.1.1 J.1.1) (exteriorMul K S I.1.2 J.1.2))
      (poissonFrequency K S P u (exteriorMul K S I.2.2 J.2.2))) * _ = _
  rw [hfinite]
  ring

/-- An exact bridge back to the original definition, retaining its mask. -/
theorem initialRowEulerTerm_eq_masked (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (I : FourIdealIndex K S) :
    initialRowEulerTerm K S P ψ Q u s w z I =
      if Squarefree I.1.1.val.val ∧
          (∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S I.1.1 I.1.2).val.val) then
        rowEulerUnmaskedTerm K S P ψ u s w z I else 0 := by
  simp only [initialRowEulerTerm, wholeIndexMask, primeSetIdeal_empty_val,
    isCoprime_one_right, true_and]
  split_ifs
  · unfold rowEulerUnmaskedTerm rowEulerWeight
    ring
  · rfl

theorem initialRowEulerTerm_empty (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (I : FourIdealIndex K S) :
    initialRowEulerTerm K S P ψ ∅ u s w z I =
      if Squarefree I.1.1.val.val then rowEulerUnmaskedTerm K S P ψ u s w z I else 0 := by
  rw [initialRowEulerTerm_eq_masked]
  simp

/-- Multiplicativity of the original unmarked four-ideal term. -/
theorem initialRowEulerTerm_empty_coprime_mul (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (I J : FourIdealIndex K S)
    (hIJ : IsCoprime (fourIdealSupportIdeal K S I).val.val
      (fourIdealSupportIdeal K S J).val.val) :
    initialRowEulerTerm K S P ψ ∅ u s w z (fourIdealMul K S I J) =
      initialRowEulerTerm K S P ψ ∅ u s w z I * initialRowEulerTerm K S P ψ ∅ u s w z J := by
  have hA : IsCoprime (completedIdeal K S I.1.1 I.1.2).val.val
      (completedIdeal K S J.1.1 J.1.2).val.val :=
    hIJ.of_mul_left_left.of_mul_right_left.of_mul_left_right.of_mul_right_right
  have hc : IsCoprime I.1.1.val.val J.1.1.val.val := hA.of_mul_left_left.of_mul_right_left
  have hsq : Squarefree (fourIdealMul K S I J).1.1.val.val ↔
      Squarefree I.1.1.val.val ∧ Squarefree J.1.1.val.val := by
    change Squarefree (I.1.1.val.val * J.1.1.val.val) ↔ _
    rw [squarefree_mul_iff]
    simp only [hc.isRelPrime, true_and]
  rw [initialRowEulerTerm_empty, initialRowEulerTerm_empty, initialRowEulerTerm_empty]
  by_cases hI : Squarefree I.1.1.val.val <;> by_cases hJ : Squarefree J.1.1.val.val
  · rw [if_pos (hsq.mpr ⟨hI, hJ⟩), if_pos hI, if_pos hJ]
    exact rowEulerUnmaskedTerm_coprime_mul K S P hP ψ u s w z I J hIJ
  · rw [if_neg (fun h => hJ (hsq.mp h).2), if_neg hJ, mul_zero]
  · rw [if_neg (fun h => hI (hsq.mp h).1), if_neg hI, zero_mul]
  · rw [if_neg (fun h => hI (hsq.mp h).1), if_neg hI, zero_mul]

/-- Nonempty marks are a literal finite-support filter on the proved
unmarked term; they are never imposed independently on both CRT blocks. -/
theorem initialRowEulerTerm_eq_filter_empty (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (I : FourIdealIndex K S) :
    initialRowEulerTerm K S P ψ Q u s w z I =
      if ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S I.1.1 I.1.2).val.val then
        initialRowEulerTerm K S P ψ ∅ u s w z I else 0 := by
  rw [initialRowEulerTerm_eq_masked, initialRowEulerTerm_empty]
  by_cases hQ : ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S I.1.1 I.1.2).val.val <;>
    by_cases hc : Squarefree I.1.1.val.val <;> simp [hQ, hc]

#print axioms rowEulerUnmaskedTerm_coprime_mul
#print axioms initialRowEulerTerm_empty_coprime_mul
#print axioms initialRowEulerTerm_eq_filter_empty
end HeckeSkeleton.HighBinActualInitial
