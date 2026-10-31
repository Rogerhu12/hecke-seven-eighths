import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MaskNorm

/-!
# The remaining ideal in the actual common mask

An extra coprimality ideal is retained by adjoining its actual prime
support to the original S/6/complete-row deletion set.  The row character
and the row itself do not change.  This gives the literal polynomial
identity needed by a reflected descendant with a remaining mask R.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

def remainingRowDeletionPrimes (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (u R : NonzeroIdeal K) : Finset (Ideal (𝓞 K)) :=
  completeRowDeletionPrimes S u ∪ primeSupport R.val

theorem remainingRowDeletionPrimes_prime
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u R : NonzeroIdeal K) :
    ∀ P ∈ remainingRowDeletionPrimes S u R, Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hP | hP
  · exact completeRowDeletionPrimes_prime S u P hP
  · exact support_prime hP

theorem remainingRowDeletionPrimes_outside_iff
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u R I : NonzeroIdeal K) :
    outside (remainingRowDeletionPrimes S u R) I.val ↔
      outside (completeRowDeletionPrimes S u) I.val ∧ IsCoprime I.val R.val := by
  have hsplit : outside (remainingRowDeletionPrimes S u R) I.val ↔
      outside (completeRowDeletionPrimes S u) I.val ∧ outside (primeSupport R.val) I.val := by
    constructor
    · intro h
      exact ⟨fun P hP => h P (Finset.mem_union_left _ hP),
        fun P hP => h P (Finset.mem_union_right _ hP)⟩
    · rintro ⟨h₁, h₂⟩ P hP
      rcases Finset.mem_union.mp hP with hP | hP
      · exact h₁ P hP
      · exact h₂ P hP
  rw [hsplit]
  exact and_congr_right fun _ =>
    (outside_iff_coprime (primeSupport R.val) (fun _ hP => support_prime hP)
      (nonzeroIdealDeletionEquiv I)).trans
      (coprime_support_iff I.val R.val (nonZeroDivisors.coe_ne_zero R)).symm

theorem remainingCommonMask_eq_deletion
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u R I : NonzeroIdeal K) :
    (completeIdealCommonMask K S u I.val && decide (IsCoprime I.val R.val)) =
      decide (outside (remainingRowDeletionPrimes S u R) I.val) := by
  by_cases ho : outside (completeRowDeletionPrimes S u) I.val <;>
    by_cases hc : IsCoprime I.val R.val <;>
    simp [completeIdealCommonMask_eq_deletion,
      remainingRowDeletionPrimes_outside_iff, ho, hc]

theorem maskValue_eq_remaining_deletion {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u R : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I R.val)))
    (I : NonzeroIdeal K) :
    maskValue d u I.val =
      if outside (remainingRowDeletionPrimes S u R) I.val then (1 : ℂ) else 0 := by
  simp [maskValue, hmask, remainingCommonMask_eq_deletion]

/-- The extra mask costs the norm of R once, while retaining the entire
original row ideal u, including redundant sixth powers. -/
theorem remainingRowDeletionProduct_dvd
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u R : NonzeroIdeal K) :
    (∏ P ∈ remainingRowDeletionPrimes S u R, P) ∣
      fixedRowDeletionIdeal S * u.val * R.val := by
  have hM : fixedRowDeletionIdeal S * u.val * R.val ≠ ⊥ :=
    mul_ne_zero (mul_ne_zero (fixedRowDeletionIdeal_ne_bot S)
      (nonZeroDivisors.coe_ne_zero u)) (nonZeroDivisors.coe_ne_zero R)
  apply support_product_dvd hM
  intro P hP
  apply (prime_mem_support_iff _ _ hM (remainingRowDeletionPrimes_prime S u R P hP)).mpr
  rcases Finset.mem_union.mp hP with hP | hP
  · have hd : P ∣ ∏ Q ∈ completeRowDeletionPrimes S u, Q :=
      Finset.dvd_prod_of_mem _ hP
    exact dvd_mul_of_dvd_left (hd.trans (completeRowDeletionProduct_dvd S u)) _
  · exact dvd_mul_of_dvd_right
      ((prime_mem_support_iff R.val P (nonZeroDivisors.coe_ne_zero R)
        (support_prime hP)).mp hP) _

theorem remainingRowDeletionProduct_norm_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u R : NonzeroIdeal K) :
    (Ideal.absNorm (∏ P ∈ remainingRowDeletionPrimes S u R, P) : ℝ) ≤
      (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) * idealNorm K u * idealNorm K R := by
  have hM : fixedRowDeletionIdeal S * u.val * R.val ≠ ⊥ :=
    mul_ne_zero (mul_ne_zero (fixedRowDeletionIdeal_ne_bot S)
      (nonZeroDivisors.coe_ne_zero u)) (nonZeroDivisors.coe_ne_zero R)
  have h := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hM (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm (remainingRowDeletionProduct_dvd S u R))
  simp only [map_mul] at h
  dsimp only [idealNorm]
  exact_mod_cast h

/-- The actual polynomial, with the same character, test, scale and row,
is the true ideal sum with the complete remaining deletion set. -/
theorem plainPolynomial_eq_remaining_deleted_sum {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W : IdealTest K)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u R : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I R.val)))
    (N t : ℝ) :
    plainPolynomial d W u N t =
      plainPoly (excl (remainingRowDeletionPrimes S u R)
        (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u))))
        (W.profile u t) N := by
  unfold plainPolynomial plainPoly
  congr 1
  let term : NonzeroIdeal K → ℂ := fun I =>
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
      W.profile u t (idealNorm K I / N) * maskValue d u I.val
  have hfinite : (∑' I, term I) = ∑ I ∈ W.support u t N, term I := by
    apply tsum_eq_sum
    intro I hI
    have hz : W.profile u t (idealNorm K I / N) = 0 := by
      by_contra hn
      exact hI ((W.support_spec u t N I).mpr hn)
    simp only [term, hz, mul_zero, zero_mul]
  calc
    _ = ∑' I, term I := hfinite.symm
    _ = ∑' I : NonzeroIdeal K,
        excl (remainingRowDeletionPrimes S u R)
          (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u)))
          (nonzeroIdealDeletionEquiv I).val *
          W.profile u t (inorm (nonzeroIdealDeletionEquiv I) / N) := by
      apply tsum_congr
      intro I
      dsimp only [term, nonzeroIdealDeletionEquiv, inorm,
        heckeIdealCoefficient, nonzeroIdealCoefficient, idealNorm]
      rw [maskValue_eq_remaining_deletion d S u R hmask I]
      by_cases hI : outside (remainingRowDeletionPrimes S u R) I.val
      · simp only [excl, if_pos hI, mul_one]
      · simp only [excl, if_neg hI, mul_zero, zero_mul]
    _ = _ := (nonzeroIdealDeletionEquiv (K := K)).tsum_eq _

end HeckeSkeleton.Moments.EngineInduction
