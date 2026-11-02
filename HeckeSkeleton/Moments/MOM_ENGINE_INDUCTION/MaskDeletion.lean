import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData
import HeckeGeneral.Analysis.HeckeConjugation
import HeckePort.Moments.ReflectionDeletion

/-!
# The original complete-row mask as genuine finite prime deletion

The deletion set contains the fixed primes in `S`, the primes above 6,
and every prime factor of the original complete row ideal.  In particular,
the latter is not replaced by a chosen sixth-power-free representative.

The finite polynomial is identified with the literally deleted actual
Hecke ideal sum before the proved finite deletion formula is applied.
This is only the arithmetic deletion step: it does not claim a reflected
profile tail bound, a restored common mask, or a completed parent reduction.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Arithmetic
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open scoped BigOperators Classical ComplexConjugate nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

private theorem sixIdeal_ne_bot :
    (Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K))) ≠ ⊥ := by
  intro h
  have hz : (6 : 𝓞 K) = 0 := Ideal.span_singleton_eq_bot.mp h
  norm_num at hz

/-- The full original common mask, including the redundant prime factors
of the complete ideal `u`, as a finite set of actual prime ideals. -/
def completeRowDeletionPrimes (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (u : NonzeroIdeal K) : Finset (Ideal (𝓞 K)) :=
  (S.toFinset.image HeightOneSpectrum.asIdeal ∪
    primeSupport (Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K)))) ∪ primeSupport u.val

theorem completeRowDeletionPrimes_prime
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u : NonzeroIdeal K) :
    ∀ P ∈ completeRowDeletionPrimes S u, Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hfixed | hu
  · rcases Finset.mem_union.mp hfixed with hS | h6
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hS
      exact p.prime
    · exact support_prime h6
  · exact support_prime hu

/-- Exact predicate equality with the original `S/6/u` mask. -/
theorem completeRowDeletionPrimes_outside_iff
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (u I : NonzeroIdeal K) :
    outside (completeRowDeletionPrimes S u) I.val ↔
      (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val →
        p ∉ S ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧ IsCoprime I.val u.val := by
  have hI : I.val ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  have hu : u.val ≠ ⊥ := nonZeroDivisors.coe_ne_zero u
  constructor
  · intro hout
    refine ⟨?_, ?_⟩
    · intro p hpI
      constructor
      · intro hpS
        apply hout p.asIdeal ?_ hpI
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨p, Set.mem_toFinset.mpr hpS, rfl⟩))
      · intro hp6
        have hpdvd : p.asIdeal ∣ Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K)) :=
          Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hp6)
        have hpsupport : p.asIdeal ∈
            primeSupport (Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K))) :=
          (prime_mem_support_iff _ _ (sixIdeal_ne_bot (K := K)) p.prime).mpr hpdvd
        exact hout p.asIdeal
          (Finset.mem_union_left _ (Finset.mem_union_right _ hpsupport)) hpI
    · apply (primeSupport_disjoint_iff hI hu).mp
      apply Finset.disjoint_left.mpr
      intro P hPI hPu
      exact hout P (Finset.mem_union_right _ hPu)
        ((prime_mem_support_iff I.val P hI (support_prime hPI)).mp hPI)
  · rintro ⟨hfixed, hcoprime⟩ P hP hPI
    rcases Finset.mem_union.mp hP with hfixedP | huP
    · rcases Finset.mem_union.mp hfixedP with hSP | h6P
      · obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hSP
        exact (hfixed p hPI).1 (Set.mem_toFinset.mp hpS)
      · let p : HeightOneSpectrum (𝓞 K) :=
          ⟨P, Ideal.isPrime_of_prime (support_prime h6P), (support_prime h6P).ne_zero⟩
        have hpdvd : P ∣ Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K)) :=
          (prime_mem_support_iff _ _ (sixIdeal_ne_bot (K := K)) (support_prime h6P)).mp h6P
        exact (hfixed p hPI).2
          ((Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp hpdvd))
    · have hdisjoint := (primeSupport_disjoint_iff hI hu).mpr hcoprime
      exact Finset.disjoint_left.mp hdisjoint
        ((prime_mem_support_iff I.val P hI (support_prime huP)).mpr hPI) huP

/-- The source constructor's literal Bool mask is the finite prime
deletion predicate, with no modification of its original support. -/
theorem completeIdealCommonMask_eq_deletion
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (u I : NonzeroIdeal K) :
    completeIdealCommonMask K S u I.val =
      decide (outside (completeRowDeletionPrimes S u) I.val) := by
  simp only [completeIdealCommonMask,
    (completeRowDeletionPrimes_outside_iff S u I).symm]

/-- Consume the actual source mask calibration, without adding a
predicate about the energy of the source polynomial. -/
theorem maskValue_eq_complete_deletion {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (u : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I = completeIdealCommonMask K S u I)
    (I : NonzeroIdeal K) :
    maskValue d u I.val =
      if outside (completeRowDeletionPrimes S u) I.val then (1 : ℂ) else 0 := by
  simp [maskValue, hmask, completeIdealCommonMask_eq_deletion]

/-- The two standard representations of nonzero ideals have identical
ideal values. This changes no row, coefficient, or norm. -/
def nonzeroIdealDeletionEquiv : NonzeroIdeal K ≃ HeckePort.Moments.NI K where
  toFun I := ⟨I.val, nonZeroDivisors.coe_ne_zero I⟩
  invFun I := ⟨I.val, mem_nonZeroDivisors_of_ne_zero I.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coefficient required by the finite-deletion theorem is the
actual zero-extended Hecke coefficient on integral ideals. -/
theorem heckeIdealCoeff_for_deletion (χ : HeckeCharacter K) :
    HeckePort.Moments.IdealCoeff (idealCoefficient (primeCoefficient K χ)) where
  map_one := idealCoefficient_one _
  mul := idealCoefficient_mul _
  norm_le_one := norm_idealCoefficient_le_one _ (norm_primeCoefficient_le_one K χ)

/-- A genuine finite `plainPolynomial` is exactly the deleted ideal sum
with the same norm profile and square-root normalization. -/
theorem plainPolynomial_eq_complete_deleted_sum {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W : IdealTest K)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (u : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I = completeIdealCommonMask K S u I)
    (N t : ℝ) :
    plainPolynomial d W u N t =
      HeckePort.Moments.plainPoly
        (HeckePort.Moments.excl (completeRowDeletionPrimes S u)
          (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u))))
        (W.profile u t) N := by
  unfold plainPolynomial HeckePort.Moments.plainPoly
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
        (HeckePort.Moments.excl (completeRowDeletionPrimes S u)
          (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u))))
          (nonzeroIdealDeletionEquiv (K := K) I).val *
          W.profile u t
            (HeckePort.Moments.inorm (nonzeroIdealDeletionEquiv (K := K) I) / N) := by
      apply tsum_congr
      intro I
      change idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u)) I.val *
          W.profile u t ((Ideal.absNorm I.val : ℝ) / N) * maskValue d u I.val =
        HeckePort.Moments.excl (completeRowDeletionPrimes S u)
          (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u))) I.val *
            W.profile u t ((Ideal.absNorm I.val : ℝ) / N)
      rw [maskValue_eq_complete_deletion d S u hmask I]
      by_cases hI : outside (completeRowDeletionPrimes S u) I.val
      · simp only [HeckePort.Moments.excl, if_pos hI, mul_one]
      · simp only [HeckePort.Moments.excl, if_neg hI, mul_zero, zero_mul]
    _ = _ := (nonzeroIdealDeletionEquiv (K := K)).tsum_eq
      (fun I : HeckePort.Moments.NI K =>
        HeckePort.Moments.excl (completeRowDeletionPrimes S u)
          (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u))) I.val *
            W.profile u t (HeckePort.Moments.inorm I / N))

/-- The exact finite Möbius deletion formula is now available for the
original actual moment polynomial. Its inputs are only the original
mask calibration, positive scale and a true profile decay estimate. -/
theorem plainPolynomial_complete_finite_deletion {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W : IdealTest K)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (u : NonzeroIdeal K)
    (hmask : ∀ I, d.commonMask u I = completeIdealCommonMask K S u I)
    (N t : ℝ) (hN : 0 < N) (hW : HeckePort.Moments.DecayTwo (W.profile u t)) :
    plainPolynomial d W u N t =
      ∑ D ∈ (completeRowDeletionPrimes S u).powerset,
        (UniqueFactorizationMonoid.moebius (∏ P ∈ D, P) : ℂ) *
          (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u))
            (∏ P ∈ D, P) /
            (Real.sqrt (Ideal.absNorm (∏ P ∈ D, P) : ℝ) : ℂ)) *
          HeckePort.Moments.plainPoly
            (idealCoefficient (primeCoefficient K (d.plainBackground * d.rowCharacter u)))
            (W.profile u t) (N / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)) := by
  rw [plainPolynomial_eq_complete_deleted_sum d W S u hmask N t]
  exact HeckePort.Moments.normalized_finite_deletion_moebius
    (heckeIdealCoeff_for_deletion (d.plainBackground * d.rowCharacter u))
    (completeRowDeletionPrimes S u) (completeRowDeletionPrimes_prime S u)
    (W.profile u t) hW N hN

/-- Invert the actual Hecke character by conjugating the norm profile,
retaining every prime deletion. This avoids replacing the original row
ideal by another ideal to encode the inverse moving character. -/
theorem deletedHeckePlainPoly_inv_conjugate (χ : HeckeCharacter K)
    (P : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (N : ℝ) :
    HeckePort.Moments.plainPoly
        (HeckePort.Moments.excl P (idealCoefficient (primeCoefficient K χ⁻¹))) F N =
      conj (HeckePort.Moments.plainPoly
        (HeckePort.Moments.excl P (idealCoefficient (primeCoefficient K χ)))
        (fun y => conj (F y)) N) := by
  have hcoefficient (I : Ideal (𝓞 K)) :
      idealCoefficient (primeCoefficient K χ⁻¹) I =
        conj (idealCoefficient (primeCoefficient K χ) I) := by
    rw [show primeCoefficient K χ⁻¹ = fun p => conj (primeCoefficient K χ p)
      from funext (primeCoefficient_inv K χ)]
    exact idealCoefficient_conjugate _ _
  simp only [HeckePort.Moments.plainPoly, map_mul, map_inv₀,
    Complex.conj_ofReal, Complex.conj_tsum]
  congr 1
  apply tsum_congr
  intro I
  by_cases hI : outside P I.val
  · simp only [HeckePort.Moments.excl, if_pos hI, hcoefficient, map_mul,
      Complex.conj_conj]
  · simp only [HeckePort.Moments.excl, if_neg hI, zero_mul, map_zero]

/-- The ordinary reflected factor has exactly the same norm with the
original character and conjugated test. The other original plain factor
and slot product can therefore remain in the same `MomentData`. -/
theorem norm_deletedHeckePlainPoly_inv (χ : HeckeCharacter K)
    (P : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (N : ℝ) :
    ‖HeckePort.Moments.plainPoly
        (HeckePort.Moments.excl P (idealCoefficient (primeCoefficient K χ⁻¹))) F N‖ =
      ‖HeckePort.Moments.plainPoly
        (HeckePort.Moments.excl P (idealCoefficient (primeCoefficient K χ)))
        (fun y => conj (F y)) N‖ := by
  rw [deletedHeckePlainPoly_inv_conjugate, Complex.norm_conj]

end HeckeSkeleton.Moments.EngineInduction
