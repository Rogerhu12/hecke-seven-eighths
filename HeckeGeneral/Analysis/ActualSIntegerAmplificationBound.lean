import HeckeGeneral.Analysis.ActualSIntegerAmplifierRows
import HeckeGeneral.Analysis.SIntegerSexticMellinAmplification
import HeckeGeneral.Analysis.IdealAmplifierSmallPower

/-!
Actual ideal amplification into a sum over the norm-bounded S-integer orbits.
The row embedding, norm, exact Mellin-test identity and divisor small-power
estimate are proved arithmetic inputs. Only a rowwise scale majorant is
consumed here. The later ideal-count lower bound and MI/Q4.5 estimate are
not hidden in an admissibility predicate or assumed injective row map.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis.SquarefreeAmplification
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (τ : ThetaArithmeticData K S)

theorem dyadicDividingPrimes_thetaGenerator_subset (A : ExteriorIdeal K S) (D : ℝ) :
    dyadicDividingPrimes K S (τ.generator A) D ⊆ idealPrimeSupport K A.val := by
  intro p hp
  apply (mem_idealPrimeSupport_iff K A.val p).mpr
  have hdvd := (Finset.mem_filter.mp hp).2
  rwa [contraction_thetaGenerator K S τ A] at hdvd

theorem sum_amplifier_majorants_le_bounded_orbits
    (F : Finset (ExteriorIdeal K S)) {P H : ℝ}
    (hF : ∀ A ∈ F, idealNorm K A.val ≤ P) (hPH : P ^ 6 ≤ H)
    (B : ActualSIntegerOrbit K S → ℝ) (hB : ∀ q, 0 ≤ B q) :
    (∑ A ∈ F, B (actualAmplifierRow K S τ A)) ≤
      ∑ q : ActualBoundedSIntegerOrbits K S H, B q.val := by
  let e : {A : ExteriorIdeal K S // A ∈ F} → ActualBoundedSIntegerOrbits K S H :=
    fun A => ⟨actualAmplifierRow K S τ A.val,
      (actualAmplifierRow_norm_le K S τ A.val (hF A.val A.property)).trans hPH⟩
  have he : Function.Injective e := fun _ _ h =>
    Subtype.ext (actualAmplifierRow_injective K S τ (congrArg Subtype.val h))
  rw [← Finset.sum_coe_sort]
  exact Finset.sum_le_sum_of_injOn e he.injOn (Finset.subset_univ _)
    (fun _ _ => le_rfl) (fun q _ _ => hB q.val)

/-- Uniform in the target, scales and finite amplifier set. Every member of
F is an actual exterior ideal and contributes a distinct actual sixth-power
row. All divisor scales lie between zero and D, exactly as required by the
scale-majorant input. -/
theorem actualMellin_amplification_to_orbit_majorant {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : HeckeCharacter K) (F : Finset (ExteriorIdeal K S))
      (P H D : ℝ) (s : ℂ) (B : ActualSIntegerOrbit K S → ℝ),
      1 ≤ P → P ^ 6 ≤ H → 0 < D →
      (∀ A ∈ F, idealNorm K A.val ≤ P) →
      (∀ q, 0 ≤ B q) →
      (∀ q, actualSIntegerOrbitNorm K S q ≤ H → ∀ r : ℝ,
        0 < r → r ≤ D →
        ‖actualSIntegerInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η q r s‖ ^ 2
          ≤ B q) →
      (F.card : ℝ) *
        ‖dyadicSexticMellinInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η 1 D s‖ ^ 2
        ≤ C * P ^ (2 * δ) * ∑ q : ActualBoundedSIntegerOrbits K S H, B q.val := by
  obtain ⟨C, hC, hmass⟩ := sexticAmplifierCoefficient_mass_small_power K hδ
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro η F P H D s B hP hPH hD hF hB hrow
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have heach (A : ExteriorIdeal K S) (hA : A ∈ F) :
      ‖dyadicSexticMellinInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η 1 D s‖ ^ 2
        ≤ (C * P ^ δ) ^ 2 * B (actualAmplifierRow K S τ A) := by
    apply dyadicSexticMellinInversePolynomial_sq_le K S τ.root6 τ.primitive6 τ.embedding η
      (τ.generator A) hD s (hB _)
    · exact (hmass η A.val _ (dyadicDividingPrimes_thetaGenerator_subset K S τ A D)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (idealNorm_pos K A.val).le (hF A hA) hδ.le) hC.le)
    · intro T _hT
      have hscale : D / idealNorm K (squarefreeIdeal K T) ≤ D :=
        div_le_self hD.le (one_le_idealNorm K _)
      have h := hrow (actualAmplifierRow K S τ A)
        ((actualAmplifierRow_norm_le K S τ A (hF A hA)).trans hPH)
        (D / idealNorm K (squarefreeIdeal K T))
        (div_pos hD (idealNorm_pos K _)) hscale
      exact h
  have hsum := Finset.sum_le_sum heach
  have hsum' : (F.card : ℝ) *
        ‖dyadicSexticMellinInversePolynomial K S τ.root6 τ.primitive6 τ.embedding η 1 D s‖ ^ 2
      ≤ (C * P ^ δ) ^ 2 * ∑ A ∈ F, B (actualAmplifierRow K S τ A) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum] using hsum
  have hpow : (C * P ^ δ) ^ 2 = C ^ 2 * P ^ (2 * δ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hP0 δ 2]
    congr 1
    ring
  calc
    _ ≤ (C * P ^ δ) ^ 2 * ∑ A ∈ F, B (actualAmplifierRow K S τ A) := hsum'
    _ ≤ (C * P ^ δ) ^ 2 * ∑ q : ActualBoundedSIntegerOrbits K S H, B q.val :=
      mul_le_mul_of_nonneg_left
        (sum_amplifier_majorants_le_bounded_orbits K S τ F hF hPH B hB) (sq_nonneg _)
    _ = _ := by rw [hpow]

end HeckeGeneral.Analysis.ActualSIntegerMoments
