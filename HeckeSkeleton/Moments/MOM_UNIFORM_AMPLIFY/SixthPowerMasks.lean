import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData

/-!
# Sixth-power descendants of the actual complete-ideal model

The base is recovered by prime valuations modulo six.  Its Hecke character
and original unit sector stay fixed; the complete row mask acquires exactly
the additional coprimality zero.  This proves the arithmetic mask input for
the existing `decomposedZeroSlotMomentData` constructor at every scale and
for every actual `IdealTest`, without making an analytic moment assumption.
-/

noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped BigOperators Classical nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- Every nontrivial multiplier leaves the sixth-power-free range.
Consequently a seed summed only over sixth-free rows cannot serve as the
complete-row seed for the sixth-power amplifier. -/
theorem sixthPowerFree_mul_sixth_iff {u a : NonzeroIdeal K}
    (hu : SixthPowerFreeIdeal u) :
    SixthPowerFreeIdeal (u * a ^ 6) ↔ a = 1 := by
  constructor
  · intro h
    have he : u * a ^ 6 = (u * a ^ 6) * (1 : NonzeroIdeal K) ^ 6 := by simp
    exact (sixthPowerFree_mul_sixth_unique hu h he).2
  · rintro rfl
    simpa using hu

/-- The exact omitted summand in a sixth-free-only strict moment seed. -/
theorem complete_rows_inverse_energy_split {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (U D t : ℝ) :
    (∑ u ∈ d.rows U, ‖inversePolynomial d u D t‖ ^ 2) =
      (∑ u ∈ (d.rows U).filter (SixthPowerFreeIdeal (K := K)),
        ‖inversePolynomial d u D t‖ ^ 2) +
      ∑ u ∈ (d.rows U).filter (fun u => ¬SixthPowerFreeIdeal (K := K) u),
        ‖inversePolynomial d u D t‖ ^ 2 := by
  symm
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- Multiplication by any sixth power preserves the actual sixth-free
ideal, including when the original complete ideal already has sixth powers. -/
theorem sixthPowerFreePart_mul_sixth (u a : NonzeroIdeal K) :
    sixthPowerFreePart (u * a ^ 6) = sixthPowerFreePart u := by
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  apply Finsupp.ext
  intro p
  change primeExponents (sixthPowerFreePart (u * a ^ 6)) p =
    primeExponents (sixthPowerFreePart u) p
  rw [primeExponents_sixthPowerFreePart, primeExponents_sixthPowerFreePart,
    primeExponents_mul, Finsupp.add_apply, primeExponents_pow_apply]
  omega

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Original fixed-place exclusions survive every permitted multiplier. -/
theorem completeIdealIsExterior_mul_sixth (u : NonzeroIdeal K)
    (a : ExteriorIdeal K S) (hu : completeIdealIsExterior K S u) :
    completeIdealIsExterior K S (u * a.val ^ 6) := by
  intro p hp
  change p.asIdeal ∣ u.val * a.val.val ^ 6 at hp
  rcases p.prime.dvd_mul.mp hp with hpu | hpa
  · exact hu p hpu
  · exact a.property p (p.prime.dvd_of_dvd_pow hpa)

/-- The fixed exceptional-prime mask is retained on all ideals, including
zero and every ideal sharing a prime with the original complete row. -/
theorem completeIdealCommonMask_sixth (u : NonzeroIdeal K)
    (a : ExteriorIdeal K S) (I : Ideal (𝓞 K)) :
    (if completeIdealCommonMask K S (u * a.val ^ 6) I then (1 : ℂ) else 0) =
      (if completeIdealCommonMask K S u I then (1 : ℂ) else 0) *
        (if IsCoprime I a.val.val then 1 else 0) := by
  have hcop : IsCoprime I (u * a.val ^ 6).val ↔
      IsCoprime I u.val ∧ IsCoprime I a.val.val := by
    change IsCoprime I (u.val * a.val.val ^ 6) ↔ _
    rw [IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 6)]
  simp only [completeIdealCommonMask, decide_eq_true_eq, hcop]
  split_ifs <;> simp_all

variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- The original unit sector and the sixth-free ideal determine exactly
the same calibrated frequency row after multiplication by a sixth power. -/
theorem decomposedFrequencyRow_mul_sixth (u : NonzeroIdeal K)
    (a : ExteriorIdeal K S) (hu : completeIdealIsExterior K S u)
    (ξ : SixthUnitClasses K S) :
    decomposedFrequencyRow K S
      ⟨u * a.val ^ 6, completeIdealIsExterior_mul_sixth S u a hu⟩ ξ =
      decomposedFrequencyRow K S ⟨u, hu⟩ ξ := by
  have hi : exteriorSixthPowerFreePart S
      (⟨u * a.val ^ 6, completeIdealIsExterior_mul_sixth S u a hu⟩ : ExteriorIdeal K S) =
      exteriorSixthPowerFreePart S (⟨u, hu⟩ : ExteriorIdeal K S) := by
    apply Subtype.ext
    exact sixthPowerFreePart_mul_sixth u a.val
  simp only [decomposedFrequencyRow, hi]

/-- Character invariance for the existing constructor, with all original
sectors retained.  This is an equality of actual Hecke characters. -/
theorem completeIdealRowCharacter_mul_sixth (u : NonzeroIdeal K)
    (a : ExteriorIdeal K S) (hu : completeIdealIsExterior K S u)
    (ξ : SixthUnitClasses K S) :
    completeIdealRowCharacter K S P R ξ (u * a.val ^ 6) =
      completeIdealRowCharacter K S P R ξ u := by
  rw [completeIdealRowCharacter_exterior K S P R ξ
      ⟨u * a.val ^ 6, completeIdealIsExterior_mul_sixth S u a hu⟩,
    completeIdealRowCharacter_exterior K S P R ξ ⟨u, hu⟩,
    decomposedFrequencyRow_mul_sixth]

/-- The arithmetic calibration needed by an arbitrary source model is
equality with the actual exhaustive row predicate, calibrated base character
and original common mask.  No condition on its background or profile is
needed for this identity. -/
theorem momentData_sixthPowerMasks_of_arithmetic_calibration
    {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ) (ξ : SixthUnitClasses K S)
    (hrows : d.allowedRow = completeIdealIsExterior K S)
    (hchar : d.rowCharacter = completeIdealRowCharacter K S P R ξ)
    (hmask : d.commonMask = completeIdealCommonMask K S)
    (u : NonzeroIdeal K) (a : ExteriorIdeal K S) (hu : d.allowedRow u) :
    d.allowedRow (u * a.val ^ 6) ∧
      d.rowCharacter (u * a.val ^ 6) = d.rowCharacter u ∧
      ∀ I : Ideal (𝓞 K), maskValue d (u * a.val ^ 6) I =
        maskValue d u I * (if IsCoprime I a.val.val then 1 else 0) := by
  have hu' : completeIdealIsExterior K S u := by simpa only [hrows] using hu
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hrows] using completeIdealIsExterior_mul_sixth S u a hu'
  · simpa only [hchar] using completeIdealRowCharacter_mul_sixth S P R u a hu' ξ
  · intro I
    simpa only [maskValue, hmask] using completeIdealCommonMask_sixth S u a I

/-- The full arithmetic input required by sixth-power amplification holds
for the repository's actual complete-row model and any finite-support test. -/
theorem decomposedZeroSlotMomentData_sixthPowerMasks
    (ω η : HeckeCharacter K) (ξ : SixthUnitClasses K S) (W : IdealTest K)
    (u : NonzeroIdeal K) (a : ExteriorIdeal K S)
    (hu : (decomposedZeroSlotMomentData K S P R ω η ξ W).allowedRow u) :
    let d := decomposedZeroSlotMomentData K S P R ω η ξ W
    d.allowedRow (u * a.val ^ 6) ∧
      d.rowCharacter (u * a.val ^ 6) = d.rowCharacter u ∧
      ∀ I : Ideal (𝓞 K), maskValue d (u * a.val ^ 6) I =
        maskValue d u I * (if IsCoprime I a.val.val then 1 else 0) := by
  refine ⟨completeIdealIsExterior_mul_sixth S u a hu,
    completeIdealRowCharacter_mul_sixth S P R u a hu ξ, ?_⟩
  intro I
  exact completeIdealCommonMask_sixth S u a I

end HeckeSkeleton.Moments.UniformAmplify
