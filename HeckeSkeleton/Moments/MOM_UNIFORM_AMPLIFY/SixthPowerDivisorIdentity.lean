import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerMasks
import HeckeGeneral.Analysis.IdealAmplifierSmallPower

/-!
# Exact sixth-power divisor expansion of the original ideal polynomial

The finite envelope is constructed from the actual parent support and the
finitely many divisor-scale child supports.  No support estimate or analytic
moment bound is assumed.  The complete common mask is retained throughout,
including the primes shared with the original base row.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped BigOperators Classical nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Only the profile is pulled back.  All original arithmetic fields,
backgrounds, directions and fixed-place zeros remain unchanged. -/
def sixthRootInverseData (d : MomentData K ω ψ) : MomentData K ω ψ :=
  { d with inverseTest := {
      profile u t y := d.inverseTest.profile (sixthPowerFreePart u) t y
      support u t D := d.inverseTest.support (sixthPowerFreePart u) t D
      support_spec u t D I :=
        d.inverseTest.support_spec (sixthPowerFreePart u) t D I } }

theorem sixthRootInverseData_profile_sixth (d : MomentData K ω ψ)
    (u a : NonzeroIdeal K) (t y : ℝ) :
    (sixthRootInverseData d).inverseTest.profile (u * a ^ 6) t y =
      (sixthRootInverseData d).inverseTest.profile u t y := by
  simp only [sixthRootInverseData, sixthPowerFreePart_mul_sixth]

theorem sixthPowerFreePart_eq_self {u : NonzeroIdeal K}
    (hu : SixthPowerFreeIdeal u) : sixthPowerFreePart u = u := by
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  apply Finsupp.ext
  intro p
  change primeExponents (sixthPowerFreePart u) p = primeExponents u p
  rw [primeExponents_sixthPowerFreePart,
    Nat.mod_eq_of_lt ((sixthPowerFreeIdeal_iff_primeExponents_lt u).mp hu p)]

theorem inversePolynomial_sixthRoot_eq (d : MomentData K ω ψ)
    {u : NonzeroIdeal K} (hu : SixthPowerFreeIdeal u) (D t : ℝ) :
    inversePolynomial (sixthRootInverseData d) u D t =
      inversePolynomial d u D t := by
  simp only [inversePolynomial, sixthRootInverseData, sixthPowerFreePart_eq_self hu, maskValue] <;>
    rfl

/-- The literal coefficient, including the full row mask, before inserting
the smooth profile and the square-root normalization. -/
def inverseRowCoefficient (d : MomentData K ω ψ)
    (u I : NonzeroIdeal K) : ℂ :=
  (UniqueFactorizationMonoid.moebius I.val : ℂ) *
    heckeIdealCoefficient K d.inverseBackground I *
    heckeIdealCoefficient K (d.rowCharacter u) I ^ d.direction *
    maskValue d u I.val

theorem inversePolynomial_sum_coeff (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial d u D t = (Real.sqrt D : ℂ)⁻¹ *
      ∑ I ∈ d.inverseTest.support u t D,
        inverseRowCoefficient d u I * d.inverseTest.profile u t (idealNorm K I / D) := by
  unfold inversePolynomial inverseRowCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  ring

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem completeIdealCommonMask_mul (u I J : NonzeroIdeal K) :
    (if completeIdealCommonMask K S u (I * J).val then (1 : ℂ) else 0) =
      (if completeIdealCommonMask K S u I.val then (1 : ℂ) else 0) *
        (if completeIdealCommonMask K S u J.val then (1 : ℂ) else 0) := by
  have hgood :
      (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ (I * J).val →
        p ∉ S ∧ (6 : 𝓞 K) ∉ p.asIdeal) ↔
      (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val →
        p ∉ S ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧
      (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J.val →
        p ∉ S ∧ (6 : 𝓞 K) ∉ p.asIdeal) := by
    constructor
    · intro h
      exact ⟨fun p hp => h p (dvd_mul_of_dvd_left hp _),
        fun p hp => h p (dvd_mul_of_dvd_right hp _)⟩
    · rintro ⟨hI, hJ⟩ p hp
      rcases p.prime.dvd_mul.mp hp with h | h
      · exact hI p h
      · exact hJ p h
  have hcop : IsCoprime (I * J).val u.val ↔
      IsCoprime I.val u.val ∧ IsCoprime J.val u.val := IsCoprime.mul_left_iff
  simp only [completeIdealCommonMask, decide_eq_true_eq, hgood, hcop]
  split_ifs <;> simp_all

theorem inverseRowCoefficient_squarefree_union (d : MomentData K ω ψ)
    (hmask : d.commonMask = completeIdealCommonMask K S) (u : NonzeroIdeal K)
    (A B : Finset (HeightOneSpectrum (𝓞 K))) (hAB : Disjoint A B) :
    inverseRowCoefficient d u (squarefreeIdeal K (A ∪ B)) =
      inverseRowCoefficient d u (squarefreeIdeal K A) *
        inverseRowCoefficient d u (squarefreeIdeal K B) := by
  unfold inverseRowCoefficient
  rw [moebius_squarefree_union K A B hAB, squarefreeIdeal_union K A B hAB,
    heckeIdealCoefficient_mul, heckeIdealCoefficient_mul, mul_zpow]
  simp only [maskValue, hmask]
  rw [completeIdealCommonMask_mul]
  ring

theorem inverseRowCoefficient_sixth (d : MomentData K ω ψ)
    (hmask : d.commonMask = completeIdealCommonMask K S)
    (u : NonzeroIdeal K) (a : ExteriorIdeal K S)
    (hchar : d.rowCharacter (u * a.val ^ 6) = d.rowCharacter u)
    (I : NonzeroIdeal K) :
    inverseRowCoefficient d (u * a.val ^ 6) I =
      inverseRowCoefficient d u I * (if IsCoprime I.val a.val.val then 1 else 0) := by
  simp only [inverseRowCoefficient, hchar, maskValue, hmask]
  rw [completeIdealCommonMask_sixth]
  ring

omit [Fintype S] in
theorem squarefreeIdeal_coprime_iff_subset
    (P Q : Finset (HeightOneSpectrum (𝓞 K))) (a : NonzeroIdeal K)
    (hP : ∀ p ∈ P, p.asIdeal ∣ a.val)
    (hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ a.val)
    (A : Finset (HeightOneSpectrum (𝓞 K))) (hA : A ⊆ P ∪ Q) :
    IsCoprime (squarefreeIdeal K A).val a.val ↔ A ⊆ Q := by
  change IsCoprime (∏ p ∈ A, p.asIdeal) a.val ↔ _
  rw [IsCoprime.prod_left_iff]
  constructor
  · intro hc p hp
    rcases Finset.mem_union.mp (hA hp) with hpP | hpQ
    · exact False.elim ((primeIdeal_coprime_iff_not_dvd K p _).mp
        (hc p hp) (hP p hpP))
    · exact hpQ
  · intro h p hp
    exact (primeIdeal_coprime_iff_not_dvd K p _).mpr (hQ p (h hp))

variable {S}

def inverseEnvelopePolynomial (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (D t : ℝ) : ℂ :=
  (Real.sqrt D : ℂ)⁻¹ * ∑ A ∈ E.powerset,
    inverseRowCoefficient d u (squarefreeIdeal K A) *
      d.inverseTest.profile u t (idealNorm K (squarefreeIdeal K A) / D)

theorem inversePolynomial_eq_envelope (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (D t : ℝ)
    (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hcover : ∀ I ∈ d.inverseTest.support u t D, idealPrimeSupport K I ⊆ E) :
    inversePolynomial d u D t = inverseEnvelopePolynomial d u E D t := by
  rw [inversePolynomial_sum_coeff]
  unfold inverseEnvelopePolynomial
  congr 1
  have hsq : ∀ I : NonzeroIdeal K,
      inverseRowCoefficient d u I * d.inverseTest.profile u t (idealNorm K I / D) ≠ 0 →
      Squarefree I.val := by
    intro I hn
    by_contra h
    simp [inverseRowCoefficient, UniqueFactorizationMonoid.moebius_of_not_squarefree h] at hn
  apply Finset.sum_bij_ne_zero (fun I _ _ => idealPrimeSupport K I)
  · intro I hI _
    exact Finset.mem_powerset.mpr (hcover I hI)
  · intro I _ hi J _ hj hij
    calc
      I = squarefreeIdeal K (idealPrimeSupport K I) :=
        (squarefreeIdeal_primeSupport K I (hsq I hi)).symm
      _ = squarefreeIdeal K (idealPrimeSupport K J) := congrArg _ hij
      _ = J := squarefreeIdeal_primeSupport K J (hsq J hj)
  · intro A hA hn
    have hmem : squarefreeIdeal K A ∈ d.inverseTest.support u t D := by
      apply (d.inverseTest.support_spec u t D _).mpr
      exact right_ne_zero_of_mul hn
    exact ⟨squarefreeIdeal K A, hmem, hn, idealPrimeSupport_squarefreeIdeal K A⟩
  · intro I _ hi
    rw [squarefreeIdeal_primeSupport K I (hsq I hi)]

theorem inverseEnvelopePolynomial_disjoint_union
    (d : MomentData K ω ψ) (hmask : d.commonMask = completeIdealCommonMask K S)
    (u : NonzeroIdeal K) (P Q : Finset (HeightOneSpectrum (𝓞 K)))
    (hd : Disjoint P Q) {D : ℝ} (hD : 0 < D) (t : ℝ) :
    inverseEnvelopePolynomial d u (P ∪ Q) D t =
      ∑ A ∈ P.powerset,
        inverseRowCoefficient d u (squarefreeIdeal K A) *
          (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹ *
          inverseEnvelopePolynomial d u Q (D / idealNorm K (squarefreeIdeal K A)) t := by
  unfold inverseEnvelopePolynomial
  rw [sum_powerset_disjoint_union P Q hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sqrt_scale_amplification hD (idealNorm_pos K (squarefreeIdeal K A))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hAB : Disjoint A B := hd.mono
    (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)
  rw [inverseRowCoefficient_squarefree_union S d hmask u A B hAB,
    idealNorm_squarefree_union K A B hAB, div_div_eq_mul_div]
  ring

theorem inverseEnvelopePolynomial_sixth
    (d : MomentData K ω ψ) (hmask : d.commonMask = completeIdealCommonMask K S)
    (u : NonzeroIdeal K) (a : ExteriorIdeal K S)
    (hchar : d.rowCharacter (u * a.val ^ 6) = d.rowCharacter u)
    (htest : ∀ t y, d.inverseTest.profile (u * a.val ^ 6) t y =
      d.inverseTest.profile u t y)
    (P Q : Finset (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ p ∈ P, p.asIdeal ∣ a.val.val)
    (hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ a.val.val) (D t : ℝ) :
    inverseEnvelopePolynomial d (u * a.val ^ 6) (P ∪ Q) D t =
      inverseEnvelopePolynomial d u Q D t := by
  unfold inverseEnvelopePolynomial
  congr 1
  have he : (P ∪ Q).powerset.filter (fun A => A ⊆ Q) = Q.powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans Finset.subset_union_right, h⟩⟩
  rw [← he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  rw [inverseRowCoefficient_sixth S d hmask u a hchar,
    squarefreeIdeal_coprime_iff_subset P Q a.val hP hQ A (Finset.mem_powerset.mp hA),
    htest]
  by_cases h : A ⊆ Q <;> simp [h]

/-- The original `inversePolynomial`, with its exact finite supports, has
the complete sixth-power divisor identity.  Its right side uses the same
profile at the amplified row and at every divisor scale. -/
theorem inversePolynomial_sixth_power_divisor_identity
    (d : MomentData K ω ψ) (hmask : d.commonMask = completeIdealCommonMask K S)
    (u : NonzeroIdeal K) (a : ExteriorIdeal K S)
    (hchar : d.rowCharacter (u * a.val ^ 6) = d.rowCharacter u)
    (htest : ∀ t y, d.inverseTest.profile (u * a.val ^ 6) t y =
      d.inverseTest.profile u t y)
    {D : ℝ} (hD : 0 < D) (t : ℝ) :
    inversePolynomial d u D t =
      ∑ A ∈ (idealPrimeSupport K a.val).powerset,
        inverseRowCoefficient d u (squarefreeIdeal K A) *
          (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹ *
          inversePolynomial d (u * a.val ^ 6)
            (D / idealNorm K (squarefreeIdeal K A)) t := by
  let P := idealPrimeSupport K a.val
  let F := d.inverseTest.support u t D ∪
    P.powerset.biUnion (fun A => d.inverseTest.support (u * a.val ^ 6) t
      (D / idealNorm K (squarefreeIdeal K A)))
  let Q := finitePrimeEnvelope K F \ P
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hq).2 hp
  have hEF : finitePrimeEnvelope K F ⊆ P ∪ Q := by
    intro p hp
    by_cases h : p ∈ P
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp, h⟩)
  have hP : ∀ p ∈ P, p.asIdeal ∣ a.val.val := fun p hp =>
    (mem_idealPrimeSupport_iff K a.val p).mp hp
  have hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ a.val.val := by
    intro p hp h
    exact (Finset.mem_sdiff.mp hp).2 ((mem_idealPrimeSupport_iff K a.val p).mpr h)
  have hparent : ∀ I ∈ d.inverseTest.support u t D,
      idealPrimeSupport K I ⊆ P ∪ Q := by
    intro I hI
    exact (idealPrimeSupport_subset_envelope K F I (Finset.mem_union_left _ hI)).trans hEF
  rw [inversePolynomial_eq_envelope d u D t (P ∪ Q) hparent,
    inverseEnvelopePolynomial_disjoint_union d hmask u P Q hd hD t]
  apply Finset.sum_congr rfl
  intro A hA
  have hchild : ∀ I ∈ d.inverseTest.support (u * a.val ^ 6) t
      (D / idealNorm K (squarefreeIdeal K A)), idealPrimeSupport K I ⊆ P ∪ Q := by
    intro I hI
    apply (idealPrimeSupport_subset_envelope K F I ?_).trans hEF
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨A, hA, hI⟩)
  rw [inversePolynomial_eq_envelope d (u * a.val ^ 6)
    (D / idealNorm K (squarefreeIdeal K A)) t (P ∪ Q) hchild,
    inverseEnvelopePolynomial_sixth d hmask u a hchar htest P Q hP hQ]

end HeckeSkeleton.Moments.UniformAmplify
