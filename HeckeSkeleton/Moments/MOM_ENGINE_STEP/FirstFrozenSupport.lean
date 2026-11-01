import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCharacterSource
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SexticHilbertReciprocity

/-!
# Frozen first-transform scalars retain the actual coprimality support

The first divisor factors have their original zero extensions.  Their
nonvanishing forces each residual ideal to avoid both the actual mask
divisor and the active common ideal.  The proof uses the genuine sextic
noncoprime vanishing theorem, for arbitrary actual generators.

The support restriction is proved for the entire summand.  Any centered
coefficient, normalization, Fourier twist, or other scalar remains in it.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- The source dictionary's nonunit zeros already imply base-ideal
coprimality; no conductor or reciprocal phase premise is used. -/
theorem generated_character_nonzero_coprime
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (hne : generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ b) ≠ 0) :
    IsCoprime I.val J.val := by
  by_contra hcop
  have hs : I.val ⊔ J.val ≠ ⊤ := fun hh =>
    hcop (Ideal.isCoprime_iff_sup_eq.mpr hh)
  have hz := (ArithmeticContext.actual_sextic_noncoprime_vanishing
    A I J a b ha hb hs).1
  apply hne
  rw [generatedIdealCharacter_mk, hz, map_zero]

theorem first_left_frozen_support
    (I D R : A.Exterior) (a δ r : A.R)
    (ha : A.Generates I a) (hδ : A.Generates D δ) (hr : A.Generates R r)
    (hne : firstLeftDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ I a ha)
      (generatedOriginalColumn (σ := σ) hΓ R r hr) δ ≠ 0) :
    IsCoprime I.val (D.val * R.val) := by
  change (generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ δ) *
      generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ r)) *
        generatedIdealCharacter (σ := σ) R r hr (Ideal.Quotient.mk _ a) ≠ 0 at hne
  have hfirst := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1
  exact (generated_character_nonzero_coprime I D a δ ha hδ hfirst.1).mul_right
    (generated_character_nonzero_coprime I R a r ha hr hfirst.2)

theorem first_right_frozen_support
    (I D R : A.Exterior) (a δ r : A.R)
    (ha : A.Generates I a) (hδ : A.Generates D δ) (hr : A.Generates R r)
    (hne : firstRightDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ I a ha)
      (generatedOriginalColumn (σ := σ) hΓ R r hr) δ ≠ 0) :
    IsCoprime I.val (D.val * R.val) := by
  change (generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ δ) *
      generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ r)) *
        star (generatedIdealCharacter (σ := σ) R r hr (Ideal.Quotient.mk _ a)) ≠ 0 at hne
  have hfirst := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1
  exact (generated_character_nonzero_coprime I D a δ ha hδ hfirst.1).mul_right
    (generated_character_nonzero_coprime I R a r ha hr hfirst.2)

theorem first_frozen_paired_support
    (I J D R : A.Exterior) (a b δ r : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b)
    (hδ : A.Generates D δ) (hr : A.Generates R r) (c d : ℂ)
    (hne : (c * firstLeftDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ I a ha)
      (generatedOriginalColumn (σ := σ) hΓ R r hr) δ) *
        star (d * firstRightDivisorFactor
          (generatedOriginalColumn (σ := σ) hΓ J b hb)
          (generatedOriginalColumn (σ := σ) hΓ R r hr) δ) ≠ 0) :
    IsCoprime (I.val * J.val) (D.val * R.val) := by
  have hleft : firstLeftDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ I a ha)
      (generatedOriginalColumn (σ := σ) hΓ R r hr) δ ≠ 0 := by
    intro hz
    apply hne
    rw [hz, mul_zero, zero_mul]
  have hright : firstRightDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ J b hb)
      (generatedOriginalColumn (σ := σ) hΓ R r hr) δ ≠ 0 := by
    intro hz
    apply hne
    rw [hz, mul_zero, star_zero, mul_zero]
  exact (first_left_frozen_support hΓ I D R a δ r ha hδ hr hleft).mul_left
    (first_right_frozen_support hΓ J D R b δ r hb hδ hr hright)

/-- The complete left polynomial can be restricted to the actual
coprime columns without splitting any coefficient into pieces. -/
theorem first_left_whole_polynomial_support {ι : Type*}
    (S : Finset ι) (I : ι → A.Exterior) (a : ι → A.R)
    (ha : ∀ i, A.Generates (I i) (a i))
    (D R : A.Exterior) (δ r : A.R)
    (hδ : A.Generates D δ) (hr : A.Generates R r) (c G : ι → ℂ) :
    (∑ i ∈ S, c i * firstLeftDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i))
      (generatedOriginalColumn (σ := σ) hΓ R r hr) δ * G i) =
      ∑ i ∈ S with IsCoprime (I i).val (D.val * R.val),
        c i * firstLeftDivisorFactor
          (generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i))
          (generatedOriginalColumn (σ := σ) hΓ R r hr) δ * G i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : IsCoprime (I i).val (D.val * R.val)
  · rw [if_pos hi]
  · rw [if_neg hi]
    have hz : firstLeftDivisorFactor
        (generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i))
        (generatedOriginalColumn (σ := σ) hΓ R r hr) δ = 0 := by
      by_contra hn
      exact hi (first_left_frozen_support hΓ (I i) D R (a i) δ r (ha i) hδ hr hn)
    rw [hz, mul_zero, zero_mul]

theorem first_right_whole_polynomial_support {ι : Type*}
    (S : Finset ι) (I : ι → A.Exterior) (a : ι → A.R)
    (ha : ∀ i, A.Generates (I i) (a i))
    (D R : A.Exterior) (δ r : A.R)
    (hδ : A.Generates D δ) (hr : A.Generates R r) (c G : ι → ℂ) :
    (∑ i ∈ S, c i * firstRightDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i))
      (generatedOriginalColumn (σ := σ) hΓ R r hr) δ * G i) =
      ∑ i ∈ S with IsCoprime (I i).val (D.val * R.val),
        c i * firstRightDivisorFactor
          (generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i))
          (generatedOriginalColumn (σ := σ) hΓ R r hr) δ * G i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : IsCoprime (I i).val (D.val * R.val)
  · rw [if_pos hi]
  · rw [if_neg hi]
    have hz : firstRightDivisorFactor
        (generatedOriginalColumn (σ := σ) hΓ (I i) (a i) (ha i))
        (generatedOriginalColumn (σ := σ) hΓ R r hr) δ = 0 := by
      by_contra hn
      exact hi (first_right_frozen_support hΓ (I i) D R (a i) δ r (ha i) hδ hr hn)
    rw [hz, mul_zero, zero_mul]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_frozen_paired_support
#print axioms HeckeSkeleton.Moments.EngineStep.first_left_whole_polynomial_support

