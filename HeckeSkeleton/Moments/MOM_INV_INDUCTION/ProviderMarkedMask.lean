import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOverlap
import HeckeSkeleton.Moments.MOM_BASE.PairedContext

/-! The original exterior and row masks through the initial overlap. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMask

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.MOM_BASE.Paired
open HeckePort.Moments ProviderMarkedOverlap
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- The original prime exclusions, independent of the moving row. -/
def outside (good : HeightOneSpectrum (𝓞 K) → Prop) (I : Ideal (𝓞 K)) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → good p

theorem outside_mul (good : HeightOneSpectrum (𝓞 K) → Prop)
    (I J : Ideal (𝓞 K)) : outside good (I * J) ↔ outside good I ∧ outside good J := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (hp.trans (dvd_mul_right _ _)),
      fun p hp => h p (hp.trans (dvd_mul_left _ _))⟩
  · rintro ⟨hI, hJ⟩ p hp
    exact ((p.prime.dvd_mul).mp hp).elim (hI p) (hJ p)

def value (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u I : Ideal (𝓞 K)) : ℂ :=
  if outside good I ∧ IsCoprime I u then 1 else 0

theorem value_mul (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u I J : Ideal (𝓞 K)) : value good u (I * J) = value good u I * value good u J := by
  simp only [value, outside_mul, IsCoprime.mul_left_iff]
  split_ifs <;> simp_all

theorem value_one (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u : Ideal (𝓞 K)) : value good u 1 = 1 := by
  have hgood : outside good 1 := by
    intro p hp
    exact (p.irreducible.not_isUnit (isUnit_of_dvd_one hp)).elim
  simp only [value, hgood, isCoprime_one_left, and_self, if_true]

theorem value_prod {ι : Type*} (I : Finset ι)
    (good : HeightOneSpectrum (𝓞 K) → Prop) (u : Ideal (𝓞 K))
    (n : ι → Ideal (𝓞 K)) :
    value good u (∏ i ∈ I, n i) = ∏ i ∈ I, value good u (n i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, value_one]
  | @insert i I hi ih => rw [Finset.prod_insert hi, value_mul, Finset.prod_insert hi, ih]

theorem value_sq (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u I : Ideal (𝓞 K)) : value good u I * value good u I = value good u I := by
  unfold value
  split_ifs <;> norm_num

theorem norm_value_le (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u I : Ideal (𝓞 K)) : ‖value good u I‖ ≤ 1 := by
  unfold value
  split_ifs <;> norm_num

/-- Every original prime exclusion and the row coprimality mask occur
once on the extracted ideal and once on the actual new column. -/
theorem overlap_value (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u j P : Ideal (𝓞 K)) (n : Source j P) :
    value good u n.val * value good u (j * P) =
      value good u j * value good u (forward j P n.val) := by
  have hn : n.val = j * idealQuotient j n.val :=
    (idealQuotient_mul (source_common_dvd j P n)).symm
  rw [hn, value_mul, value_mul]
  change _ = value good u j * value good u (idealQuotient j (j * idealQuotient j n.val) * P)
  have hj : j ≠ ⊥ := ne_zero_of_dvd_ne_zero n.property.1.ne_zero
    (source_common_dvd j P n)
  rw [idealQuotient_self_mul hj, value_mul]
  calc
    _ = (value good u j * value good u j) *
        (value good u (idealQuotient j n.val) * value good u P) := by ring
    _ = _ := by rw [value_sq]; ring

theorem context_value (c : TargetContext K) (u : NonzeroIdeal K)
    (I : Ideal (𝓞 K)) :
    (if contextOriginalMask K c u I then (1 : ℂ) else 0) =
      value (fun p => p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal) u.val I := by
  unfold contextOriginalMask value outside
  split_ifs <;> rfl

/-- The equality is stated on the literal `MomentData` mask used by
the original source, with its actual context formula. -/
theorem original_mask_overlap (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (u : NonzeroIdeal K) (hmask : ∀ I, d.commonMask u I = contextOriginalMask K c u I)
    (j P : Ideal (𝓞 K)) (n : Source j P) :
    maskValue d u n.val * maskValue d u (j * P) =
      maskValue d u j * maskValue d u (forward j P n.val) := by
  simp only [maskValue, hmask, context_value]
  exact overlap_value _ u.val j P n

/-- The complete extracted scalar is a row contraction, including the
original exclusion mask and all zero-extended character zeros. -/
theorem extracted_scalar_norm_le (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u j : Ideal (𝓞 K)) (χ : HeckeCharacter K) :
    ‖(moebius j : ℂ) * idealCoefficient (primeCoefficient K χ) j ^ 2 *
      value good u j‖ ≤ 1 := by
  rw [norm_mul, norm_mul]
  apply mul_le_one₀
  · exact mul_le_one₀ (HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one _)
      (norm_nonneg _) (extracted_character_norm_le j χ)
  · exact norm_nonneg _
  · exact norm_value_le good u j

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMask
