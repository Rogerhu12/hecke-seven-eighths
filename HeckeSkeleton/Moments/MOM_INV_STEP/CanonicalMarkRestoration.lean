import HeckeSkeleton.Moments.MOM_INV_STEP.SecondOverlapColumns

/-!
# Original mark lists restored by the actual child zeros

Priority temporarily removes primes dividing an extracted ideal. When
that ideal divides the product of the child puncture and averaged label,
the literal child coefficient already vanishes at every removed prime.
The full original lists and original squarefree column pool can therefore
be restored by equality before positive enlargement.

For the second pass the extracted ideal is the fixed original g times
the new Moebius divisor v. The new puncture contains g/d₂, and the new
label contains d₂ v. The needed divisibility is proved from the actual
original common-factor divisor decomposition.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalMarkRestoration

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers SecondSourceCharacters SecondOverlapColumns
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

variable {σ : Type*} [DecidableEq σ]

theorem mark_eq_on_coprime (slots : Finset σ)
    (lists : σ → Finset (Ideal (𝓞 K))) (a : σ → Ideal (𝓞 K) → ℂ)
    (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p)
    (E n : Ideal (𝓞 K)) (hc : IsCoprime n E) :
    divisorMark slots (residualDivisorLists E lists) a n = divisorMark slots lists a n := by
  unfold divisorMark
  apply Finset.prod_congr rfl
  intro i hi
  change (∑ p ∈ (lists i).filter (fun p => ¬p ∣ E), if p ∣ n then a i p else 0) = _
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hE : p ∣ E := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
  have hn : ¬p ∣ n := fun hd => (hprime i hi p hp).not_unit (hc.isUnit_of_dvd' hd hE)
  exact if_neg hn

theorem live_forward_label_coprime (Λ ν : HeckeCharacter K) (n f I : Ext) (ξ : Sector)
    (hlive : forwardCoefficient K S Γ D Λ ν n f I ξ ≠ 0) :
    IsCoprime n.val.val f.val.val := by
  have hsymbol : idealSymbol K Sset D n (D.generator f) ≠ 0 := by
    intro hh
    exact hlive (by simp only [forwardCoefficient, hh, zero_pow (by decide : (4 : ℕ) ≠ 0),
      zero_mul, mul_zero])
  have hfcon : sIntegerModulusContraction K Sset (D.generator f) = f.val.val := by
    simpa only [CanonicalIdealRow.generator_ofExterior, CanonicalIdealRow.ofExterior_val] using
      CanonicalIdealRow.generator_contraction K S D (CanonicalIdealRow.ofExterior K S f)
  have hmask : idealCoprimeMask f.val.val n.val.val ≠ 0 := by
    rw [← hfcon, ← symbol_self_pair]
    exact mul_ne_zero (star_ne_zero.mpr hsymbol) hsymbol
  exact (idealCoprimeMask_ne_zero _ _).mp hmask

/-- A retained actual puncture and fourth-power label already kill
every deleted prime. The original coefficient function a is unchanged. -/
theorem restore_original_lists (Λ ν : HeckeCharacter K) (n f I : Ext) (ξ : Sector)
    (R E : Ideal (𝓞 K)) (hE : E ∣ R * f.val.val)
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p) :
    forwardCoefficient K S Γ D Λ ν n f I ξ * idealCoprimeMask R n.val.val *
        divisorMark slots (residualDivisorLists E lists) a n.val.val =
      forwardCoefficient K S Γ D Λ ν n f I ξ * idealCoprimeMask R n.val.val *
        divisorMark slots lists a n.val.val := by
  by_cases hc : forwardCoefficient K S Γ D Λ ν n f I ξ = 0
  · simp only [hc, zero_mul]
  by_cases hm : idealCoprimeMask R n.val.val = 0
  · simp only [hm, mul_zero, zero_mul]
  have hR := (idealCoprimeMask_ne_zero _ _).mp hm
  have hf := live_forward_label_coprime K S Γ D Λ ν n f I ξ hc
  have hnE : IsCoprime n.val.val E := (hR.mul_right hf).of_isCoprime_of_dvd_right hE
  rw [mark_eq_on_coprime K slots lists a hprime E n.val.val hnE]

theorem coefficient_zero_outside_coprime_pool (Λ ν : HeckeCharacter K)
    (n f I : Ext) (ξ : Sector) (R E : Ideal (𝓞 K)) (hE : E ∣ R * f.val.val)
    (hbad : ¬IsCoprime n.val.val E) :
    forwardCoefficient K S Γ D Λ ν n f I ξ * idealCoprimeMask R n.val.val = 0 := by
  by_contra h
  obtain ⟨hc, hm⟩ := mul_ne_zero_iff.mp h
  have hR := (idealCoprimeMask_ne_zero _ _).mp hm
  have hf := live_forward_label_coprime K S Γ D Λ ν n f I ξ hc
  exact hbad ((hR.mul_right hf).of_isCoprime_of_dvd_right hE)

/-- Restoring all columns is an exact equality. No preferred ideal or
unit sector is substituted for a vanishing deleted source column. -/
theorem restore_original_pool (Λ ν : HeckeCharacter K) (T : Finset Ext)
    (f I : Ext) (ξ : Sector) (R E : Ideal (𝓞 K)) (hE : E ∣ R * f.val.val)
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ T with IsCoprime n.val.val E,
      forwardCoefficient K S Γ D Λ ν n f I ξ * idealCoprimeMask R n.val.val *
        divisorMark slots lists a n.val.val * W ((n.val.val.absNorm : ℝ) / X)) =
      ∑ n ∈ T, forwardCoefficient K S Γ D Λ ν n f I ξ * idealCoprimeMask R n.val.val *
        divisorMark slots lists a n.val.val * W ((n.val.val.absNorm : ℝ) / X) := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hbad : ¬IsCoprime n.val.val E := by
    intro hc
    exact hnot (Finset.mem_filter.mpr ⟨hn, hc⟩)
  rw [coefficient_zero_outside_coprime_pool K S Γ D Λ ν n f I ξ R E hE hbad,
    zero_mul, zero_mul]

/-- The original g is computed only from its original inverse pair.
The independently introduced v is not inserted into that gcd. -/
theorem second_extracted_dvd (x₁ x₂ j d₂ v : Ext) (R : Ideal (𝓞 K))
    (hd₂ : d₂.val.val ∣ (ActualInverseFactors.common K Sset x₁ x₂).val.val) :
    (ActualInverseFactors.common K Sset x₁ x₂).val.val * v.val.val ∣
      (R * (residual K S (ActualInverseFactors.common K Sset x₁ x₂) d₂).val.val) *
        (exteriorMul K Sset (exteriorMul K Sset j d₂) v).val.val := by
  have hg := (FirstSourceDecomposition.squarefree_divisor_decomposition
    (ActualInverseFactors.common K Sset x₁ x₂).val d₂.val
    (ActualInverseFactors.common_squarefree K Sset x₁ x₂) hd₂).1
  refine ⟨R * j.val.val, ?_⟩
  change R * (residual K S (ActualInverseFactors.common K Sset x₁ x₂) d₂).val.val *
      ((j.val.val * d₂.val.val) * v.val.val) =
    ((ActualInverseFactors.common K Sset x₁ x₂).val.val * v.val.val) * (R * j.val.val)
  rw [hg]
  simp only [SecondOverlapColumns.residual, ActualInverseFactors.residual_val,
    FirstSourceDecomposition.pairResidual,
    FirstSourceDecomposition.divisorResidual]
  ring

/-- Exact restoration for the real second child: puncture R(g/d₂),
label j d₂ v, original g, original lists and original weights. -/
theorem second_original_lists (Λ ν : HeckeCharacter K) (x₁ x₂ j d₂ v n I : Ext)
    (ξ : Sector) (R : Ideal (𝓞 K))
    (hd₂ : d₂.val.val ∣ (ActualInverseFactors.common K Sset x₁ x₂).val.val)
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p) :
    forwardCoefficient K S Γ D Λ ν n (exteriorMul K Sset (exteriorMul K Sset j d₂) v) I ξ *
        idealCoprimeMask
          (R * (residual K S (ActualInverseFactors.common K Sset x₁ x₂) d₂).val.val) n.val.val *
        divisorMark slots
          (residualDivisorLists ((ActualInverseFactors.common K Sset x₁ x₂).val.val * v.val.val)
            lists) a n.val.val =
      forwardCoefficient K S Γ D Λ ν n (exteriorMul K Sset (exteriorMul K Sset j d₂) v) I ξ *
        idealCoprimeMask
          (R * (residual K S (ActualInverseFactors.common K Sset x₁ x₂) d₂).val.val) n.val.val *
        divisorMark slots lists a n.val.val :=
  restore_original_lists K S Γ D Λ ν n _ I ξ _ _
    (second_extracted_dvd K S x₁ x₂ j d₂ v R hd₂) slots lists a hprime

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalMarkRestoration

end
