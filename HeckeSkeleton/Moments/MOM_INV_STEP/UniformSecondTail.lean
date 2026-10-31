import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalTailBound
import HeckeSkeleton.Moments.MOM_INV_STEP.JointMaskGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.MaskCounting
import HeckeSkeleton.Moments.MOM_INV_STEP.InverseCoefficientBounds
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonSplit

/-!
# Uniform tails for the actual intermediate inverse coefficient

This is the high-frequency part of the genuine second Poisson identity.
It retains the conjugate-first coefficient orientation and the original
unit subgroup. The external mask is empty; the actual principal mask is
counted and its norm is combined with the disjoint active conductor.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondTail

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open CanonicalBlock CanonicalPoissonSplit CanonicalTailBound FirstDualTruncation
  FirstMaskGeometry JointMaskGeometry PrimitivePoissonSource ConductorMasks ActualPoissonScale
  FixedTripleFibers CanonicalChildren PrincipalBudget FirstInversePoisson
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "e" => unitIdeal K S

theorem externalMask_unit : externalMask K S e = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
  have hdiv := (FirstSourceDecomposition.mem_primeSupport e.val p.val).mp p.property
  exact p.val.prime.not_dvd_one (by simpa only [unitIdeal_val] using hdiv)

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

theorem second_norm_product_bound (x₁ x₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ principalMask K S (pairSupport K S D x₁ x₂ e e)
      (pairExponent K S x₁ x₂ e e)) :
    (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
      ((primitiveIdeal (pairSupport K S D x₁ x₂ e e).support
        (pairExponent K S x₁ x₂ e e)).absNorm : ℝ) ≤
      (x₁.val.val.absNorm : ℝ) * (x₂.val.val.absNorm : ℝ) := by
  have hδ' : δ ⊆ actualMask K S D e x₁ x₂ e e := by
    simpa only [actualMask, externalMask_unit, Finset.empty_union] using hδ
  simpa only [unitIdeal_val, map_one, Nat.cast_one, one_mul] using
    actual_norm_product_bound K S D e x₁ x₂ e e δ hδ'

theorem exists_second_mask_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x₁ x₂ : Ext,
      (2 : ℝ) ^ (principalMask K S (pairSupport K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e)).card ≤
        A * (x₁.val.val.absNorm : ℝ) * (x₂.val.val.absNorm : ℝ) := by
  obtain ⟨A, hA, hb⟩ := MaskCounting.exists_actual_pair_mask_bound K S D 1 (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro x₁ x₂
  have hQ : ∀ p ∈ FirstSourceDecomposition.primeSupport e.val, p ∉ Sset :=
    fun p hp => e.property p ((FirstSourceDecomposition.mem_primeSupport e.val p).mp hp)
  have h := hb (FirstSourceDecomposition.primeSupport e.val) hQ e.val.val
    (nonZeroDivisors.coe_ne_zero e.val)
    (fun p hp => (FirstSourceDecomposition.mem_primeSupport e.val p).mp hp) x₁ x₂ e e
  change (2 : ℝ) ^ (externalMask K S e ∪ principalMask K S
    (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e)).card ≤ _ at h
  simpa only [externalMask_unit, Finset.empty_union, unitIdeal_val,
    Ideal.absNorm_mul, map_one, Nat.cast_mul, Nat.cast_one, one_mul, Real.rpow_one,
    mul_assoc] using h

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
/-- Every restriction of the genuine second source has a uniform tail
bound. The coefficient is the actual retained-divisor inverse column. -/
theorem exists_inverse_tail_bound_uniform
    (slotCap : ℕ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (Rmax tauMin savingMax : ℝ) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hsavingMax : 0 ≤ savingMax) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
      (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
      (j : Ideal (𝓞 K)) (d : OS) (P : Finset (Ext × Ext))
      (φ : SchwartzMap V ℂ) (ρ : {r : ℝ // 0 < r}) (X Z R tau saving : ℝ),
      1 ≤ Z → 0 ≤ R → R ≤ Rmax → tauMin ≤ tau →
      0 ≤ saving → saving ≤ savingMax → 1 ≤ X →
      C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ C.columns γ, (n.val.val.absNorm : ℝ) ≤ X) →
      P ⊆ C.columns γ ×ˢ C.columns γ →
      ρ.val * X ^ 2 ≤ Z ^ R →
      ‖SecondPoissonSplit.tailSource K S D Γ hΓ μv
        (DivisorInverseColumn.coefficient K S D C γ j d) P φ h hlc hcs ρ
        (Z ^ (R + tau))‖ ≤
        A * (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (fieldConstant K / ρ.val) * X ^ 6 * Z ^ (-saving) := by
  obtain ⟨s, At, hAt, ht⟩ := exists_primitive_tail_bound_uniform
    K S D Γ hΓ μv ν h hlc hcs Rmax tauMin savingMax hRmax htauMin hsavingMax
  obtain ⟨Ac, hAc, hc⟩ := InverseCoefficientBounds.exists_coefficient_bound K S D slotCap 1
    (by norm_num)
  obtain ⟨Am, hAm, hm⟩ := exists_second_mask_bound K S D
  obtain ⟨Ai, hAi, hi⟩ := exists_ideal_count_bound K
  refine ⟨s, Ai ^ 2 * Ac ^ 2 * Am * At, by positivity, ?_⟩
  intro σ Θ ψ C γ j d P φ ρ X Z R tau saving
    hZ hR hRR htau hsaving hss hX hslots ha hn hP hbudget
  let U := At * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
    (fieldConstant K / ρ.val) * Z ^ (-saving)
  have hU : 0 ≤ U := by
    dsimp only [U]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hAt (apply_nonneg _ _))
        (div_nonneg (fieldConstant_nonneg K) ρ.property.le))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  have hX0 := zero_le_one.trans hX
  have hAc0 := zero_le_one.trans hAc
  have hAm0 := zero_le_one.trans hAm
  have hAi0 := zero_le_one.trans hAi
  have hpoint (x : Ext × Ext) (hx : x ∈ P) :
      ‖SecondPoissonSplit.sourceWeight K S
          (DivisorInverseColumn.coefficient K S D C γ j d) x *
        dualTail K S D Γ μv (SecondPoissonSplit.pairBlock K S D Γ hΓ x φ h hlc hcs ρ)
          (Z ^ (R + tau))‖ ≤
      (Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * X) ^ 2 * (Am * X ^ 2) * U := by
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.mp (hP hx)
    have hc₁ := hc C γ j d x.1 X hslots ha (hn x.1 hx₁)
    have hc₂ := hc C γ j d x.2 X hslots ha (hn x.2 hx₂)
    simp only [Real.rpow_one] at hc₁ hc₂
    have hw :
        ‖SecondPoissonSplit.sourceWeight K S
          (DivisorInverseColumn.coefficient K S D C γ j d) x‖ ≤
        (Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * X) ^ 2 := by
      rw [SecondPoissonSplit.sourceWeight, norm_mul, norm_star, pow_two]
      exact mul_le_mul hc₁ hc₂ (norm_nonneg _) (by positivity)
    have htail :
        ‖dualTail K S D Γ μv (SecondPoissonSplit.pairBlock K S D Γ hΓ x φ h hlc hcs ρ)
          (Z ^ (R + tau))‖ ≤ (Am * X ^ 2) * U := by
      apply (dualTail_norm_le K S D Γ μv _ _ U hU ?_).trans
      · intro δ hδ
        apply ht (pairSupport K S D x.1 x.2 e e) (pairExponent K S x.1 x.2 e e)
          φ ∅ ρ δ Z R tau saving hZ hR hRR htau hsaving hss
        have hδ' : δ ⊆ principalMask K S (pairSupport K S D x.1 x.2 e e)
            (pairExponent K S x.1 x.2 e e) := by
          simpa only [SecondPoissonSplit.pairBlock, primitivePairBlock, block,
            Finset.empty_union] using Finset.mem_powerset.mp hδ
        have hd := second_norm_product_bound K S D x.1 x.2 δ hδ'
        have hnprod : (x.1.val.val.absNorm : ℝ) * (x.2.val.val.absNorm : ℝ) ≤ X ^ 2 := by
          rw [pow_two]
          exact mul_le_mul (hn x.1 hx₁) (hn x.2 hx₂) (Nat.cast_nonneg _) hX0
        calc
          _ = ρ.val *
            ((sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
              ((primitiveIdeal (pairSupport K S D x.1 x.2 e e).support
                (pairExponent K S x.1 x.2 e e)).absNorm : ℝ)) := by ring
          _ ≤ ρ.val * X ^ 2 := mul_le_mul_of_nonneg_left (hd.trans hnprod) ρ.property.le
          _ ≤ _ := hbudget
      · apply mul_le_mul_of_nonneg_right _ hU
        change (2 : ℝ) ^ (∅ ∪ principalMask K S (pairSupport K S D x.1 x.2 e e)
          (pairExponent K S x.1 x.2 e e)).card ≤ Am * X ^ 2
        rw [Finset.empty_union]
        apply (hm x.1 x.2).trans
        rw [pow_two]
        gcongr
        · exact hn x.1 hx₁
        · exact hn x.2 hx₂
    rw [norm_mul]
    exact (mul_le_mul hw htail (norm_nonneg _) (sq_nonneg _)).trans_eq (by ring)
  have hcT : ((C.columns γ).card : ℝ) ≤ Ai * X := by
    have hci : ((C.columns γ).card : ℝ) ≤ ((boundedNormIdeals K X).card : ℝ) := by
      exact_mod_cast exterior_card_le_norm_count K S (C.columns γ) X hn
    exact hci.trans (hi X hX)
  have hcP : (P.card : ℝ) ≤ Ai ^ 2 * X ^ 2 := by
    have hci : (P.card : ℝ) ≤ ((C.columns γ ×ˢ C.columns γ).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hP
    apply hci.trans
    simp only [Finset.card_product, Nat.cast_mul]
    calc
      _ ≤ (Ai * X) * (Ai * X) := by gcongr
      _ = _ := by ring
  unfold SecondPoissonSplit.tailSource
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _x ∈ P, (Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * X) ^ 2 *
        (Am * X ^ 2) * U := Finset.sum_le_sum hpoint
    _ = (P.card : ℝ) *
        ((Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * X) ^ 2 * (Am * X ^ 2) * U) := by
      simp
    _ ≤ (Ai ^ 2 * X ^ 2) *
        ((Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * X) ^ 2 * (Am * X ^ 2) * U) :=
      mul_le_mul_of_nonneg_right hcP (by positivity)
    _ = _ := by dsimp only [U]; ring

include ν in
/-- A bounded family of intermediate lengths admits a common finite
Schwartz control and arbitrary normalized power saving. -/
theorem exists_normalized_inverse_tail_bound_uniform
    (slotCap : ℕ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (lengthCap Rmax tauMin desiredSaving : ℝ)
    (hcap0 : 0 ≤ lengthCap) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hdesired : 0 ≤ desiredSaving) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
      (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
      (j : Ideal (𝓞 K)) (d : OS) (P : Finset (Ext × Ext))
      (φ : SchwartzMap V ℂ) (Z M B eta R tau : ℝ),
      ∀ hZ : 1 ≤ Z,
      M ≤ lengthCap → 0 ≤ B → B ≤ lengthCap → 0 ≤ eta → eta ≤ lengthCap →
      0 ≤ R → R ≤ Rmax → tauMin ≤ tau →
      C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ C.columns γ, (n.val.val.absNorm : ℝ) ≤ Z ^ (B + eta)) →
      P ⊆ C.columns γ ×ˢ C.columns γ →
      -M + 2 * B + 2 * eta ≤ R →
      Z ^ (-B) *
        ‖SecondPoissonSplit.tailSource K S D Γ hΓ μv
          (DivisorInverseColumn.coefficient K S D C γ j d) P φ h hlc hcs
          ⟨Z ^ (-M), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩
          (Z ^ (R + tau))‖ ≤
        A * (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ * Z ^ (-desiredSaving) := by
  let saving := desiredSaving + 12 * lengthCap
  have hsaving : 0 ≤ saving := by dsimp only [saving]; positivity
  obtain ⟨s, A, hA, hb⟩ := exists_inverse_tail_bound_uniform
    K S D Γ hΓ μv ν slotCap h hlc hcs Rmax tauMin saving hRmax htauMin hsaving
  refine ⟨s, A * fieldConstant K, mul_nonneg hA (fieldConstant_nonneg K), ?_⟩
  intro σ Θ ψ C γ j d P φ Z M B eta R tau hZ hMc hB hBc heta hetac hR hRR htau
    hslots ha hn hP hradius
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  let ρ : {r : ℝ // 0 < r} := ⟨Z ^ (-M), Real.rpow_pos_of_pos hz _⟩
  have hbudget : ρ.val * (Z ^ (B + eta)) ^ 2 ≤ Z ^ R := by
    calc
      _ = Z ^ (-M + 2 * B + 2 * eta) := by
        dsimp only [ρ]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ hradius
  have hraw := hb C γ j d P φ ρ (Z ^ (B + eta)) Z R tau saving
    hZ hR hRR htau hsaving le_rfl (Real.one_le_rpow hZ (add_nonneg hB heta))
    hslots ha hn hP hbudget
  have hpref : fieldConstant K / ρ.val = fieldConstant K * Z ^ M := by
    dsimp only [ρ]
    rw [div_eq_mul_inv, Real.rpow_neg hz.le, inv_inv]
  rw [hpref] at hraw
  have hpower : Z ^ (-B) * Z ^ M * (Z ^ (B + eta)) ^ 6 * Z ^ (-saving) ≤
      Z ^ (-desiredSaving) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    repeat rw [← Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    dsimp only [saving]
    norm_num
    linarith
  have hconst : 0 ≤ (A * fieldConstant K) *
      (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hA (fieldConstant_nonneg K)) (sq_nonneg _))
      (apply_nonneg _ _)
  apply (mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hz.le _)).trans
  convert mul_le_mul_of_nonneg_left hpower hconst using 1 <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondTail

end

