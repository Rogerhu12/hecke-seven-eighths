import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveCutoff
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondTail

/-!
# Uniform saving for the actual second, common-local tail

The cutoff is the actual common/divisor scale, not a larger whole-source
frequency cap. Coefficient, mask and ideal counts are proved from the
original inverse column. The constants and Schwartz seminorm precede
the base, all source lengths, every row, label, prime list and sector.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveTail

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open FixedTripleFibers CanonicalChildren CanonicalNormPools ActualInverseFactors
  SecondSourceMasks FirstInversePoisson PrimitivePoissonSource ConductorMasks
  ActualPoissonScale SecondAdaptiveCutoff UniformSecondTail PrincipalBudget
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "e" => unitIdeal K S

include ν in
/-- This includes the principal subset, the nonprincipal subset and
the full inverse source, with the same constant and source-local cutoff. -/
theorem exists_inverse_tail_bound_uniform
    (slotCap : ℕ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (Rmax tauMin savingMax : ℝ) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hsavingMax : 0 ≤ savingMax) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
      (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
      (j : Ideal (𝓞 K)) (d : OS) (P : Finset (Ext × Ext))
      (φ : SchwartzMap V ℂ) (r : {r : ℝ // 0 < r}) (X Z tau saving : ℝ),
      1 ≤ Z → tauMin ≤ tau → 0 ≤ saving → saving ≤ savingMax → 0 < X →
      C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ C.columns γ, height K Sset n ≤ 4 * X) →
      P ⊆ C.columns γ ×ˢ C.columns γ → 16 * r.val * X ^ 2 ≤ Z ^ Rmax →
      ‖tailSourceAt K S D Γ hΓ μv (DivisorInverseColumn.coefficient K S D C γ j d)
        P φ h hlc hcs r (fineCutoff K S r X Z tau)‖ ≤
        A * (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (fieldConstant K / r.val) * (max 1 (4 * X)) ^ 6 * Z ^ (-saving) := by
  obtain ⟨s, At, hAt, ht⟩ := CanonicalAdaptiveTail.exists_primitive_tail_bound_uniform
    K S D Γ hΓ μv ν h hlc hcs Rmax tauMin savingMax hRmax htauMin hsavingMax
  obtain ⟨Ac, hAc, hc⟩ := InverseCoefficientBounds.exists_coefficient_bound K S D slotCap 1
    (by norm_num)
  obtain ⟨Am, hAm, hm⟩ := UniformSecondTail.exists_second_mask_bound K S D
  obtain ⟨Ai, hAi, hi⟩ := exists_ideal_count_bound K
  refine ⟨s, Ai ^ 2 * Ac ^ 2 * Am * At, by positivity, ?_⟩
  intro σ Θ ψ C γ j d P φ r X Z tau saving
    hZ htau hsaving hss hX hslots ha hn hP hbudget
  let Y := max 1 (4 * X)
  have hY : 1 ≤ Y := le_max_left _ _
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hnY (n : Ext) (hnmem : n ∈ C.columns γ) : (n.val.val.absNorm : ℝ) ≤ Y :=
    (hn n hnmem).trans (le_max_right _ _)
  let U := At * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
    (fieldConstant K / r.val) * Z ^ (-saving)
  have hU : 0 ≤ U := by
    dsimp only [U]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hAt (apply_nonneg _ _))
        (div_nonneg (fieldConstant_nonneg K) r.property.le))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  have hAc0 := zero_le_one.trans hAc
  have hAm0 := zero_le_one.trans hAm
  have hAi0 := zero_le_one.trans hAi
  have hpoint (x : Ext × Ext) (hx : x ∈ P) :
      ‖SecondPoissonSplit.sourceWeight K S
          (DivisorInverseColumn.coefficient K S D C γ j d) x *
        CanonicalAdaptiveTail.dualTail K S D Γ μv
          (SecondPoissonSplit.pairBlock K S D Γ hΓ x φ h hlc hcs r)
          (fineCutoff K S r X Z tau (common K Sset x.1 x.2))‖ ≤
      (Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * Y) ^ 2 * (Am * Y ^ 2) * U := by
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.mp (hP hx)
    have hc₁ := hc C γ j d x.1 Y hslots ha (hnY x.1 hx₁)
    have hc₂ := hc C γ j d x.2 Y hslots ha (hnY x.2 hx₂)
    simp only [Real.rpow_one] at hc₁ hc₂
    have hw : ‖SecondPoissonSplit.sourceWeight K S
        (DivisorInverseColumn.coefficient K S D C γ j d) x‖ ≤
        (Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * Y) ^ 2 := by
      rw [SecondPoissonSplit.sourceWeight, norm_mul, norm_star, pow_two]
      exact mul_le_mul hc₁ hc₂ (norm_nonneg _) (by positivity)
    have htail : ‖CanonicalAdaptiveTail.dualTail K S D Γ μv
        (SecondPoissonSplit.pairBlock K S D Γ hΓ x φ h hlc hcs r)
        (fineCutoff K S r X Z tau (common K Sset x.1 x.2))‖ ≤ (Am * Y ^ 2) * U := by
      have hdivisor : ∀ δ ∈
          (SecondPoissonSplit.pairBlock K S D Γ hΓ x φ h hlc hcs r).mask.powerset,
          ‖(SecondPoissonSplit.pairBlock K S D Γ hΓ x φ h hlc hcs r).prefactor δ *
            FirstDualTruncation.primitiveTail K S D Γ μv
              (SecondPoissonSplit.pairBlock K S D Γ hΓ x φ h hlc hcs r) δ
              (fineCutoff K S r X Z tau (common K Sset x.1 x.2) δ)‖ ≤ U := by
        intro δ hδ
        have hδmask : δ ⊆ FirstSourcePartition.actualMask K S D ∅ x.1 x.2 e e :=
          Finset.mem_powerset.mp hδ
        rw [actualMask_eq_commonMask] at hδmask
        apply ht (pairSupport K S D x.1 x.2 e e) (pairExponent K S x.1 x.2 e e)
          φ ∅ r δ Z tau saving
          (fineCutoff K S r X Z tau (common K Sset x.1 x.2) δ)
          hZ htau hsaving hss
        · exact actual_radius_lower K S D x.1 x.2
            (C.columns_squarefree γ x.1 hx₁) (C.columns_squarefree γ x.2 hx₂)
            r X Z Rmax hX (zero_lt_one.trans_le hZ)
            (hn x.1 hx₁) (hn x.2 hx₂) δ hδmask hbudget
        · exact fineCutoff_scaled_lower K S D x.1 x.2
            (C.columns_squarefree γ x.1 hx₁) (C.columns_squarefree γ x.2 hx₂)
            r X Z tau hX (zero_lt_one.trans_le hZ) (hn x.1 hx₁) (hn x.2 hx₂) δ
      apply (CanonicalAdaptiveTail.dualTail_norm_le K S D Γ μv _ _ U hU hdivisor).trans
      apply mul_le_mul_of_nonneg_right _ hU
      change (2 : ℝ) ^ (∅ ∪ principalMask K S (pairSupport K S D x.1 x.2 e e)
        (pairExponent K S x.1 x.2 e e)).card ≤ Am * Y ^ 2
      rw [Finset.empty_union]
      have hnprod : (x.1.val.val.absNorm : ℝ) * (x.2.val.val.absNorm : ℝ) ≤ Y ^ 2 := by
        rw [pow_two]
        exact mul_le_mul (hnY x.1 hx₁) (hnY x.2 hx₂) (Nat.cast_nonneg _) hY0
      calc
        _ ≤ Am * (x.1.val.val.absNorm : ℝ) * (x.2.val.val.absNorm : ℝ) := hm x.1 x.2
        _ = Am * ((x.1.val.val.absNorm : ℝ) * (x.2.val.val.absNorm : ℝ)) := by ring
        _ ≤ Am * Y ^ 2 := mul_le_mul_of_nonneg_left hnprod hAm0
    rw [norm_mul]
    exact (mul_le_mul hw htail (norm_nonneg _) (sq_nonneg _)).trans_eq (by ring)
  have hcT : ((C.columns γ).card : ℝ) ≤ Ai * Y := by
    have hci : ((C.columns γ).card : ℝ) ≤ ((boundedNormIdeals K Y).card : ℝ) := by
      exact_mod_cast exterior_card_le_norm_count K S (C.columns γ) Y hnY
    exact hci.trans (hi Y hY)
  have hcP : (P.card : ℝ) ≤ Ai ^ 2 * Y ^ 2 := by
    have hci : (P.card : ℝ) ≤ ((C.columns γ ×ˢ C.columns γ).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hP
    apply hci.trans
    simp only [Finset.card_product, Nat.cast_mul]
    calc
      _ ≤ (Ai * Y) * (Ai * Y) := by gcongr
      _ = _ := by ring
  unfold tailSourceAt
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _x ∈ P, (Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * Y) ^ 2 *
        (Am * Y ^ 2) * U := Finset.sum_le_sum hpoint
    _ = (P.card : ℝ) *
        ((Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * Y) ^ 2 * (Am * Y ^ 2) * U) := by simp
    _ ≤ (Ai ^ 2 * Y ^ 2) *
        ((Ac * SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) * Y) ^ 2 * (Am * Y ^ 2) * U) :=
      mul_le_mul_of_nonneg_right hcP (by positivity)
    _ = _ := by dsimp only [U, Y]; ring

include ν in
/-- Fixed length bounds give arbitrary normalized saving with the
actual fine cutoff. The finite seminorm and constant are selected first. -/
theorem exists_normalized_inverse_tail_bound
    (slotCap : ℕ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (lengthCap tauMin desiredSaving : ℝ)
    (hcap : 0 ≤ lengthCap) (htauMin : 0 < tauMin) (hdesired : 0 ≤ desiredSaving) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
      (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
      (j : Ideal (𝓞 K)) (d : OS) (P : Finset (Ext × Ext))
      (φ : SchwartzMap V ℂ) (Z M B tau : ℝ),
      ∀ hZ : 2 ≤ Z,
      -lengthCap ≤ M → M ≤ lengthCap → 0 ≤ B → B ≤ lengthCap → tauMin ≤ tau →
      C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ C.columns γ, height K Sset n ≤ 4 * Z ^ B) →
      P ⊆ C.columns γ ×ˢ C.columns γ →
      let r : {r : ℝ // 0 < r} := ⟨Z ^ (-M), Real.rpow_pos_of_pos (by linarith) _⟩
      Z ^ (-B) *
        ‖tailSourceAt K S D Γ hΓ μv (DivisorInverseColumn.coefficient K S D C γ j d)
          P φ h hlc hcs r (fineCutoff K S r (Z ^ B) Z tau)‖ ≤
        A * (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ * Z ^ (-desiredSaving) := by
  let Rmax := 3 * lengthCap + 4
  let saving := desiredSaving + 6 * lengthCap
  have hRmax : 0 ≤ Rmax := by dsimp only [Rmax]; positivity
  have hsaving : 0 ≤ saving := by dsimp only [saving]; positivity
  obtain ⟨s, A, hA, hb⟩ := exists_inverse_tail_bound_uniform
    K S D Γ hΓ μv ν slotCap h hlc hcs Rmax tauMin saving hRmax htauMin hsaving
  have hA' : 0 ≤ A * fieldConstant K * 4 ^ 6 :=
    mul_nonneg (mul_nonneg hA (fieldConstant_nonneg K)) (by norm_num)
  refine ⟨s, A * fieldConstant K * 4 ^ 6, hA', ?_⟩
  intro σ Θ ψ C γ j d P φ Z M B tau hZ hMlo hMhi hB hBc htau hslots ha hn hP
  dsimp only
  have hz : 0 < Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  let r : {r : ℝ // 0 < r} := ⟨Z ^ (-M), Real.rpow_pos_of_pos hz _⟩
  have hX : 1 ≤ Z ^ B := Real.one_le_rpow hz1 hB
  have h16 : (16 : ℝ) ≤ Z ^ (4 : ℝ) := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ Z ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hZ 4
      _ = Z ^ (4 : ℝ) := (Real.rpow_natCast Z 4).symm
  have hbudget : 16 * r.val * (Z ^ B) ^ 2 ≤ Z ^ Rmax := by
    calc
      _ ≤ Z ^ (4 : ℝ) * Z ^ lengthCap * (Z ^ lengthCap) ^ 2 := by
        have hr : r.val ≤ Z ^ lengthCap :=
          Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
        have hBpow : Z ^ B ≤ Z ^ lengthCap :=
          Real.rpow_le_rpow_of_exponent_le hz1 hBc
        exact mul_le_mul
          (mul_le_mul h16 hr r.property.le (Real.rpow_nonneg hz.le _))
          (pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) hBpow 2)
          (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
        repeat rw [← Real.rpow_add hz]
        congr 1
        dsimp only [Rmax]
        norm_num
        ring
  have hraw := hb C γ j d P φ r (Z ^ B) Z tau saving hz1 htau hsaving le_rfl
    (Real.rpow_pos_of_pos hz _) hslots ha hn hP hbudget
  have hpref : fieldConstant K / r.val = fieldConstant K * Z ^ M := by
    dsimp only [r]
    rw [div_eq_mul_inv, Real.rpow_neg hz.le, inv_inv]
  have hmax : max 1 (4 * Z ^ B) = 4 * Z ^ B :=
    max_eq_right (one_le_mul_of_one_le_of_one_le (by norm_num) hX)
  rw [hpref, hmax, mul_pow] at hraw
  have hpower : Z ^ (-B) * Z ^ M * (Z ^ B) ^ 6 * Z ^ (-saving) ≤
      Z ^ (-desiredSaving) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    repeat rw [← Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hz1
    dsimp only [saving]
    norm_num
    linarith
  have hconst : 0 ≤ (A * fieldConstant K * 4 ^ 6) *
      (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    exact mul_nonneg (mul_nonneg hA' (sq_nonneg _)) (apply_nonneg _ _)
  apply (mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hz.le _)).trans
  convert mul_le_mul_of_nonneg_left hpower hconst using 1 <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveTail

end
