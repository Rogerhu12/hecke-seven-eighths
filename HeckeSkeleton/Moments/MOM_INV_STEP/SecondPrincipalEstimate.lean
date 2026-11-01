import HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonSplit
import HeckeSkeleton.Moments.MOM_INV_STEP.InverseCoefficientBounds
import HeckeSkeleton.Moments.MOM_INV_STEP.MaskCounting
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalBudget

/-!
# Principal bounds for the actual intermediate inverse family

The physical principal source and both additive zeros use the literal
retained-divisor coefficient. Their pointwise coefficient bounds and
their diagonal cardinality are proved from the original family.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondPrincipalEstimate

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalPoissonSplit
  PrincipalZero PrimitivePoissonSource ConductorMasks FirstInversePoisson
  PrincipalOrbitalMass InverseCoefficientBounds
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "e" => unitIdeal K S

theorem exists_physicalPrincipal_bound (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)}
      {ψ : HeckeCharacter K} (C : ColumnFamily K Sset σ Θ ψ)
      (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS) (X : ℝ)
      (φ : SchwartzMap V ℂ)
      (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
      (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}),
      1 ≤ X → C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ P ∈ C.primeLists i, ‖C.primeWeights i P‖ ≤ 1) →
      (∀ n ∈ C.columns γ, (n.val.val.absNorm : ℝ) ≤ X) →
      ‖SecondPoissonSplit.physicalPrincipal K S D Γ hΓ
        (DivisorInverseColumn.coefficient K S D C γ j d) (C.columns γ) φ h hlc hcs r‖ ≤
      A * (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
        absoluteRowMass K Sset Γ φ (sIntegerFiniteTestFunction K S h) r *
        X ^ (1 + 2 * ε) := by
  obtain ⟨Ac, hAc, hcoef⟩ := exists_coefficient_bound K S D slotCap ε hε
  obtain ⟨An, hAn, hcount⟩ := exists_ideal_count_bound K
  refine ⟨An * Ac ^ 2, one_le_mul_of_one_le_of_one_le hAn (one_le_pow₀ hAc), ?_⟩
  intro σ Θ ψ C γ j d X φ h hlc hcs r hX hcap ha hN
  let W := SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)
  let z := absoluteRowMass K Sset Γ φ (sIntegerFiniteTestFunction K S h) r
  have hW : 0 ≤ W := apply_nonneg _ _
  have hz : 0 ≤ z := tsum_nonneg (fun _ => norm_nonneg _)
  have hb := SecondPoissonSplit.physicalPrincipal_norm_le K S D Γ hΓ
    (DivisorInverseColumn.coefficient K S D C γ j d) (C.columns γ)
    (C.columns_squarefree γ) (Ac * W * X ^ ε) (by positivity)
    (fun n hn => hcoef C γ j d n X hcap ha (hN n hn)) φ h hlc hcs r
  have hcard : ((C.columns γ).card : ℝ) ≤ An * X := by
    have hc : ((C.columns γ).card : ℝ) ≤ ((boundedNormIdeals K X).card : ℝ) := by
      exact_mod_cast PrincipalBudget.exterior_card_le_norm_count K S (C.columns γ) X hN
    exact hc.trans (hcount X hX)
  have hpow : X * (X ^ ε) ^ 2 = X ^ (1 + 2 * ε) := by
    rw [show 1 + 2 * ε = 1 + (ε + ε) by ring,
      Real.rpow_add (lt_of_lt_of_le zero_lt_one hX),
      Real.rpow_add (lt_of_lt_of_le zero_lt_one hX), Real.rpow_one, pow_two]
  apply hb.trans
  calc
    _ ≤ (An * X) * (Ac * W * X ^ ε) ^ 2 * z := by gcongr
    _ = (An * Ac ^ 2) * W ^ 2 * z * (X * (X ^ ε) ^ 2) := by ring
    _ = _ := by rw [hpow]

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

theorem exists_additiveZeros_bound (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)}
      {ψ : HeckeCharacter K} (C : ColumnFamily K Sset σ Θ ψ)
      (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS) (X : ℝ)
      (φ : SchwartzMap V ℂ)
      (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
      (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}),
      1 ≤ X → C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ P ∈ C.primeLists i, ‖C.primeWeights i P‖ ≤ 1) →
      (∀ n ∈ C.columns γ, (n.val.val.absNorm : ℝ) ≤ X) →
      ‖SecondPoissonSplit.additiveZeros K S D Γ hΓ μv
        (DivisorInverseColumn.coefficient K S D C γ j d) (C.columns γ) φ h hlc hcs r‖ ≤
      A * (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
        zeroEnvelope K S Γ μv φ h r * X ^ (1 + 4 * ε) := by
  obtain ⟨Ac, hAc, hcoef⟩ := exists_coefficient_bound K S D slotCap ε hε
  obtain ⟨Am, hAm, hmask⟩ := MaskCounting.exists_actual_pair_mask_bound K S D ε hε
  obtain ⟨An, hAn, hcount⟩ := exists_ideal_count_bound K
  refine ⟨An * Ac ^ 2 * Am, one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hAn (one_le_pow₀ hAc)) hAm, ?_⟩
  intro σ Θ ψ C γ j d X φ h hlc hcs r hX hcap ha hN
  let a := DivisorInverseColumn.coefficient K S D C γ j d
  let W := SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)
  let z := zeroEnvelope K S Γ μv φ h r
  let U := (Ac * W * X ^ ε) ^ 2 * (Am * (X * X) ^ ε) * z
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hW : 0 ≤ W := apply_nonneg _ _
  have hz : 0 ≤ z := zeroEnvelope_nonneg K S Γ μv φ h r
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hpoint (p : Ext × Ext) (hp : p ∈ SecondPoissonSplit.principalPairs K S D (C.columns γ)) :
      ‖SecondPoissonSplit.sourceWeight K S a p *
        pairPrincipal K S D Γ hΓ μv (e, p.1) (e, p.2) φ h hlc hcs ∅ r‖ ≤ U := by
    obtain ⟨hmem, hzero⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hmem
    have h₁ := hcoef C γ j d p.1 X hcap ha (hN p.1 hp₁)
    have h₂ := hcoef C γ j d p.2 X hcap ha (hN p.2 hp₂)
    have hw : ‖SecondPoissonSplit.sourceWeight K S a p‖ ≤ (Ac * W * X ^ ε) ^ 2 := by
      rw [SecondPoissonSplit.sourceWeight, norm_mul, norm_star, pow_two]
      exact mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
    have hm := hmask ∅ (fun v hv => by simp only [Finset.notMem_empty] at hv)
      1 one_ne_zero (fun v hv => by simp only [Finset.notMem_empty] at hv) p.1 p.2 e e
    have hprod : (((unitIdeal K S).val.val * (unitIdeal K S).val.val *
        p.1.val.val * p.2.val.val).absNorm : ℝ) ≤ X * X := by
      simp only [FirstInversePoisson.unitIdeal_val, one_mul, map_mul, Nat.cast_mul]
      exact mul_le_mul (hN p.1 hp₁) (hN p.2 hp₂) (Nat.cast_nonneg _) hX0
    simp only [LocalizedMasks.localizeSupportedMask, Finset.attach_empty, Finset.image_empty,
      Finset.empty_union, map_one, Nat.cast_one, one_mul] at hm
    have hm' := hm.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hprod hε.le) (le_trans zero_le_one hAm))
    have hpz := principalContribution_norm_le K S D Γ hΓ μv
      (pairSupport K S D p.1 p.2 e e) (pairExponent K S p.1 p.2 e e)
      φ h hlc hcs ∅ r
    rw [if_pos hzero, Finset.empty_union] at hpz
    have hzero' := hpz.trans (mul_le_mul_of_nonneg_right hm' hz)
    dsimp only [U]
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hw hzero' (norm_nonneg _) (sq_nonneg _)
  have hcard : ((SecondPoissonSplit.principalPairs K S D (C.columns γ)).card : ℝ) ≤ An * X := by
    have hc₁ : ((SecondPoissonSplit.principalPairs K S D (C.columns γ)).card : ℝ) ≤
        ((C.columns γ).card : ℝ) := by
      exact_mod_cast SecondPoissonSplit.principalPairs_card_le K S D (C.columns γ)
        (C.columns_squarefree γ)
    have hc₂ : ((C.columns γ).card : ℝ) ≤ ((boundedNormIdeals K X).card : ℝ) := by
      exact_mod_cast PrincipalBudget.exterior_card_le_norm_count K S (C.columns γ) X hN
    exact hc₁.trans (hc₂.trans (hcount X hX))
  have hpow : X * (X ^ ε) ^ 2 * (X * X) ^ ε = X ^ (1 + 4 * ε) := by
    rw [Real.mul_rpow hX0 hX0,
      show 1 + 4 * ε = 1 + ε + ε + ε + ε by ring]
    repeat rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hX)]
    rw [Real.rpow_one]
    ring
  rw [SecondPoissonSplit.additiveZeros_eq_principalPairs]
  calc
    _ ≤ ∑ p ∈ SecondPoissonSplit.principalPairs K S D (C.columns γ),
        ‖SecondPoissonSplit.sourceWeight K S a p *
          pairPrincipal K S D Γ hΓ μv (e, p.1) (e, p.2) φ h hlc hcs ∅ r‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ SecondPoissonSplit.principalPairs K S D (C.columns γ), U :=
      Finset.sum_le_sum hpoint
    _ = ((SecondPoissonSplit.principalPairs K S D (C.columns γ)).card : ℝ) * U := by simp
    _ ≤ (An * X) * U := mul_le_mul_of_nonneg_right hcard hU
    _ = (An * Ac ^ 2 * Am) * W ^ 2 * z * (X * (X ^ ε) ^ 2 * (X * X) ^ ε) := by
      dsimp only [U]
      ring
    _ = _ := by rw [hpow]

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondPrincipalEstimate

end
