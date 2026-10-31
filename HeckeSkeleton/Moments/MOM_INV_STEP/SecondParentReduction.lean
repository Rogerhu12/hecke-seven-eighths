import HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondPrincipal
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondTail

/-!
# Uniform second reduction from the actual intermediate inverse energy

Genuine masked Poisson supplies the retained source and both additive
zeros. The real original coefficient bounds supply the principal cost
and the complete tail. Only arithmetic support windows are premises.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentReduction

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep CanonicalChildren SecondPoissonSplit
open scoped Classical BigOperators nonZeroDivisors

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
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

include ν μ in
theorem exists_uniform_parent_reduction
    (slotCap : ℕ) (lengthCap Rmax tauMin loss saving : ℝ)
    (hL : 0 ≤ lengthCap) (hRmax : 0 ≤ Rmax) (htauMin : 0 < tauMin)
    (hloss : 0 < loss) (hsaving : 0 ≤ saving)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
      (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
      (j : Ideal (𝓞 K)) (d : OS) (φ : SchwartzMap Varch ℂ)
      (Z H U eta R tau : ℝ), ∀ hZ : 1 ≤ Z,
      0 ≤ H → H ≤ lengthCap → 0 ≤ U → U ≤ lengthCap →
      0 ≤ eta → eta ≤ lengthCap → 4 ≤ Z ^ eta →
      0 ≤ R → R ≤ Rmax → tauMin ≤ tau →
      C.originalSlots.card ≤ slotCap →
      (∀ i ∈ C.originalSlots, ∀ P ∈ C.primeLists i, ‖C.primeWeights i P‖ ≤ 1) →
      (∀ n ∈ C.columns γ, (n.val.val.absNorm : ℝ) ≤ 4 * Z ^ U) →
      -H + 2 * U + 2 * eta ≤ R →
      Z ^ (-U) * ‖DivisorInverseColumn.weightedEnergy K S Γ D C γ j d φ h ∅
        ⟨Z ^ (-H), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩‖ ≤
      Z ^ (-U) * ‖retainedSource K S D Γ hΓ μv
        (DivisorInverseColumn.coefficient K S D C γ j d)
        (C.columns γ ×ˢ C.columns γ) φ h hlc hcs
        ⟨Z ^ (-H), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩ (Z ^ (R + tau))‖ +
      A * (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 *
        s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ *
        (Z ^ (H + loss) + Z ^ (-saving)) := by
  obtain ⟨s₁, Ap, hAp, hp⟩ := UniformSecondPrincipal.exists_uniform_principal_bound
    K S D Γ hΓ μv slotCap lengthCap lengthCap loss hL hL hloss h hlc hcs
  obtain ⟨s₂, At, hAt, ht⟩ := UniformSecondTail.exists_normalized_inverse_tail_bound_uniform
    K S D Γ hΓ μv ν slotCap h hlc hcs lengthCap Rmax tauMin saving hL hRmax htauMin hsaving
  let s := s₁ ∪ s₂
  refine ⟨s, Ap + At, add_nonneg hAp hAt, ?_⟩
  intro σ Θ ψ C γ j d φ Z H U eta R tau hZ hH0 hH hU0 hU heta hetaL hfour
    hR hRR htau hcap ha hN hradius
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  let rad : {r : ℝ // 0 < r} := ⟨Z ^ (-H), Real.rpow_pos_of_pos hZpos _⟩
  let a := DivisorInverseColumn.coefficient K S D C γ j d
  let W := SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)
  let p := s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ
  have hW : 0 ≤ W := apply_nonneg _ _
  have hp0 : 0 ≤ p := apply_nonneg _ _
  have hsup₁ : s₁.sup (schwartzSeminormFamily ℝ Varch ℂ) φ ≤ p := by
    apply Seminorm.finset_sup_apply_le hp0
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
  have hsup₂ : s₂.sup (schwartzSeminormFamily ℝ Varch ℂ) φ ≤ p := by
    apply Seminorm.finset_sup_apply_le hp0
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_right _ hi)
  have hNa : ∀ n ∈ C.columns γ, (n.val.val.absNorm : ℝ) ≤ Z ^ (U + eta) := by
    intro n hn
    apply (hN n hn).trans
    rw [Real.rpow_add hZpos]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hZpos.le U)
  have hprincipal := hp C γ j d Z H U φ hZ hH0 hH hU0 hU hcap ha hN
  have hzero : ‖additiveZeros K S D Γ hΓ μv a (C.columns γ) φ h hlc hcs rad‖ ≤
      Ap * W ^ 2 * p * Z ^ (H + U + loss) := by
    have hp' := hprincipal.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsup₁ (by positivity)) (Real.rpow_nonneg hZpos.le _))
    have hn := norm_nonneg (physicalPrincipal K S D Γ hΓ a (C.columns γ) φ h hlc hcs rad)
    change 2 * ‖physicalPrincipal K S D Γ hΓ a (C.columns γ) φ h hlc hcs rad‖ +
      ‖additiveZeros K S D Γ hΓ μv a (C.columns γ) φ h hlc hcs rad‖ ≤ _ at hp'
    linarith
  have hzero' : Z ^ (-U) *
      ‖additiveZeros K S D Γ hΓ μv a (C.columns γ) φ h hlc hcs rad‖ ≤
        Ap * W ^ 2 * p * Z ^ (H + loss) := by
    apply (mul_le_mul_of_nonneg_left hzero (Real.rpow_nonneg hZpos.le _)).trans_eq
    calc
      _ = Ap * W ^ 2 * p * (Z ^ (-U) * Z ^ (H + U + loss)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hZpos, show -U + (H + U + loss) = H + loss by ring]
  have htail := ht C γ j d (C.columns γ ×ˢ C.columns γ) φ Z H U eta R tau hZ
    hH hU0 hU heta hetaL hR hRR htau hcap ha hNa (Finset.Subset.refl _) hradius
  have htail' : Z ^ (-U) * ‖tailSource K S D Γ hΓ μv a
      (C.columns γ ×ˢ C.columns γ) φ h hlc hcs rad (Z ^ (R + tau))‖ ≤
        At * W ^ 2 * p * Z ^ (-saving) :=
    htail.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsup₂ (by positivity)) (Real.rpow_nonneg hZpos.le _))
  rw [genuine_second_split K S D Γ hΓ μv ν μ C γ j d φ h hlc hcs rad (Z ^ (R + tau))]
  have hn := (norm_add_le
    (retainedSource K S D Γ hΓ μv a (C.columns γ ×ˢ C.columns γ) φ h hlc hcs rad (Z ^ (R + tau)) +
      additiveZeros K S D Γ hΓ μv a (C.columns γ) φ h hlc hcs rad)
    (tailSource K S D Γ hΓ μv a (C.columns γ ×ˢ C.columns γ) φ h hlc hcs rad (Z ^ (R + tau)))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have hn' := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hZpos.le (-U))
  rw [mul_add, mul_add] at hn'
  apply hn'.trans
  apply (add_le_add (add_le_add le_rfl hzero') htail').trans
  rw [add_assoc]
  apply add_le_add le_rfl
  have h₁ : 0 ≤ Ap * W ^ 2 * p * Z ^ (-saving) := by positivity
  have h₂ : 0 ≤ At * W ^ 2 * p * Z ^ (H + loss) := by positivity
  nlinarith

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentReduction

end

