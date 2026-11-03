import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorPhysicalBudget

/-!
# The actual first-outer adaptive tail after physical normalization

The literal infinite second tail is summed over the actual first outer
source and integrated against the original Mellin and Fourier measures.
The positive first row cap permits the sharp first-outer mass to be
absorbed with an arbitrary prescribed power saving. No finite or
infinite tail bound is supplied as an input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorTailBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstErrorSource FirstErrorIntegration FirstErrorBudget
  FirstCenteredErrorIntegrals FirstOuterErrors FirstErrorPhysicalBudget
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K
local notation "Ext" => ExteriorIdeal K Sset

variable {σ : Type*}
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool)
variable (U : FirstErrorSource.Index K S D T → ℝ)
variable (P : FirstErrorSource.Index K S D T → Finset σ →
  Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) ×
    ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℕ) (coordinate : CommonKernel.LogPlane → ℝ)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))

def tailTotal (Z kappa H a tau : ℝ) (hZ : 0 < Z) : ℝ :=
  (Z ^ kappa * ((T.columns.slots.powerset.card : ℝ) *
    (InverseRowMajorant.rowCovolume K S)⁻¹) * mellinMass W hW) *
    ∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
      mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 *
        spectralAverage (MellinSeparation.density W hW) m coordinate
          (fun t => tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (P i J) (U i) a t Z tau
            φ h hlc hcs ⟨Z ^ (-H), Real.rpow_pos_of_pos hZ _⟩)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

/- Constants and the original W seminorm precede Z and all original
source data. The cutoff and the infinite tail remain the actual ones. -/
include ν in
theorem exists_tailTotal_bound
    (slotCap : ℕ) (lengthCap Hmax Umax tauMin loss saving a : ℝ)
    (hcap : 0 ≤ lengthCap) (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax)
    (htauMin : 0 < tauMin) (hloss : 0 < loss) (hsaving : 0 ≤ saving)
    (φ : SchwartzMap Varch ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ {σ : Type*}
      (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
      (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
      (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
      (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool)
      (U : FirstErrorSource.Index K S D T → ℝ)
      (P : FirstErrorSource.Index K S D T → Finset σ → Finset (Ext × Ext))
      (Z M r ell V delta A B R j t eta tau : ℝ), ∀ hZ : 2 ≤ Z,
      ell ≤ lengthCap → R ≤ lengthCap → B ≤ lengthCap →
      t ≤ lengthCap → eta ≤ lengthCap → 0 ≤ j → tauMin ≤ tau →
      0 ≤ firstPhysicalHeight M r ell V delta B j + 12 * eta + tau →
      firstPhysicalHeight M r ell V delta B j + 12 * eta + tau ≤ Hmax →
      (∀ i ∈ I, 0 < U i ∧ U i ≤ Z ^ Umax ∧
        U i ≤ Z ^ (r - A - B - t + 4 * eta)) →
      (∀ i ∈ I, ∀ J ∈ T.columns.slots.powerset,
        P i J ⊆ squarefreePool K Sset (2 * U i) ×ˢ squarefreePool K Sset (2 * U i)) →
      (∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p) →
      (∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k,
        ‖T.columns.primeWeights k p‖ ≤ 1) →
      T.columns.slots.card ≤ slotCap →
      (∀ i ∈ I,
        ((bare K S D Γ T hmask i).b₁.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta) ∧
        ((bare K S D Γ T hmask i).b₂.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta) ∧
        ((cubeConductor K S D Γ T hmask i).absNorm : ℝ) ≤ Z ^ (R + eta) ∧
        Z ^ (j - eta) ≤ ((bare K S D Γ T hmask i).cubeJ.absNorm : ℝ) ∧
        ((bare K S D Γ T hmask i).cubeJ.absNorm : ℝ) ≤ Z ^ (j + eta) ∧
        ((bare K S D Γ T hmask i).firstCommon.absNorm : ℝ) ≤ Z ^ (B + eta) ∧
        ((bare K S D Γ T hmask i).quotient.val.val.absNorm : ℝ) ≤ Z ^ (t + eta)) →
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (m : ℕ) (coordinate : CommonKernel.LogPlane → ℝ), Continuous coordinate →
      tailTotal K S D Γ hΓ μv T Θ ψ G hν hG I side U P W hW m coordinate
        φ h hlc hcs Z (firstKappa M r ell V delta A B R + 9 * eta / 2)
        (firstPhysicalHeight M r ell V delta B j + 12 * eta + tau) a tau
        (by linarith) ≤
      C * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        Z ^ (r + 3 * ell + V - B - j + 26 * eta + tau + loss - saving) := by
  obtain ⟨Am,hAm,hm⟩ := FirstErrorBudget.exists_uniform_annular_mass_bound
    K S D Γ slotCap lengthCap loss hcap hloss
  obtain ⟨Ap,hAp,hp⟩ := FirstCenteredErrorIntegrals.exists_tail_integral_bound
    K S D Γ hΓ μv ν slotCap Hmax Umax tauMin saving a
      hHmax hUmax htauMin hsaving φ h hlc hcs
  obtain ⟨s,As,hAs,hs⟩ := FirstErrorIntegration.exists_spectralMass_bound K S slotCap
  refine ⟨s, Am * Ap * As, mul_nonneg (mul_nonneg hAm.le hAp) hAs, ?_⟩
  intro σ T hmask Θ ψ G hν hG I side U P Z M r ell V delta A B R j t eta tau hZ
    hell hR hB ht heta hj htau hH0 hH hU hP hprime hweights hslots hsource W hW m coordinate hc
  have hz : 0 < Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  let H := firstPhysicalHeight M r ell V delta B j + 12 * eta + tau
  have hHnonneg : 0 ≤ H := hH0
  let L := r - A - B - t + 4 * eta
  let kappa := firstKappa M r ell V delta A B R + 9 * eta / 2
  let count := ell + B + R / 2 + t + 11 * eta / 2 + loss
  let Q : ℝ := Ap * Z ^ (H + L - saving) * fourierMass m * mellinMass W hW
  have hfm : 0 ≤ fourierMass m := fourierMass_nonneg m
  have hwm : 0 ≤ mellinMass W hW := mellinMass_nonneg W hW
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hAp (Real.rpow_nonneg hz.le _)) (fourierMass_nonneg m))
      (mellinMass_nonneg W hW)
  let av (i : FirstErrorSource.Index K S D T) (J : Finset σ) : ℝ :=
    spectralAverage (MellinSeparation.density W hW) m coordinate
      (fun q => tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (P i J) (U i) a q Z tau
        φ h hlc hcs ⟨Z ^ (-H), Real.rpow_pos_of_pos hz _⟩)
  have hav0 (i : FirstErrorSource.Index K S D T) (J : Finset σ) : 0 ≤ av i J := by
    apply integral_nonneg
    intro ξ
    apply mul_nonneg (FirstCommonEnvelope.frequencyEnvelope_nonneg m ξ)
    apply integral_nonneg
    intro q
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hav (i : FirstErrorSource.Index K S D T) (hi : i ∈ I) (J : Finset σ) (hJ : J ∈ T.columns.slots.powerset) :
      av i J ≤ Q := by
    have hp' := hp T.columns Θ ψ G hν hG J
      (FirstToSecondData.triple K S D T i.1 i.2)
      (FirstToSecondData.label K S D T i.1).val.val
      (FirstLocalizedEnergy.divisor K S D T i.1).val
      (P i J) Z H (U i) tau hZ hH0 hH (hU i hi).1 (hU i hi).2.1 htau hslots hweights (hP i hi J hJ)
      W hW m coordinate hc
    change av i J ≤ _ at hp'
    apply hp'.trans
    calc
      Ap * U i * Z ^ (-saving) * fourierMass m * mellinMass W hW ≤
          Ap * Z ^ L * Z ^ (-saving) * fourierMass m * mellinMass W hW := by
        gcongr
        exact (hU i hi).2.2
      _ = Ap * Z ^ (L - saving) * fourierMass m * mellinMass W hW := by
        have hprod : Z ^ L * Z ^ (-saving) = Z ^ (L - saving) := by
          simpa only [sub_eq_add_neg] using (Real.rpow_add hz L (-saving)).symm
        rw [mul_assoc Ap (Z ^ L) (Z ^ (-saving)), hprod]
      _ ≤ Q := by
        dsimp only [Q]
        apply mul_le_mul_of_nonneg_right _ hwm
        apply mul_le_mul_of_nonneg_right _ hfm
        apply mul_le_mul_of_nonneg_left _ hAp
        apply Real.rpow_le_rpow_of_exponent_le hz1
        linarith

  have hm' : (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
      ‖mark K S D T side i J‖ ^ 2) ≤ Am * Z ^ count := by
    exact hm T hmask I side Z ell R B j t eta hz1 hell hR hB ht heta hj
      hprime hweights hslots hsource
  have hsum : (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
      mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 * av i J) ≤
        Am * Z ^ count * Q := by
    calc
      _ ≤ ∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset, ‖mark K S D T side i J‖ ^ 2 * Q := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro J hJ
        have he := mul_le_mul (mobiusWeight_le_one K S D T i) (hav i hi J hJ)
          (hav0 i J) (by norm_num : (0 : ℝ) ≤ 1)
        calc
          _ = ‖mark K S D T side i J‖ ^ 2 * (mobiusWeight K S D T i * av i J) := by ring
          _ ≤ ‖mark K S D T side i J‖ ^ 2 * Q := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_left he (sq_nonneg _)
      _ = (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
          ‖mark K S D T side i J‖ ^ 2) * Q := by simp only [Finset.sum_mul]
      _ ≤ Am * Z ^ count * Q := mul_le_mul_of_nonneg_right hm' hQ
  let out : ℝ := Z ^ kappa *
    ((T.columns.slots.powerset.card : ℝ) * (InverseRowMajorant.rowCovolume K S)⁻¹) *
      mellinMass W hW
  have hout : 0 ≤ out := by
    dsimp only [out]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hz.le _)
        (mul_nonneg (Nat.cast_nonneg _)
          (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)))
      (mellinMass_nonneg W hW)
  have hpowers : Z ^ kappa * Z ^ count * Z ^ (H + L - saving) =
      Z ^ (r + 3 * ell + V - B - j + 26 * eta + tau + loss - saving) := by
    rw [← Real.rpow_add hz, ← Real.rpow_add hz]
    congr 1
    dsimp only [kappa,count,H,L]
    have he := physical_exponent M r ell V delta A B R j t eta tau loss (-saving)
    linarith
  calc
    _ = out * (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 * av i J) := rfl
    _ ≤ out * (Am * Z ^ count * Q) := mul_le_mul_of_nonneg_left hsum hout
    _ = (Am * Ap * spectralMass K S T W hW m) *
        Z ^ (r + 3 * ell + V - B - j + 26 * eta + tau + loss - saving) := by
      dsimp only [out,Q,spectralMass]
      calc
        _ = (Am * Ap *
            (((T.columns.slots.powerset.card : ℝ) * (InverseRowMajorant.rowCovolume K S)⁻¹) *
              fourierMass m * mellinMass W hW ^ 2)) *
              (Z ^ kappa * Z ^ count * Z ^ (H + L - saving)) := by ring
        _ = _ := by rw [hpowers]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (hs T hslots W hW m) (mul_nonneg hAm.le hAp)
      have hh' := mul_le_mul_of_nonneg_right hh
        (Real.rpow_nonneg hz.le (r + 3 * ell + V - B - j + 26 * eta + tau + loss - saving))
      simpa only [mul_assoc] using hh'

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorTailBudget

end

