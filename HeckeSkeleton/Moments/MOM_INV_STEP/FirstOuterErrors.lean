import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredErrors
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorMass
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstToSecondData

/-!
# Actual second errors summed over the original first outer source

The finite source may be any subset of the genuine first outer and
overlap indices, in particular the live-first-row subset.  The literal
intermediate coefficient is used at every index.  Its principal and
adaptive tail costs are bounded by the proved centered-family theorems,
then summed against the original assigned marks.

Only original norm windows and individual prime-weight contractions are
hypotheses.  No pointwise error or aggregate energy bound is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterErrors

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstCenteredFamily FirstCenteredErrors FirstParentRows
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
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {σ : Type*}

def markSquare (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
    (side : Bool) (i : FirstErrorSource.Index K S D T) (J : Finset σ) : ℝ :=
  ‖divisorMark J T.columns.primeLists T.columns.primeWeights
    (PositiveAssignedSource.oldExtracted (FirstErrorSource.bare K S D Γ T hmask i) side)‖ ^ 2

theorem markSquare_nonneg (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
    (side : Bool) (i : FirstErrorSource.Index K S D T) (J : Finset σ) :
    0 ≤ markSquare K S D Γ T hmask side i J := sq_nonneg _

theorem markSquare_eq (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
    (side : Bool) (i : FirstErrorSource.Index K S D T) (J : Finset σ) :
    markSquare K S D Γ T hmask side i J =
      ‖FirstOverlapColumns.assignedMark K S T.columns
        (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
        i.1.1.val i.1.2.1.val side
        (FirstMobiusGeometry.overlapIdeal K S D T.scale
          (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
          i.1.1.val i.1.2.1.val false i.2) J‖ ^ 2 := rfl

def principalTerm (T : FirstParentEnergy.Data K S (σ := σ))
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
    (i : FirstErrorSource.Index K S D T) (J : Finset σ)
    (U a t : ℝ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) : ℝ :=
  principalCost K S D Γ hΓ μv T.columns Θ ψ G hν hG J
    (FirstToSecondData.triple K S D T i.1 i.2)
    (FirstToSecondData.label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val U a t φ h hlc hcs r

def tailTerm (T : FirstParentEnergy.Data K S (σ := σ))
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
    (i : FirstErrorSource.Index K S D T) (J : Finset σ)
    (P : Finset (Ext × Ext)) (U a t Z tau : ℝ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) : ℝ :=
  tailCost K S D Γ hΓ μv T.columns Θ ψ G hν hG J
    (FirstToSecondData.triple K S D T i.1 i.2)
    (FirstToSecondData.label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val P U a t Z tau φ h hlc hcs r

/-- The whole actual original-mark sum has a principal error bound.
The frequency may depend on every index; it does not occur in A. -/
theorem exists_total_principal_bound
    (slotCap : ℕ) (eps Hmax Umax loss a : ℝ)
    (heps : 0 < eps) (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax) (hloss : 0 < loss)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {σ : Type*}
      (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
      (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
      (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
      (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool)
      (U : FirstErrorSource.Index K S D T → ℝ)
      (frequency : FirstErrorSource.Index K S D T → Finset σ → ℝ)
      (Z H L Xq Xe Xf : ℝ), ∀ hZ : 1 < Z,
      0 ≤ H → H ≤ Hmax →
      (∀ i ∈ I, 0 < U i ∧ U i ≤ Z ^ Umax ∧ U i ≤ Z ^ L) →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p) →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
        ‖T.columns.primeWeights j p‖ ≤ 1) →
      T.columns.slots.card ≤ slotCap → 1 ≤ Xq → 1 ≤ Xe → 1 ≤ Xf →
      (∀ i ∈ I,
        ((FirstErrorSource.bare K S D Γ T hmask i).cubeQ.absNorm : ℝ) ≤ Xq ∧
        ((FirstErrorSource.bare K S D Γ T hmask i).quotient.val.val.absNorm : ℝ) ≤ Xe ∧
        ((FirstErrorSource.bare K S D Γ T hmask i).firstLabel.val.val.absNorm : ℝ) ≤ Xf) →
      (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        markSquare K S D Γ T hmask side i J *
          principalTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (U i) a (frequency i J)
            φ h hlc hcs ⟨Z ^ (-H), Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _⟩) ≤
        A * (Xq * Xe) ^ (1 + eps) * Xq ^ eps * Xf ^ (1 + eps) *
          Z ^ (H + L + loss) := by
  obtain ⟨Ap, hAp, hp⟩ := FirstCenteredErrors.exists_uniform_principal_bound
    K S D Γ hΓ μv slotCap Hmax Umax loss a hHmax hUmax hloss φ h hlc hcs
  obtain ⟨Am, hAm, hm⟩ := FirstErrorMass.exists_all_original_mass_bound
    K S D Γ slotCap eps heps
  refine ⟨Am * Ap, mul_nonneg hAm.le hAp, ?_⟩
  intro σ T hmask Θ ψ G hν hG I side U frequency Z H L Xq Xe Xf hZ
    hH0 hH hU hprime hweights hslots hq he hf hnorm
  have hz : 0 < Z := zero_lt_one.trans hZ
  let B := Ap * Z ^ (H + L + loss)
  have hB : 0 ≤ B := mul_nonneg hAp (Real.rpow_nonneg hz.le _)
  have hp' (i : FirstErrorSource.Index K S D T) (hi : i ∈ I) (J : Finset σ) :
      principalTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (U i) a (frequency i J)
        φ h hlc hcs ⟨Z ^ (-H), Real.rpow_pos_of_pos hz _⟩ ≤ B := by
    apply (hp T.columns Θ ψ G hν hG J
      (FirstToSecondData.triple K S D T i.1 i.2)
      (FirstToSecondData.label K S D T i.1).val.val
      (FirstLocalizedEnergy.divisor K S D T i.1).val
      Z H (U i) (frequency i J) hZ hH0 hH (hU i hi).1 (hU i hi).2.1
      hslots hweights).trans
    calc
      Ap * U i * Z ^ (H + loss) ≤ Ap * Z ^ L * Z ^ (H + loss) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hU i hi).2.2 hAp) (Real.rpow_nonneg hz.le _)
      _ = B := by
        dsimp only [B]
        rw [mul_assoc, ← Real.rpow_add hz]
        congr 2
        ring
  have hmass := hm T hmask I side hprime hweights hslots Xq Xe Xf hq he hf hnorm
  change (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
    markSquare K S D Γ T hmask side i J) ≤ _ at hmass
  calc
    _ ≤ ∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        markSquare K S D Γ T hmask side i J * B := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro J hJ
      exact mul_le_mul_of_nonneg_left (hp' i hi J)
        (markSquare_nonneg K S D Γ T hmask side i J)
    _ = (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        markSquare K S D Γ T hmask side i J) * B := by simp only [Finset.sum_mul]
    _ ≤ (Am * (Xq * Xe) ^ (1 + eps) * Xq ^ eps * Xf ^ (1 + eps)) * B :=
      mul_le_mul_of_nonneg_right hmass hB
    _ = _ := by dsimp only [B]; ring

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
/-- The genuine common/divisor cutoff is preserved at every outer
index. Any actual pair subset is allowed, including the principal pairs
needed for principal restoration. -/
theorem exists_total_tail_bound
    (slotCap : ℕ) (eps Hmax Umax tauMin saving a : ℝ)
    (heps : 0 < eps) (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax)
    (htauMin : 0 < tauMin) (hsaving : 0 ≤ saving)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {σ : Type*}
      (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
      (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
      (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
      (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool)
      (U : FirstErrorSource.Index K S D T → ℝ)
      (frequency : FirstErrorSource.Index K S D T → Finset σ → ℝ)
      (P : FirstErrorSource.Index K S D T → Finset σ → Finset (Ext × Ext))
      (Z H L tau Xq Xe Xf : ℝ), ∀ hZ : 2 ≤ Z,
      0 ≤ H → H ≤ Hmax → tauMin ≤ tau →
      (∀ i ∈ I, 0 < U i ∧ U i ≤ Z ^ Umax ∧ U i ≤ Z ^ L) →
      (∀ i ∈ I, ∀ J ∈ T.columns.slots.powerset,
        P i J ⊆ squarefreePool K Sset (2 * U i) ×ˢ squarefreePool K Sset (2 * U i)) →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p) →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
        ‖T.columns.primeWeights j p‖ ≤ 1) →
      T.columns.slots.card ≤ slotCap → 1 ≤ Xq → 1 ≤ Xe → 1 ≤ Xf →
      (∀ i ∈ I,
        ((FirstErrorSource.bare K S D Γ T hmask i).cubeQ.absNorm : ℝ) ≤ Xq ∧
        ((FirstErrorSource.bare K S D Γ T hmask i).quotient.val.val.absNorm : ℝ) ≤ Xe ∧
        ((FirstErrorSource.bare K S D Γ T hmask i).firstLabel.val.val.absNorm : ℝ) ≤ Xf) →
      (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        markSquare K S D Γ T hmask side i J *
          tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (P i J)
            (U i) a (frequency i J) Z tau φ h hlc hcs
            ⟨Z ^ (-H), Real.rpow_pos_of_pos (by linarith) _⟩) ≤
        A * (Xq * Xe) ^ (1 + eps) * Xq ^ eps * Xf ^ (1 + eps) *
          Z ^ (L - saving) := by
  obtain ⟨At, hAt, ht⟩ := FirstCenteredErrors.exists_uniform_tail_bound
    K S D Γ hΓ μv ν slotCap Hmax Umax tauMin saving a
      hHmax hUmax htauMin hsaving φ h hlc hcs
  obtain ⟨Am, hAm, hm⟩ := FirstErrorMass.exists_all_original_mass_bound
    K S D Γ slotCap eps heps
  refine ⟨Am * At, mul_nonneg hAm.le hAt, ?_⟩
  intro σ T hmask Θ ψ G hν hG I side U frequency P Z H L tau Xq Xe Xf hZ
    hH0 hH htau hU hP hprime hweights hslots hq he hf hnorm
  have hz : 0 < Z := by linarith
  let B := At * Z ^ (L - saving)
  have hB : 0 ≤ B := mul_nonneg hAt (Real.rpow_nonneg hz.le _)
  have ht' (i : FirstErrorSource.Index K S D T) (hi : i ∈ I)
      (J : Finset σ) (hJ : J ∈ T.columns.slots.powerset) :
      tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (P i J)
        (U i) a (frequency i J) Z tau φ h hlc hcs
        ⟨Z ^ (-H), Real.rpow_pos_of_pos hz _⟩ ≤ B := by
    apply (ht T.columns Θ ψ G hν hG J
      (FirstToSecondData.triple K S D T i.1 i.2)
      (FirstToSecondData.label K S D T i.1).val.val
      (FirstLocalizedEnergy.divisor K S D T i.1).val
      (P i J) Z H (U i) (frequency i J) tau hZ hH0 hH
      (hU i hi).1 (hU i hi).2.1 htau hslots hweights (hP i hi J hJ)).trans
    calc
      At * U i * Z ^ (-saving) ≤ At * Z ^ L * Z ^ (-saving) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hU i hi).2.2 hAt) (Real.rpow_nonneg hz.le _)
      _ = B := by
        dsimp only [B]
        rw [mul_assoc, ← Real.rpow_add hz]
        congr 2
        ring
  have hmass := hm T hmask I side hprime hweights hslots Xq Xe Xf hq he hf hnorm
  change (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
    markSquare K S D Γ T hmask side i J) ≤ _ at hmass
  calc
    _ ≤ ∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        markSquare K S D Γ T hmask side i J * B := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro J hJ
      exact mul_le_mul_of_nonneg_left (ht' i hi J hJ)
        (markSquare_nonneg K S D Γ T hmask side i J)
    _ = (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        markSquare K S D Γ T hmask side i J) * B := by simp only [Finset.sum_mul]
    _ ≤ (Am * (Xq * Xe) ^ (1 + eps) * Xq ^ eps * Xf ^ (1 + eps)) * B :=
      mul_le_mul_of_nonneg_right hmass hB
    _ = _ := by dsimp only [B]; ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterErrors

end
