import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedNormalization
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLiveCappedFreeEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorIntegration

/-!
# Actual physical normalization with the live first source retained

Every original live arithmetic and spectral index is retained, with the
physical row cap fixed before the free inverse energy is formed. The literal
Poisson prefactor and the overlap/center Mellin normalization are
replaced by their proved kappa bound, while the actual inverse energy,
the two Mobius weights and the assigned original marks remain visible.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLiveNormalization

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstColumnAssembly
  FirstParentRows FirstOuterCenters FirstMobiusGeometry FirstPositiveSource
  FirstCenteredPositiveEnergy FirstCommonEnvelope FirstFreeMellinEnergy
  FirstBranchIntegration FirstLocalizedFreeEnergy FirstCappedFreeEnergy FirstPoissonNormalization
  FirstActualPrefactor InverseRowMajorant CommonKernel FirstCappedNormalization
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ ι : Type*} [Fintype ι]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r})
  (L : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℕ) (side : Bool)
variable (Rcap : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps ε : ℝ)

def budgetTotal (Z M r ell V eta : ℝ) (delta A B R : OuterIndex K S D T → ℝ) : ℝ :=
  ∑ o : OuterIndex K S D T, if FirstLiveCappedFreeEnergy.alive K S D Γ T H L o then
    Z ^ (firstKappa M r ell V (delta o) (A o) (B o) (R o) + 9 * eta / 2) *
      ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then
          ∑ J ∈ T.columns.slots.powerset,
            remainder K S D Γ T Θ ψ G hν hG grid W hW m side Rcap massEps ε o e k J
        else 0
    else 0

/-- The normalized production sum is exactly a sum over live original
(o,e), with one assigned center and every original mark subset. -/
theorem budgetTotal_eq_liveIndices (Z M r ell V eta : ℝ)
    (delta A B R : OuterIndex K S D T → ℝ) :
    budgetTotal K S D Γ T Θ ψ G hν hG H L grid centers W hW m side Rcap massEps ε
      Z M r ell V eta delta A B R =
      ∑ i ∈ FirstLiveCappedFreeEnergy.liveIndices K S D Γ T H L,
        Z ^ (firstKappa M r ell V (delta i.1) (A i.1) (B i.1) (R i.1) + 9 * eta / 2) *
          ∑ J ∈ T.columns.slots.powerset,
            remainder K S D Γ T Θ ψ G hν hG grid W hW m side Rcap massEps ε
              i.1 i.2 (centers.assignment side i.1 i.2) J := by
  have hc := FirstErrorIntegration.live_center_assignment_collapse
    K S D T grid centers side Γ H L
    (fun o e k =>
      Z ^ (firstKappa M r ell V (delta o) (A o) (B o) (R o) + 9 * eta / 2) *
        ∑ J ∈ T.columns.slots.powerset,
          remainder K S D Γ T Θ ψ G hν hG grid W hW m side Rcap massEps ε o e k J)
  calc
    _ = (∑ o : OuterIndex K S D T,
        if FirstLiveCappedFreeEnergy.alive K S D Γ T H L o then
          ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
            if centers.assignment side o e = k then
              Z ^ (firstKappa M r ell V (delta o) (A o) (B o) (R o) + 9 * eta / 2) *
                ∑ J ∈ T.columns.slots.powerset,
                  remainder K S D Γ T Θ ψ G hν hG grid W hW m side Rcap massEps ε o e k J
            else 0
        else 0) := by
      simp only [budgetTotal, Finset.mul_sum, mul_ite, mul_zero]
    _ = _ := hc

theorem budgetTotal_nonneg (Z M r ell V eta : ℝ) (hZ : 0 ≤ Z)
    (delta A B R : OuterIndex K S D T → ℝ) :
    0 ≤ budgetTotal K S D Γ T Θ ψ G hν hG H L grid centers W hW m side Rcap massEps ε
      Z M r ell V eta delta A B R := by
  apply Finset.sum_nonneg
  intro o ho
  by_cases hlive : FirstLiveCappedFreeEnergy.alive K S D Γ T H L o
  · simp only [if_pos hlive]
    apply mul_nonneg (Real.rpow_nonneg hZ _)
    apply Finset.sum_nonneg
    intro k hk
    apply Finset.sum_nonneg
    intro e he
    split_ifs
    · apply Finset.sum_nonneg
      intro J hJ
      exact remainder_nonneg K S D Γ T Θ ψ G hν hG grid W hW m side Rcap massEps ε o e k J
    · exact le_rfl
  · simp only [if_neg hlive, le_refl]


/-- Geometric norm windows produce the complete physical prefactor
bound. These are windows for the actual mask divisor, active cube
conductor and extracted ideal, with no source or energy premise. -/
theorem normalized_freeTotal_le (Z M r ell V eta : ℝ)
    (hZ : 1 ≤ Z) (heta : 0 ≤ eta)
    (delta A B R : OuterIndex K S D T → ℝ)
    (hradius : T.radius.val = Z ^ (-M)) (hX : T.scale.val = Z ^ r)
    (hd : ∀ o, Z ^ (delta o - eta) ≤
      (sIntegerElementNorm K Sset (FirstLocalizedEnergy.divisor K S D T o)).val)
    (hR : ∀ o, Z ^ (R o - eta) ≤
      cubeNorm K S D (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val)
    (hA : ∀ o, ((FirstSourceColumns.extractedFactor K S
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side).val.val.absNorm : ℝ) ≤
      Z ^ (A o + B o + 2 * eta)) :
    Z ^ (-r - 2 * ell - V) *
      FirstLiveCappedFreeEnergy.freeTotal K S D Γ T Θ ψ G hν hG H L grid centers W hW m side Rcap massEps ε ≤
    ActualPoissonScale.fieldConstant K *
      budgetTotal K S D Γ T Θ ψ G hν hG H L grid centers W hW m side Rcap massEps ε
        Z M r ell V eta delta A B R := by
  unfold FirstLiveCappedFreeEnergy.freeTotal budgetTotal
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o ho
  by_cases hlive : FirstLiveCappedFreeEnergy.alive K S D Γ T H L o
  · simp only [if_pos hlive]
    simp only [mul_assoc, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum
    intro e he
    by_cases ha : centers.assignment side o e = k
    · simp only [ha, if_true, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro J hJ
      have hv : (grid k).val ≤
          extractedHeight K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
            o.1.val o.2.1.val side
            (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
              o.1.val o.2.1.val false e) := by
        simpa only [ha, FirstOuterCenters.extractedNorm] using centers.lower side o e
      have hp := normalizedScalar_le K S D Z M r ell V (delta o) (A o) (B o) (R o) eta
        hZ heta T.radius T.scale (grid k) (FirstLocalizedEnergy.divisor K S D T o)
        (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
        (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val false e) side hradius hX hv (hd o) (hR o) (hA o)
      have hb := mul_le_mul_of_nonneg_right hp
        (remainder_nonneg K S D Γ T Θ ψ G hν hG grid W hW m side Rcap massEps ε o e k J)
      calc
        _ = normalizedScalar K S D Z r ell V T.radius T.scale (grid k)
            (FirstLocalizedEnergy.divisor K S D T o)
            (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
            (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
              o.1.val o.2.1.val false e) *
            remainder K S D Γ T Θ ψ G hν hG grid W hW m side Rcap massEps ε o e k J := by
          simpa only [mul_assoc, FirstLiveCappedFreeEnergy.freeRowIntegral_eq_capped]
            using normalized_summand_eq K S D Γ T Θ ψ G hν hG
            grid centers W hW m side Rcap massEps ε Z r ell V o e k J
        _ ≤ _ := hb.trans_eq (by ring)
    · simp only [ha, if_false, mul_zero, le_refl]
  · simp only [if_neg hlive, mul_zero, le_refl]

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLiveNormalization

end
