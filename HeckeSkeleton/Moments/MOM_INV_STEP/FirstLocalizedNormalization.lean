import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedProduction
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualPrefactor

/-!
# Actual first physical normalization inside the complete free energy

Every original arithmetic and spectral index is retained. The literal
Poisson prefactor and the overlap/center Mellin normalization are
replaced by their proved kappa bound, while the actual inverse energy,
the two Mobius weights and the assigned original marks remain visible.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedNormalization

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstColumnAssembly
  FirstParentRows FirstOuterCenters FirstMobiusGeometry FirstPositiveSource
  FirstCenteredPositiveEnergy FirstCommonEnvelope FirstFreeMellinEnergy
  FirstBranchIntegration FirstLocalizedFreeEnergy FirstPoissonNormalization
  FirstActualPrefactor InverseRowMajorant CommonKernel
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
variable (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℕ) (side : Bool) (F : {r : ℝ // 0 < r}) (massEps ε : ℝ)

theorem freeRowIntegral_nonneg (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) (k : ι) (J : Finset σ) :
    0 ≤ freeRowIntegral K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps o e k J := by
  dsimp only [freeRowIntegral]
  apply mul_nonneg
  · exact mul_nonneg (Real.rpow_nonneg (rowCap K S _ F (H o)).property.le massEps)
      (inv_nonneg.mpr (rowCovolume_pos K S).le)
  · apply integral_nonneg
    intro η
    exact mul_nonneg (frequencyEnvelope_nonneg m η)
      (freeMellinEnergy_nonneg K S Γ D T.columns Θ ψ G hν hG J
        (centerScale T.scale (grid k)).val (-(1 / 2 : ℝ)) _ _ _ W hW _ _)

/-- The remaining scalar and actual free inverse energy after the
Poisson/overlap/center prefactor has been accounted for. -/
def remainder (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) (k : ι) (J : Finset σ) : ℝ :=
  ‖(UniqueFactorizationMonoid.moebius (IdealMobiusMask.primeProduct o.2.2.2.val) : ℂ)‖ *
    ‖(UniqueFactorizationMonoid.moebius e.val : ℂ)‖ * (T.columns.slots.powerset.card : ℝ) *
    (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
    ‖assignedMark K S T.columns (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val side
      (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val false e) J‖ ^ 2 *
    FirstLocalizedEnergy.radialScale K S D T o ^ ε *
    freeRowIntegral K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps o e k J

theorem remainder_nonneg (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) (k : ι) (J : Finset σ) :
    0 ≤ remainder K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps ε o e k J := by
  unfold remainder
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Nat.cast_nonneg _))
          (integral_nonneg (fun _ => norm_nonneg _)))
        (sq_nonneg _))
      (Real.rpow_nonneg (FirstLocalizedEnergy.radialScale_pos K S D T o).le ε))
    (freeRowIntegral_nonneg K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps o e k J)

/-- The grouping is an equality of the literal factors. -/
theorem normalized_summand_eq (Z r ell V : ℝ) (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) (k : ι) (J : Finset σ) :
    Z ^ (-r - 2 * ell - V) *
      ((FirstLocalizedEnergy.maskWeight K S D T o *
        FirstLocalizedEnergy.radialScale K S D T o ^ ε) *
        (branchCoefficient K S D T grid centers W hW side o e k J *
          freeRowIntegral K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps o e k J)) =
    normalizedScalar K S D Z r ell V T.radius T.scale (grid k)
      (FirstLocalizedEnergy.divisor K S D T o)
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
      (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val false e) *
      remainder K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps ε o e k J := by
  dsimp only [FirstLocalizedEnergy.maskWeight, branchCoefficient, branchFactor,
    FirstOuterCenters.Centering.at, normalizedScalar, columnScale, remainder]
  ring

def budgetTotal (Z M r ell V eta : ℝ) (delta A B R : OuterIndex K S D T → ℝ) : ℝ :=
  ∑ o : OuterIndex K S D T,
    Z ^ (firstKappa M r ell V (delta o) (A o) (B o) (R o) + 9 * eta / 2) *
      ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then
          ∑ J ∈ T.columns.slots.powerset,
            remainder K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps ε o e k J
        else 0

theorem budgetTotal_nonneg (Z M r ell V eta : ℝ) (hZ : 0 ≤ Z)
    (delta A B R : OuterIndex K S D T → ℝ) :
    0 ≤ budgetTotal K S D Γ T Θ ψ G hν hG H grid centers W hW m side F massEps ε
      Z M r ell V eta delta A B R := by
  apply Finset.sum_nonneg
  intro o ho
  apply mul_nonneg (Real.rpow_nonneg hZ _)
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro e he
  split_ifs
  · apply Finset.sum_nonneg
    intro J hJ
    exact remainder_nonneg K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps ε o e k J
  · exact le_rfl

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
      freeTotal K S D Γ T Θ ψ G hν hG H grid centers W hW m side F massEps ε ≤
    ActualPoissonScale.fieldConstant K *
      budgetTotal K S D Γ T Θ ψ G hν hG H grid centers W hW m side F massEps ε
        Z M r ell V eta delta A B R := by
  unfold freeTotal budgetTotal
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o ho
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
      (remainder_nonneg K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps ε o e k J)
    calc
      _ = normalizedScalar K S D Z r ell V T.radius T.scale (grid k)
          (FirstLocalizedEnergy.divisor K S D T o)
          (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
          (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
            o.1.val o.2.1.val false e) *
          remainder K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps ε o e k J := by
        simpa only [mul_assoc] using normalized_summand_eq K S D Γ T Θ ψ G hν hG H
          grid centers W hW m side F massEps ε Z r ell V o e k J
      _ ≤ _ := hb.trans_eq (by ring)
  · simp only [ha, if_false, mul_zero, le_refl]

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedNormalization

end

