import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentFiber

/-!
# Exact finite row aggregation inside the first common Fourier integral

Every integral in these rearrangements has already been proved
integrable for the actual centered family. In particular the old-label
and frequency sums are moved together under the same Fourier measure.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstBranchIntegration

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstColumnAssembly
  FirstCenteredPositiveEnergy FirstCenteredMellinEnergy FirstParentRows FirstParentFiber
  FirstMobiusGeometry FirstPositiveSource CommonKernel FirstCommonEnvelope
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "E" => CanonicalIdealRow.exteriorMonoid K S

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable {σ ι : Type*} [Fintype ι]
variable (C : CanonicalBlock.ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
variable (X : {r : ℝ // 0 < r})
  (r₁ r₂ b₁ b₂ : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) (side : Bool)
variable (centers : FirstCenteredPositiveEnergy.Centering K S D ι X r₁ r₂ b₁ b₂ side)
variable (f z : CanonicalIdealRow.exteriorMonoid K S)
  (d : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (ξ : CanonicalSectors.UnitClasses K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)

def branchFactor (k : ι) (e : overlapPool K S X r₁ r₂ b₁ b₂ false) : ℝ :=
  ((height K Sset (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e))⁻¹ *
      (C.slots.powerset.card : ℝ)) *
    (((centerScale X (centers.center k)).val ^ (-(1 / 2 : ℝ))) ^ 2 *
      (∫ t : ℝ, ‖MellinSeparation.density W hW t‖))

theorem branchFactor_nonneg (k : ι) (e : overlapPool K S X r₁ r₂ b₁ b₂ false) :
    0 ≤ branchFactor K S D C X r₁ r₂ b₁ b₂ side centers W hW k e := by
  unfold branchFactor
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (height_pos K Sset _).le) (Nat.cast_nonneg _))
    (mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => norm_nonneg _)))

include hΓ in
theorem integral_branchEnergy (k : ι) (e : overlapPool K S X r₁ r₂ b₁ b₂ false)
    (m : ℕ) :
    (∫ η : LogPlane, frequencyEnvelope m η *
      branchEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW k e η) =
      branchFactor K S D C X r₁ r₂ b₁ b₂ side centers W hW k e *
        ∑ J ∈ C.slots.powerset,
          ‖assignedMark K S C r₁ r₂ b₁ b₂ side
            (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) J‖ ^ 2 *
          ∫ η : LogPlane, frequencyEnvelope m η *
            mellinEnergy K S Γ D C Θ ψ G hν hG J (centerScale X (centers.center k)).val
              (-(1 / 2 : ℝ)) (firstTriple K S r₁ r₂ b₁ b₂
                (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e))
              (retainedLabel K S r₁ r₂ b₁ b₂).val.val d W hW
              (CanonicalIdealRow.toExterior K S (firstRow K S r₁ r₂ b₁ b₂ f z), ξ)
              (signedCoordinate side η) := by
  unfold branchEnergy
  simp_rw [mul_left_comm (frequencyEnvelope m _)]
  rw [integral_const_mul]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum C.slots.powerset (fun J hJ => ?_)]
  · apply Finset.sum_congr rfl
    intro J hJ
    simp_rw [mul_left_comm (frequencyEnvelope m _)]
    rw [integral_const_mul]
  · have hi := fourier_mellinEnergy_integrable K S Γ D C Θ ψ G hν hG J
      (centerScale X (centers.center k)).val (-(1 / 2 : ℝ))
      (firstTriple K S r₁ r₂ b₁ b₂ (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e))
      (retainedLabel K S r₁ r₂ b₁ b₂).val.val d hΓ W hW
      (CanonicalIdealRow.toExterior K S (firstRow K S r₁ r₂ b₁ b₂ f z), ξ)
      (frequencyEnvelope m) (frequencyEnvelope_integrable m)
      (signedCoordinate side) (signedCoordinate_continuous side)
    simpa only [mul_left_comm] using hi.const_mul
      (‖assignedMark K S C r₁ r₂ b₁ b₂ side
        (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) J‖ ^ 2)

include hΓ in
theorem centeredEnergy_expanded (m : ℕ) :
    centeredEnergy K S D Γ C Θ ψ G hν hG X r₁ r₂ b₁ b₂ side centers f z d ξ W hW
      (frequencyEnvelope m) =
      ∑ k : ι, ∑ e : overlapPool K S X r₁ r₂ b₁ b₂ false,
        if centers.assignment e = k then
          ‖(moebius e.val : ℂ)‖ *
          (branchFactor K S D C X r₁ r₂ b₁ b₂ side centers W hW k e *
            ∑ J ∈ C.slots.powerset,
              ‖assignedMark K S C r₁ r₂ b₁ b₂ side
                (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) J‖ ^ 2 *
              ∫ η : LogPlane, frequencyEnvelope m η *
                mellinEnergy K S Γ D C Θ ψ G hν hG J (centerScale X (centers.center k)).val
                  (-(1 / 2 : ℝ)) (firstTriple K S r₁ r₂ b₁ b₂
                    (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e))
                  (retainedLabel K S r₁ r₂ b₁ b₂).val.val d W hW
                  (CanonicalIdealRow.toExterior K S (firstRow K S r₁ r₂ b₁ b₂ f z), ξ)
                  (signedCoordinate side η))
        else 0 := by
  unfold centeredEnergy
  simp_rw [integral_branchEnergy K S D Γ hΓ]

include hΓ in
/-- The whole finite old-label/frequency source is moved under the same
true Fourier measure. The row conversion is proved by actual ideal
multiplication, and the original common weight remains unchanged. -/
theorem actual_sourceRows_integral
    (J : Finset σ) (U α : ℝ) (γ : OuterTriple K) (j : Ideal (𝓞 K))
    (T : Finset (FirstCanonicalLabel.SourcePair K S Γ)) (w : Ext → ℝ) (m : ℕ) :
    (∑ x ∈ T, w x.1 *
      ∫ η : LogPlane, frequencyEnvelope m η *
        mellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d W hW
          (CanonicalIdealRow.toExterior K S
            (firstRow K S r₁ r₂ b₁ b₂
              (CanonicalIdealRow.ofExterior K S x.1)
              (CanonicalIdealRow.ofExterior K S x.2.1)), x.2.2)
          (signedCoordinate side η)) =
      ∫ η : LogPlane, frequencyEnvelope m η *
        sourceMellinEnergy K S Γ D C Θ ψ G hν hG J U α γ j d W hW
          (cubeDilation K S r₁ r₂ b₁ b₂) T w (signedCoordinate side η) := by
  simp only [FirstParentRows.firstRow_eq]
  unfold sourceMellinEnergy
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum T (fun x hx => ?_)]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with η
    change w x.1 * (frequencyEnvelope m η * _) = frequencyEnvelope m η * (w x.1 * _)
    ring
  · have hi := fourier_mellinEnergy_integrable K S Γ D C Θ ψ G hν hG J U α γ j d hΓ
      W hW (row K S Γ (cubeDilation K S r₁ r₂ b₁ b₂) x)
      (frequencyEnvelope m) (frequencyEnvelope_integrable m)
      (signedCoordinate side) (signedCoordinate_continuous side)
    simpa only [mul_left_comm] using hi.const_mul (w x.1)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstBranchIntegration

end
