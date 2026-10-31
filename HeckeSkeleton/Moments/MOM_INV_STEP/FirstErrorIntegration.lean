import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorSource
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedNormalization
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLiveCappedFreeEnergy

/-!
# Exact center and spectral masses for the first outer errors

Each actual first source has one center. Collapsing its indicator
therefore introduces no factor for the number of centers. A bound
independent of both spectral frequencies integrates against precisely
one Fourier mass and two copies of the original Mellin L¹ mass (the
second copy is the first column Cauchy factor).

This module records these identities with the original mask weights,
overlap weights and assigned marks, and controls the common spectral
mass by a fixed seminorm of the original W.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorIntegration

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep FixedTripleFibers
open FirstParentRows FirstOuterCenters FirstErrorSource InverseRowMajorant
  FirstCommonEnvelope CommonKernel
open scoped Classical BigOperators nonZeroDivisors

def mellinMass (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) : ℝ :=
  ∫ t : ℝ, ‖MellinSeparation.density W hW t‖

def fourierMass (m : ℕ) : ℝ := ∫ ξ : LogPlane, frequencyEnvelope m ξ

theorem mellinMass_nonneg (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) : 0 ≤ mellinMass W hW :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem fourierMass_nonneg (m : ℕ) : 0 ≤ fourierMass m :=
  integral_nonneg (frequencyEnvelope_nonneg m)

theorem constant_double_integral (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (m : ℕ) (E : ℝ) :
    (∫ ξ : LogPlane, frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * E) =
        fourierMass m * mellinMass W hW * E := by
  simp_rw [integral_mul_const]
  unfold fourierMass mellinMass
  ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {σ ι : Type*} [Fintype ι]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
variable (side : Bool)

theorem center_assignment_collapse {A : Type*} [AddCommMonoid A]
    (I : Finset (FirstErrorSource.Index K S D T))
    (F : FirstErrorSource.Index K S D T → ι → A) :
    (∑ i ∈ I, ∑ k : ι,
      if centers.assignment side i.1 i.2 = k then F i k else 0) =
      ∑ i ∈ I, F i (centers.assignment side i.1 i.2) := by
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- Exact collapse in the original o/k/e order of the production sum. -/
theorem full_center_assignment_collapse {A : Type*} [AddCommMonoid A]
    (F : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ι → A) :
    (∑ o : OuterIndex K S D T, ∑ k : ι,
      ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then F o e k else 0) =
      ∑ i : FirstErrorSource.Index K S D T, F i.1 i.2
        (centers.assignment side i.1 i.2) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o ho
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp

/-- The same exact collapse retains the actual nonempty first-row
filter. Its finite index type is definitionally the error-count index. -/
theorem live_center_assignment_collapse
    (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]
    (H : OuterIndex K S D T → {r : ℝ // 0 < r})
    (L : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
    {A : Type*} [AddCommMonoid A]
    (F : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ι → A) :
    (∑ o : OuterIndex K S D T,
      if FirstLiveCappedFreeEnergy.alive K S D Γ T H L o then
        ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
          if centers.assignment side o e = k then F o e k else 0
      else 0) =
      ∑ i ∈ FirstLiveCappedFreeEnergy.liveIndices K S D Γ T H L,
        F i.1 i.2 (centers.assignment side i.1 i.2) := by
  simp only [FirstLiveCappedFreeEnergy.liveIndices, Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o ho
  by_cases hlive : FirstLiveCappedFreeEnergy.alive K S D Γ T H L o
  · simp only [hlive, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp
  · simp [hlive]

variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (m : ℕ)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps ε : ℝ)

def rowError (o : OuterIndex K S D T) (E : ℝ) : ℝ :=
  ((R o).val ^ massEps * (rowCovolume K S)⁻¹) *
    ∫ ξ : LogPlane, frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * E

theorem rowError_eq (o : OuterIndex K S D T) (E : ℝ) :
    rowError K S D T W hW m R massEps o E =
      (R o).val ^ massEps * (rowCovolume K S)⁻¹ *
        fourierMass m * mellinMass W hW * E := by
  rw [rowError, constant_double_integral]
  ring

def mark (i : FirstErrorSource.Index K S D T) (J : Finset σ) : ℂ :=
  FirstOverlapColumns.assignedMark K S T.columns
    (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2 i.1.1.val i.1.2.1.val side
    (FirstMobiusGeometry.overlapIdeal K S D T.scale
      (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
      i.1.1.val i.1.2.1.val false i.2) J

def mobiusWeight (i : FirstErrorSource.Index K S D T) : ℝ :=
  ‖(UniqueFactorizationMonoid.moebius (IdealMobiusMask.primeProduct i.1.2.2.2.val) : ℂ)‖ *
    ‖(UniqueFactorizationMonoid.moebius i.2.val : ℂ)‖

theorem mobiusWeight_nonneg (i : FirstErrorSource.Index K S D T) :
    0 ≤ mobiusWeight K S D T i :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem mobiusWeight_le_one (i : FirstErrorSource.Index K S D T) :
    mobiusWeight K S D T i ≤ 1 :=
  mul_le_one₀ (HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one _)
    (norm_nonneg _) (HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one _)

def spectralMass : ℝ :=
  ((T.columns.slots.powerset.card : ℝ) * (rowCovolume K S)⁻¹) *
    fourierMass m * (mellinMass W hW) ^ 2

def errorTotal (Z : ℝ) (kappa : OuterIndex K S D T → ℝ)
    (I : Finset (FirstErrorSource.Index K S D T))
    (E : FirstErrorSource.Index K S D T → ι → Finset σ → ℝ) : ℝ :=
  ∑ i ∈ I, ∑ k : ι, if centers.assignment side i.1 i.2 = k then
    Z ^ kappa i.1 *
      (mobiusWeight K S D T i * (T.columns.slots.powerset.card : ℝ) *
        mellinMass W hW * FirstLocalizedEnergy.radialScale K S D T i.1 ^ ε *
          ∑ J ∈ T.columns.slots.powerset, ‖mark K S D T side i J‖ ^ 2 *
            rowError K S D T W hW m R massEps i.1 (E i k J))
    else 0

/-- The exact production measure after collapsing the one actual
center and integrating a frequency-independent error. -/
theorem errorTotal_eq (Z : ℝ) (kappa : OuterIndex K S D T → ℝ)
    (I : Finset (FirstErrorSource.Index K S D T))
    (E : FirstErrorSource.Index K S D T → ι → Finset σ → ℝ) :
    errorTotal K S D T grid centers side W hW m R massEps ε Z kappa I E =
      spectralMass K S T W hW m *
        ∑ i ∈ I, Z ^ kappa i.1 *
          FirstLocalizedEnergy.radialScale K S D T i.1 ^ ε *
          (R i.1).val ^ massEps * mobiusWeight K S D T i *
            ∑ J ∈ T.columns.slots.powerset, ‖mark K S D T side i J‖ ^ 2 *
              E i (centers.assignment side i.1 i.2) J := by
  unfold errorTotal
  rw [center_assignment_collapse K S D T grid centers side I]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum, rowError_eq]
  apply Finset.sum_congr rfl
  intro J hJ
  unfold spectralMass
  ring

/-- All remaining spectral cost is a fixed finite seminorm squared
of the original W, uniformly over every center and every m. -/
theorem exists_spectralMass_bound (slotCap : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ)),
      T.columns.slots.card ≤ slotCap →
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (m : ℕ),
      spectralMass K S T W hW m ≤
        C * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨s,A,hA,hbound⟩ := MellinSeparation.density_moment_bound 0
  let V : ℝ := ∫ ξ : LogPlane, fourierEnvelope ξ
  have hV : 0 ≤ V := integral_nonneg fourierEnvelope_nonneg
  have hc : 0 ≤ (rowCovolume K S)⁻¹ := inv_nonneg.mpr (rowCovolume_pos K S).le
  refine ⟨s, ((2 : ℝ) ^ slotCap * (rowCovolume K S)⁻¹) * V * A ^ 2,
    by positivity, ?_⟩
  intro σ T hslots W hW m
  have hcard : (T.columns.slots.powerset.card : ℝ) ≤ (2 : ℝ) ^ slotCap := by
    rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hslots
  have hf : fourierMass m ≤ V :=
    integral_mono (frequencyEnvelope_integrable m) fourierEnvelope_integrable
      (frequencyEnvelope_le m)
  have hm : mellinMass W hW ≤ A * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    simpa [mellinMass] using hbound W hW
  have hleft : ((T.columns.slots.powerset.card : ℝ) * (rowCovolume K S)⁻¹) *
      fourierMass m ≤ ((2 : ℝ) ^ slotCap * (rowCovolume K S)⁻¹) * V :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcard hc) hf (fourierMass_nonneg m)
      (mul_nonneg (pow_nonneg (by norm_num) _) hc)
  calc
    _ ≤ (((2 : ℝ) ^ slotCap * (rowCovolume K S)⁻¹) * V) *
        (A * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 :=
      mul_le_mul hleft (pow_le_pow_left₀ (mellinMass_nonneg W hW) hm 2)
        (sq_nonneg _) (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hc) hV)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorIntegration

end

