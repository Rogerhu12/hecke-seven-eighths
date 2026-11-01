import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorMass
import HeckeSkeleton.Moments.MOM_INV_STEP.SourceLengths
import HeckeSkeleton.Moments.MOM_INV_STEP.Normalization

/-!
# The sharp first-outer error budget from actual norm annuli

The cube table gives N(q₀) ≤ Z^(ell+R/2-j+5η/2), while the retained label
is literally C J. The divisor-row source count therefore has exponent
ell+B+R/2+t+11η/2, with an independently prescribed small-power loss.

All constants precede Z and the source data. Empty norm boxes are
handled without imposing artificial lower bounds on their exponents.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorBudget

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep FixedTripleFibers FixedTripleEnergy SourceLengths
open FirstParentEnergy FirstParentRows FirstErrorSource CanonicalChildren
open PositiveReconstruction
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*}

def cubeConductor (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
    (i : FirstErrorSource.Index K S D T) : Ideal (𝓞 K) :=
  let B := bare K S D Γ T hmask i
  CubeLabels.R1 B.b₁.val B.b₂.val
    (PositiveReconstruction.Source.epsilon B.refs.1)
    (PositiveReconstruction.Source.epsilon B.refs.2)

theorem cubeConductor_nonzero (T : FirstParentEnergy.Data K S (σ := σ))
    (hmask : T.mask = ∅) (i : FirstErrorSource.Index K S D T) :
    cubeConductor K S D Γ T hmask i ≠ 0 := by
  exact IdealMobiusMask.primeProduct_ne_bot _

theorem cubeConductor_norm (T : FirstParentEnergy.Data K S (σ := σ))
    (hmask : T.mask = ∅) (i : FirstErrorSource.Index K S D T) :
    ((cubeConductor K S D Γ T hmask i).absNorm : ℝ) =
      FirstPoissonNormalization.cubeNorm K S D
        (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
        i.1.1.val i.1.2.1.val := by
  exact congrArg (fun J : Ideal (𝓞 K) => (J.absNorm : ℝ))
    (CanonicalGroupedGauss.cubeIdeal_val K S D
      (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
      i.1.1.val i.1.2.1.val).symm

theorem cubeQ_bound (T : FirstParentEnergy.Data K S (σ := σ))
    (hmask : T.mask = ∅) (i : FirstErrorSource.Index K S D T)
    (Z ell R j eta : ℝ) (hZ : 0 < Z)
    (hb₁ : ((bare K S D Γ T hmask i).b₁.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta))
    (hb₂ : ((bare K S D Γ T hmask i).b₂.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta))
    (hR : ((cubeConductor K S D Γ T hmask i).absNorm : ℝ) ≤ Z ^ (R + eta))
    (hJ : Z ^ (j - eta) ≤ ((bare K S D Γ T hmask i).cubeJ.absNorm : ℝ)) :
    ((bare K S D Γ T hmask i).cubeQ.absNorm : ℝ) ≤
      Z ^ (ell + R / 2 - j + 5 * eta / 2) := by
  let B := bare K S D Γ T hmask i
  exact cube_quotient_sharp_bound B.valid (cubeConductor K S D Γ T hmask i)
    (cubeConductor_nonzero K S D Γ T hmask i)
    (CubeLabels.s_dvd_R1 B.b₁.val B.b₂.val
      (PositiveReconstruction.Source.epsilon B.refs.1)
      (PositiveReconstruction.Source.epsilon B.refs.2))
    Z ell R j eta hZ hb₁ hb₂ hR hJ

theorem firstLabel_bound (T : FirstParentEnergy.Data K S (σ := σ))
    (hmask : T.mask = ∅) (i : FirstErrorSource.Index K S D T)
    (Z B j eta : ℝ) (hZ : 0 < Z)
    (hC : ((bare K S D Γ T hmask i).firstCommon.absNorm : ℝ) ≤ Z ^ (B + eta))
    (hJ : ((bare K S D Γ T hmask i).cubeJ.absNorm : ℝ) ≤ Z ^ (j + eta)) :
    ((bare K S D Γ T hmask i).firstLabel.val.val.absNorm : ℝ) ≤
      Z ^ (B + j + 2 * eta) := by
  rw [(bare K S D Γ T hmask i).firstLabel_val, map_mul, Nat.cast_mul]
  calc
    _ ≤ Z ^ (B + eta) * Z ^ (j + eta) :=
      mul_le_mul hC hJ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [← Real.rpow_add hZ]; congr 1; ring

theorem mass_power_identity (Z q e f eps : ℝ) (hZ : 0 < Z) :
    (Z ^ q * Z ^ e) ^ (1 + eps) * (Z ^ q) ^ eps * (Z ^ f) ^ (1 + eps) =
      Z ^ (q + e + f + eps * (2 * q + e + f)) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

/-- The three windows follow from actual original cube norms, the
actual first conductor, the actual C/J annuli and the first overlap.
The exponent loss is chosen before Z and every original source choice. -/
theorem exists_uniform_annular_mass_bound (slotCap : ℕ) (lengthCap loss : ℝ)
    (hcap : 0 ≤ lengthCap) (hloss : 0 < loss) :
    ∃ A : ℝ, 0 < A ∧ ∀ {σ : Type*}
      (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
      (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool)
      (Z ell R B j t eta : ℝ),
      1 ≤ Z → ell ≤ lengthCap → R ≤ lengthCap → B ≤ lengthCap →
      t ≤ lengthCap → eta ≤ lengthCap → 0 ≤ j →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p) →
      (∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
        ‖T.columns.primeWeights j p‖ ≤ 1) →
      T.columns.slots.card ≤ slotCap →
      (∀ i ∈ I,
        ((bare K S D Γ T hmask i).b₁.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta) ∧
        ((bare K S D Γ T hmask i).b₂.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta) ∧
        ((cubeConductor K S D Γ T hmask i).absNorm : ℝ) ≤ Z ^ (R + eta) ∧
        Z ^ (j - eta) ≤ ((bare K S D Γ T hmask i).cubeJ.absNorm : ℝ) ∧
        ((bare K S D Γ T hmask i).cubeJ.absNorm : ℝ) ≤ Z ^ (j + eta) ∧
        ((bare K S D Γ T hmask i).firstCommon.absNorm : ℝ) ≤ Z ^ (B + eta) ∧
        ((bare K S D Γ T hmask i).quotient.val.val.absNorm : ℝ) ≤ Z ^ (t + eta)) →
      (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        ‖FirstOverlapColumns.assignedMark K S T.columns
          (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
          i.1.1.val i.1.2.1.val side
          (FirstMobiusGeometry.overlapIdeal K S D T.scale
            (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
            i.1.1.val i.1.2.1.val false i.2) J‖ ^ 2) ≤
        A * Z ^ (ell + B + R / 2 + t + 11 * eta / 2 + loss) := by
  let eps : ℝ := loss / (13 * lengthCap + 1)
  have hden : 0 < 13 * lengthCap + 1 := by positivity
  have heps : 0 < eps := div_pos hloss hden
  obtain ⟨A,hA,hbound⟩ := FirstErrorMass.exists_all_original_mass_bound
    K S D Γ slotCap eps heps
  refine ⟨A,hA,?_⟩
  intro σ T hmask I side Z ell R B j t eta hZ hell hR hB ht heta hj
    hprime hweights hslots hsource
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let q := ell + R / 2 - j + 5 * eta / 2
  let e := t + eta
  let f := B + j + 2 * eta
  have hnorm (i : FirstErrorSource.Index K S D T) (hi : i ∈ I) :
      ((bare K S D Γ T hmask i).cubeQ.absNorm : ℝ) ≤ Z ^ q ∧
      ((bare K S D Γ T hmask i).quotient.val.val.absNorm : ℝ) ≤ Z ^ e ∧
      ((bare K S D Γ T hmask i).firstLabel.val.val.absNorm : ℝ) ≤ Z ^ f := by
    obtain ⟨hb₁,hb₂,hcond,hJlow,hJup,hCup,he⟩ := hsource i hi
    exact ⟨cubeQ_bound K S D Γ T hmask i Z ell R j eta hZ0 hb₁ hb₂ hcond hJlow,
      he,firstLabel_bound K S D Γ T hmask i Z B j eta hZ0 hCup hJup⟩
  by_cases hI : I.Nonempty
  · obtain ⟨i,hi⟩ := hI
    have hq1 : 1 ≤ Z ^ q :=
      one_le_norm_cap _ (bare K S D Γ T hmask i).cubeQ_ne_zero _ (hnorm i hi).1
    have he1 : 1 ≤ Z ^ e :=
      one_le_norm_cap _ (nonZeroDivisors.coe_ne_zero
        (bare K S D Γ T hmask i).quotient.val) _ (hnorm i hi).2.1
    have hf1 : 1 ≤ Z ^ f :=
      one_le_norm_cap _ (nonZeroDivisors.coe_ne_zero
        (bare K S D Γ T hmask i).firstLabel.val) _ (hnorm i hi).2.2
    have hm := hbound T hmask I side hprime hweights hslots
      (Z ^ q) (Z ^ e) (Z ^ f) hq1 he1 hf1 hnorm
    have hbudget : eps * (2 * q + e + f) ≤ loss := by
      have hlength : 2 * q + e + f ≤ 13 * lengthCap := by
        dsimp only [q,e,f]
        linarith
      calc
        eps * (2 * q + e + f) ≤ eps * (13 * lengthCap) :=
          mul_le_mul_of_nonneg_left hlength heps.le
        _ ≤ eps * (13 * lengthCap + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) heps.le
        _ = loss := div_mul_cancel₀ loss hden.ne'
    have hpow : (Z ^ q * Z ^ e) ^ (1 + eps) * (Z ^ q) ^ eps *
        (Z ^ f) ^ (1 + eps) ≤ Z ^ (ell + B + R / 2 + t + 11 * eta / 2 + loss) := by
      rw [mass_power_identity Z q e f eps hZ0]
      apply Real.rpow_le_rpow_of_exponent_le hZ
      dsimp only [q,e,f] at *
      linarith
    have hm' : (∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
        ‖FirstOverlapColumns.assignedMark K S T.columns
          (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
          i.1.1.val i.1.2.1.val side
          (FirstMobiusGeometry.overlapIdeal K S D T.scale
            (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
            i.1.1.val i.1.2.1.val false i.2) J‖ ^ 2) ≤
        A * (Z ^ q * Z ^ e) ^ (1 + eps) * (Z ^ q) ^ eps * (Z ^ f) ^ (1 + eps) := by
      simpa only [FirstOverlapColumns.assignedMark, FirstErrorSource.oldExtracted_eq] using hm
    exact hm'.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hA.le)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hI]
    simp only [Finset.sum_empty]
    positivity

/-- The physical inverse main term, its first prefactor and the actual
outer count leave the explicit C/J saving. No norm-count factor is
charged twice. -/
theorem principal_exponent_identity (M r ell V delta A B R j t : ℝ) :
    firstKappa M r ell V delta A B R +
      firstPhysicalHeight M r ell V delta B j + (r - A - B - t) +
      (ell + B + R / 2 + t) = r + 3 * ell + V - B - j := by
  unfold firstKappa firstPhysicalHeight
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorBudget

end

