import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLiveNormalization
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSecondReduction
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSpectralAggregation

/-!
# The original normalized first energy as one arithmetic source

The first prefactor below is the literal physical scalar. Its bound is
applied only after the source has been partitioned into actual norm boxes.
The old-label liveness test and the unique center assignment remain in the
source weight. Finite sums pass through the original spectral measure
using proved integrability of the actual free energies.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedSource

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstOuterCenters FirstToSecondData FirstPositiveSource FirstFreeMellinEnergy
  FirstErrorIntegration FirstCenteredErrorIntegrals CommonKernel InverseRowMajorant
  FirstSpectralAggregation FirstCenteredPositiveEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ ι : Type*} [Fintype ι]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid)
variable (side : Bool)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps ε : ℝ)
variable (Z r ell V : ℝ)
local notation "Idx" => FirstErrorSource.Index K S D T

def firstScalar (k : ι) (i : Idx) : ℝ :=
  FirstActualPrefactor.normalizedScalar K S D Z r ell V T.radius T.scale (grid k)
    (FirstLocalizedEnergy.divisor K S D T i.1)
    (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
    i.1.1.val i.1.2.1.val
    (FirstMobiusGeometry.overlapIdeal K S D T.scale
      (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
      i.1.1.val i.1.2.1.val false i.2)

theorem firstScalar_nonneg (hZ : 0 ≤ Z) (k : ι) (i : Idx) :
    0 ≤ firstScalar K S D T grid Z r ell V k i := by
  unfold firstScalar FirstActualPrefactor.normalizedScalar FirstActualPrefactor.columnScale
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hZ _)
      (FirstPoissonNormalization.outerFactor_nonneg K S D T.radius
        (FirstLocalizedEnergy.divisor K S D T i.1) _ _ _ _))
    (mul_nonneg (inv_nonneg.mpr (height_pos K Sset _).le) (sq_nonneg _))

def weight (k : ι) (i : Idx) : ℝ :=
  firstScalar K S D T grid Z r ell V k i * mobiusWeight K S D T i *
    FirstLocalizedEnergy.radialScale K S D T i.1 ^ ε * (R i.1).val ^ massEps

theorem weight_nonneg (hZ : 0 ≤ Z) (k : ι) (i : Idx) :
    0 ≤ weight K S D T grid R massEps ε Z r ell V k i := by
  unfold weight
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (firstScalar_nonneg K S D T grid Z r ell V hZ k i)
      (mobiusWeight_nonneg K S D T i))
    (Real.rpow_nonneg (FirstLocalizedEnergy.radialScale_pos K S D T i.1).le _))
    (Real.rpow_nonneg (R i.1).property.le _)

def liveWeight (k : ι) (i : Idx) : ℝ :=
  if FirstLiveCappedFreeEnergy.alive K S D Γ T H L i.1 ∧
      centers.assignment side i.1 i.2 = k then
    weight K S D T grid R massEps ε Z r ell V k i
  else 0

theorem liveWeight_nonneg (hZ : 0 ≤ Z) (k : ι) (i : Idx) :
    0 ≤ liveWeight K S D Γ T H L grid centers side R massEps ε Z r ell V k i := by
  unfold liveWeight
  split_ifs
  · exact weight_nonneg K S D T grid R massEps ε Z r ell V hZ k i
  · exact le_rfl

variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)

def freeAt (k : ι) (J : Finset σ) (i : Idx) (s : ℝ) : ℝ :=
  freeEnergyAt K S Γ D T.columns Θ ψ G hν hG J
    (centerScale T.scale (grid k)).val (-(1 / 2 : ℝ))
    (triple K S D T i.1 i.2) (label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val (R i.1) s

def sourceAt (k : ι) (J : Finset σ) (s : ℝ) : ℝ :=
  ∑ i : Idx,
    liveWeight K S D Γ T H L grid centers side R massEps ε Z r ell V k i *
      ‖mark K S D T side i J‖ ^ 2 *
      freeAt K S D Γ T grid R Θ ψ G hν hG k J i s

theorem sourceAt_nonneg (hZ : 0 ≤ Z) (k : ι) (J : Finset σ) (s : ℝ) :
    0 ≤ sourceAt K S D Γ T H L grid centers side R massEps ε Z r ell V
      Θ ψ G hν hG k J s := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (liveWeight_nonneg K S D Γ T H L grid centers side R massEps ε
      Z r ell V hZ k i) (sq_nonneg _))
    (freeEnergyAt_nonneg K S Γ D T.columns Θ ψ G hν hG J
      (centerScale T.scale (grid k)).val (-(1 / 2 : ℝ))
      (triple K S D T i.1 i.2) (label K S D T i.1).val.val
      (FirstLocalizedEnergy.divisor K S D T i.1).val (R i.1) s)

variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (m : ℕ)

/-- All original arithmetic sources share one unchanged Fourier/Mellin
integral. There is no arithmetic-source cardinality in this equality. -/
theorem sourceAverage_eq (hZ : 0 ≤ Z) (k : ι) (J : Finset σ) :
    spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
      (sourceAt K S D Γ T H L grid centers side R massEps ε Z r ell V Θ ψ G hν hG k J) =
    ∑ i : Idx,
      liveWeight K S D Γ T H L grid centers side R massEps ε Z r ell V k i *
        ‖mark K S D T side i J‖ ^ 2 *
        spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
          (freeAt K S D Γ T grid R Θ ψ G hν hG k J i) := by
  let c : Idx → ℝ := fun i =>
    liveWeight K S D Γ T H L grid centers side R massEps ε Z r ell V k i *
      ‖mark K S D T side i J‖ ^ 2
  have hc (i : Idx) : 0 ≤ c i := mul_nonneg
    (liveWeight_nonneg K S D Γ T H L grid centers side R massEps ε
      Z r ell V hZ k i) (sq_nonneg _)
  have hf (i : Idx) := freeEnergyAt_continuous K S Γ D T.columns Θ ψ G hν hG J
    (centerScale T.scale (grid k)).val (-(1 / 2 : ℝ))
    (triple K S D T i.1 i.2) (label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val (R i.1)
  have hf0 (i : Idx) (s : ℝ) := freeEnergyAt_nonneg K S Γ D T.columns Θ ψ G hν hG J
    (centerScale T.scale (grid k)).val (-(1 / 2 : ℝ))
    (triple K S D T i.1 i.2) (label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val (R i.1) s
  let B : Idx → ℝ := fun i => freeEnergyBound K S Γ D T.columns Θ ψ G hν hG J
    (centerScale T.scale (grid k)).val (-(1 / 2 : ℝ))
    (triple K S D T i.1 i.2) (label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val (R i.1)
  have hb (i : Idx) (s : ℝ) : freeAt K S D Γ T grid R Θ ψ G hν hG k J i s ≤ B i :=
    freeEnergyAt_bound K S Γ D T.columns Θ ψ G hν hG J
      (centerScale T.scale (grid k)).val (-(1 / 2 : ℝ))
      (triple K S D T i.1 i.2) (label K S D T i.1).val.val
      (FirstLocalizedEnergy.divisor K S D T i.1).val (R i.1) s
  have he := spectralAverage_finsetSum (Finset.univ : Finset Idx)
    (MellinSeparation.density W hW) m (signedCoordinate side)
    (signedCoordinate_continuous side)
    (fun i s => c i * freeAt K S D Γ T grid R Θ ψ G hν hG k J i s)
    (fun i _ => (hf i).const_mul (c i))
    (fun i _ s => mul_nonneg (hc i) (hf0 i s))
    (fun i => c i * B i)
    (fun i _ s => mul_le_mul_of_nonneg_left (hb i s) (hc i))
  simpa only [sourceAt, spectralAverage_const_mul, c] using he

/-- One original branch, with the actual normalized Poisson scalar,
is the literal source weight times the original spectral average. -/
theorem normalized_branch_eq (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) (k : ι) (J : Finset σ) :
    Z ^ (-r - 2 * ell - V) *
      ((FirstLocalizedEnergy.maskWeight K S D T o *
        FirstLocalizedEnergy.radialScale K S D T o ^ ε) *
        (FirstLocalizedFreeEnergy.branchCoefficient K S D T grid centers W hW side o e k J *
          FirstCappedFreeEnergy.freeRowIntegral K S D Γ T Θ ψ G hν hG
            grid W hW m side R massEps o e k J)) =
      ((T.columns.slots.powerset.card : ℝ) * (rowCovolume K S)⁻¹ * mellinMass W hW) *
        (weight K S D T grid R massEps ε Z r ell V k ⟨o,e⟩ *
          ‖mark K S D T side ⟨o,e⟩ J‖ ^ 2 *
          spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
            (freeAt K S D Γ T grid R Θ ψ G hν hG k J ⟨o,e⟩)) := by
  rw [FirstCappedNormalization.normalized_summand_eq K S D Γ T Θ ψ G hν hG
    grid centers W hW m side R massEps ε Z r ell V o e k J]
  unfold FirstCappedNormalization.remainder FirstCappedFreeEnergy.freeRowIntegral
    freeMellinEnergy spectralAverage firstScalar weight mark mobiusWeight mellinMass freeAt
    FirstToSecondData.triple FirstToSecondData.label
  ring

private theorem reorder_centers_marks {α β κ : Type*} [Fintype κ] [Fintype β]
    (P : Finset α) (F : κ → α → β → ℝ) :
    (∑ k : κ, ∑ J ∈ P, ∑ i : β, F k J i) =
      ∑ i : β, ∑ k : κ, ∑ J ∈ P, F k J i := by
  calc
    _ = ∑ k : κ, ∑ i : β, ∑ J ∈ P, F k J i := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Exact normalization and assembly of the full live first source.
The physical weight is evaluated before any logarithmic norm estimate,
and each center receives only its actual arithmetic source. -/
theorem normalized_freeTotal_eq (hZ : 0 ≤ Z) :
    Z ^ (-r - 2 * ell - V) *
      FirstLiveCappedFreeEnergy.freeTotal K S D Γ T Θ ψ G hν hG
        H L grid centers W hW m side R massEps ε =
    ((T.columns.slots.powerset.card : ℝ) * (rowCovolume K S)⁻¹ * mellinMass W hW) *
      ∑ k : ι, ∑ J ∈ T.columns.slots.powerset,
        spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
          (sourceAt K S D Γ T H L grid centers side R massEps ε Z r ell V
            Θ ψ G hν hG k J) := by
  simp_rw [sourceAverage_eq K S D Γ T H L grid centers side R massEps ε
    Z r ell V Θ ψ G hν hG W hW m hZ]
  rw [reorder_centers_marks]
  simp only [Fintype.sum_sigma]
  unfold FirstLiveCappedFreeEnergy.freeTotal
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o ho
  have hswap :
      (∑ e : FirstOuterCenters.Overlap K S D T o, ∑ k : ι, ∑ J ∈ T.columns.slots.powerset,
        liveWeight K S D Γ T H L grid centers side R massEps ε Z r ell V k ⟨o,e⟩ *
          ‖mark K S D T side ⟨o,e⟩ J‖ ^ 2 *
          spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
            (freeAt K S D Γ T grid R Θ ψ G hν hG k J ⟨o,e⟩)) =
      ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o, ∑ J ∈ T.columns.slots.powerset,
        liveWeight K S D Γ T H L grid centers side R massEps ε Z r ell V k ⟨o,e⟩ *
          ‖mark K S D T side ⟨o,e⟩ J‖ ^ 2 *
          spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
            (freeAt K S D Γ T grid R Θ ψ G hν hG k J ⟨o,e⟩) := Finset.sum_comm
  rw [hswap]
  by_cases halive : FirstLiveCappedFreeEnergy.alive K S D Γ T H L o
  · simp only [if_pos halive, mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro e he
    by_cases hassigned : centers.assignment side o e = k
    · simp only [if_pos hassigned, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      have heq := normalized_branch_eq K S D Γ T grid centers side R massEps ε
        Z r ell V Θ ψ G hν hG W hW m o e k J
      simpa only [liveWeight, if_pos ⟨halive, hassigned⟩,
        FirstLiveCappedFreeEnergy.freeRowIntegral_eq_capped, mul_assoc] using heq
    · simp [hassigned, liveWeight]
  · simp [halive, liveWeight]

/-- The exact normalized first energy, expressed through its original
finite arithmetic source and the two common spectral integrations. -/
def total : ℝ :=
  ((T.columns.slots.powerset.card : ℝ) * (rowCovolume K S)⁻¹ * mellinMass W hW) *
    ∑ k : ι, ∑ J ∈ T.columns.slots.powerset,
      spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
        (sourceAt K S D Γ T H L grid centers side R massEps ε Z r ell V
          Θ ψ G hν hG k J)

theorem total_nonneg (hZ : 0 ≤ Z) :
    0 ≤ total K S D Γ T H L grid centers side R massEps ε Z r ell V Θ ψ G hν hG W hW m := by
  apply mul_nonneg
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (inv_nonneg.mpr (rowCovolume_pos K S).le)) (mellinMass_nonneg W hW)
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro J hJ
  apply integral_nonneg
  intro ξ
  apply mul_nonneg (FirstCommonEnvelope.frequencyEnvelope_nonneg m ξ)
  apply integral_nonneg
  intro t
  exact mul_nonneg (norm_nonneg _)
    (sourceAt_nonneg K S D Γ T H L grid centers side R massEps ε Z r ell V
      Θ ψ G hν hG hZ k J _)

theorem total_eq_normalized_freeTotal (hZ : 0 ≤ Z) :
    total K S D Γ T H L grid centers side R massEps ε Z r ell V Θ ψ G hν hG W hW m =
      Z ^ (-r - 2 * ell - V) *
        FirstLiveCappedFreeEnergy.freeTotal K S D Γ T Θ ψ G hν hG
          H L grid centers W hW m side R massEps ε :=
  (normalized_freeTotal_eq K S D Γ T H L grid centers side R massEps ε Z r ell V
    Θ ψ G hν hG W hW m hZ).symm

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedSource

end
