import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedCutoff
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedProduction

/-!
# Whole-parent Cauchy for the genuine locally truncated first source

The original old-label sum and every actual cube, extraction, divisor
and sector are retained. One common positive measure supplies both roots.
The full source identity is proved from the primitive Poisson formula.
-/

noncomputable section
namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRetained
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open FirstParentRows FirstLocalizedEnergy FirstLocalizedCutoff FirstNormPoolEnergy
  FirstSourceColumns FirstSourcePartition FirstPoissonNormalization CanonicalNormPools
  FirstColumnAssembly FirstPositiveSource
open HeckeSkeleton.Moments.MOMInvStep.FullMobius
open scoped Classical BigOperators nonZeroDivisors

private theorem sum_label_source {α β : Type*} [Fintype α]
    (Z : α → Type*) [∀ a, Fintype (Z a)] (L : Finset β) (F : ∀ a, β → Z a → ℝ) :
    (∑ f ∈ L, ∑ a : α, ∑ z : Z a, F a f z) =
      ∑ j : (Σ a : α, Σ f : L, Z a), F j.1 j.2.1.val j.2.2 := by
  rw [Finset.sum_comm]
  simp only [Fintype.sum_sigma, Finset.sum_coe_sort]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*}
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

def term (T : FirstParentEnergy.Data K S (σ := σ))
    (o : OuterIndex K S D T) (f : Ext) (z : Ext × Sector) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct o.2.2.2.val) : ℂ) *
    (outerFactor K S D T.radius (divisor K S D T o)
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val : ℂ) *
    CanonicalFirstEnergy.originalSource K S D Γ T.columns
      (FirstParentEnergy.columnPool K S T) (FirstParentEnergy.columnPool K S T)
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
      (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S f)
      (CanonicalIdealRow.ofExterior K S z.1) (divisor K S D T o).val z.2
      (FirstLocalizedEnergy.profile K S D Γ μv ν T o z)

def pointEnergy (G : HeckeCharacter K) (T : FirstParentEnergy.Data K S (σ := σ))
    (o : OuterIndex K S D T) (f : Ext) (z : Ext × Sector) (side : Bool) : ℝ :=
  FirstPositiveSource.sourceEnergy K S D Γ T.columns G
    (FirstLocalizedEnergy.profile K S D Γ μv ν T o z) T.scale
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
    (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z.1)
    (divisor K S D T o).val z.2

theorem pointEnergy_nonneg (G : HeckeCharacter K)
    (T : FirstParentEnergy.Data K S (σ := σ))
    (o : OuterIndex K S D T) (f : Ext) (z : Ext × Sector) (side : Bool) :
    0 ≤ pointEnergy K S D Γ μv ν G T o f z side :=
  FirstParentEnergy.positiveEnergy_nonneg K S Γ _ _ _ _ _ _

def dataAt (T : FirstParentEnergy.Data K S (σ := σ))
    (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (o : OuterIndex K S D T) (f : Ext) :
    FirstParentEnergy.Data K S (σ := σ) :=
  { T with label := f, frequencyBound := (H o).val }

def indexAt (T : FirstParentEnergy.Data K S (σ := σ))
    (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (o : OuterIndex K S D T) (f : Ext)
    (z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val) :
    FirstParentEnergy.Index K S D Γ (dataAt K S D T H o f) :=
  ⟨o.1, o.2.1, o.2.2.1, o.2.2.2, z⟩

theorem term_norm_le (hallowed : AllowedGeneratorInput K Sset D)
    (G : HeckeCharacter K) (T : FirstParentEnergy.Data K S (σ := σ))
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (o : OuterIndex K S D T) (f : Ext)
    (z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val) :
    ‖term K S D Γ μv ν T o f z.val‖ ≤
      (maskWeight K S D T o *
        (‖T.columns.labelWeight o.1.val f‖ * ‖T.columns.labelWeight o.2.1.val f‖)) *
      (Real.sqrt (pointEnergy K S D Γ μv ν G T o f z.val false) *
        Real.sqrt (pointEnergy K S D Γ μv ν G T o f z.val true)) := by
  exact FirstParentEnergy.sourceTerm_norm_le K S D Γ μv ν hallowed G
    (dataAt K S D T H o f) hcal (indexAt K S D Γ T H o f z)

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

def retained (T : FirstParentEnergy.Data K S (σ := σ)) (f : Ext) (Z tau : ℝ) : ℂ :=
  FirstAdaptiveTruncation.canonicalRetained K S D Γ hΓ μv T.columns f T.cubes
    (FirstParentEnergy.columnPool K S T) T.archTest T.localTest T.locallyConstant
    T.compactSupport T.mask T.radius (fineCutoff K S D T.radius T.scale Z tau)

theorem retained_eq_sum (T : FirstParentEnergy.Data K S (σ := σ)) (f : Ext)
    (Z tau : ℝ) (hZ : 0 < Z) :
    retained K S D Γ μv hΓ T f Z tau =
      ∑ o : OuterIndex K S D T,
        ∑ z : FirstDualTruncation.sectorCutoff K S D Γ
          (sourceCutoff K S D T Z tau hZ o).val,
          term K S D Γ μv ν T o f z.val := by
  rw [retained, FirstAdaptiveTruncation.canonicalRetained_eq_slices K S D Γ hΓ μv ν
    T.columns f T.cubes (FirstParentEnergy.columnPool K S T) T.archTest T.localTest
    T.locallyConstant T.compactSupport T.mask T.radius
    (fineCutoff K S D T.radius T.scale Z tau)
    (fun n₁ n₂ r₁ r₂ b₁ b₂ hs => fineCutoff_frozen K S D T.radius T.scale Z tau
      n₁ n₂ r₁ r₂ b₁ b₂ hs)
    (fun r₁ r₂ b₁ b₂ => residualScale K S T.scale r₁ r₂ b₁ b₂ false)
    (fun r₁ r₂ b₁ b₂ => residualScale K S T.scale r₁ r₂ b₁ b₂ true)]
  simp only [OuterIndex, Fintype.sum_sigma, FirstAdaptiveTruncation.sliceValue,
    term, sourceCutoff, outerAnchor, divisor, FirstLocalizedEnergy.profile,
    Finset.sum_coe_sort]

/-- Common Cauchy is applied once to the complete original weighted
parent, with precisely the raw positive energies consumed by the first
localized Mellin and row-fiber construction. -/
theorem weighted_retained_norm_le (hallowed : AllowedGeneratorInput K Sset D)
    (G : HeckeCharacter K) (T : FirstParentEnergy.Data K S (σ := σ))
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (L : Finset Ext) (w : Ext → ℝ) (hw : ∀ f ∈ L, 0 ≤ w f)
    (Z tau : ℝ) (hZ : 0 < Z) :
    (∑ f ∈ L, w f * ‖retained K S D Γ μv hΓ T f Z tau‖) ≤
      Real.sqrt (rawTotal K S D Γ μv ν G T (sourceCutoff K S D T Z tau hZ) L w false) *
      Real.sqrt (rawTotal K S D Γ μv ν G T (sourceCutoff K S D T Z tau hZ) L w true) := by
  let H := sourceCutoff K S D T Z tau hZ
  let J := Σ o : OuterIndex K S D T, Σ f : L,
    FirstDualTruncation.sectorCutoff K S D Γ (H o).val
  let weight : J → ℝ := fun j =>
    maskWeight K S D T j.1 * pairWeight K S T.columns j.1.1.val j.1.2.1.val w j.2.1.val
  let E (side : Bool) : J → ℝ := fun j =>
    pointEnergy K S D Γ μv ν G T j.1 j.2.1.val j.2.2.val side
  have he (side : Bool) :
      (∑ j : J, weight j * E side j) = rawTotal K S D Γ μv ν G T H L w side := by
    simp only [J, Fintype.sum_sigma, Finset.sum_coe_sort, weight, E, rawTotal,
      pointEnergy, Finset.mul_sum, mul_assoc]
  have hm (j : J) : 0 ≤ weight j := by
    exact mul_nonneg (maskWeight_nonneg K S D T j.1)
      (mul_nonneg (mul_nonneg (hw j.2.1.val j.2.1.property) (norm_nonneg _))
        (norm_nonneg _))
  have hc := common_weighted_cauchy Finset.univ weight (E false) (E true)
    (fun j hj => hm j)
    (fun j hj => pointEnergy_nonneg K S D Γ μv ν G T j.1 j.2.1.val j.2.2.val false)
    (fun j hj => pointEnergy_nonneg K S D Γ μv ν G T j.1 j.2.1.val j.2.2.val true)
  rw [he false, he true] at hc
  apply le_trans _ hc
  have hpoint (f : Ext) :
      ‖retained K S D Γ μv hΓ T f Z tau‖ ≤
        ∑ o : OuterIndex K S D T,
          ∑ z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val,
            (maskWeight K S D T o *
              (‖T.columns.labelWeight o.1.val f‖ * ‖T.columns.labelWeight o.2.1.val f‖)) *
            (Real.sqrt (pointEnergy K S D Γ μv ν G T o f z.val false) *
              Real.sqrt (pointEnergy K S D Γ μv ν G T o f z.val true)) := by
    rw [retained_eq_sum K S D Γ μv ν hΓ T f Z tau hZ]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro o ho
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun z hz => term_norm_le K S D Γ μv ν hallowed G T hcal H o f z)
  calc
    _ ≤ ∑ f ∈ L, w f *
        (∑ o : OuterIndex K S D T,
          ∑ z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val,
            (maskWeight K S D T o *
              (‖T.columns.labelWeight o.1.val f‖ * ‖T.columns.labelWeight o.2.1.val f‖)) *
            (Real.sqrt (pointEnergy K S D Γ μv ν G T o f z.val false) *
              Real.sqrt (pointEnergy K S D Γ μv ν G T o f z.val true))) :=
      Finset.sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left (hpoint f) (hw f hf))
    _ = ∑ f ∈ L, ∑ o : OuterIndex K S D T,
          ∑ z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val,
            (maskWeight K S D T o * pairWeight K S T.columns o.1.val o.2.1.val w f) *
            (Real.sqrt (pointEnergy K S D Γ μv ν G T o f z.val false) *
              Real.sqrt (pointEnergy K S D Γ μv ν G T o f z.val true)) := by
      simp only [Finset.mul_sum, pairWeight, mul_assoc, mul_left_comm, mul_comm]
    _ = _ := sum_label_source _ L _

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRetained
end

