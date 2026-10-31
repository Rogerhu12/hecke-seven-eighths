import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstBranchIntegration
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstFiniteAggregation

/-!
# Whole localized first source with the old label and row removed

All actual frozen arithmetic indices are retained. The original common
label weight is pushed through the actual first fiber under the common
Fourier and Mellin measures. Each output family has a fixed center and
the genuine free positive orbital row test with empty external mask.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedFreeEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstColumnAssembly
  FirstParentRows FirstOuterCenters FirstMobiusGeometry FirstPositiveSource
  FirstCenteredPositiveEnergy FirstCenteredMellinEnergy FirstCommonEnvelope
  FirstParentFiber FirstFreeMellinEnergy FirstBranchIntegration InverseRowMajorant CommonKernel
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
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ ι : Type*} [Fintype ι]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r})
  (L : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))) (w : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) → ℝ)
variable (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℕ) (side : Bool)

def branchCoefficient (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o)
    (k : ι) (J : Finset σ) : ℝ :=
  ‖(UniqueFactorizationMonoid.moebius e.val : ℂ)‖ *
    branchFactor K S D T.columns T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val side (FirstOuterCenters.Centering.at K S D T grid centers side o)
      W hW k e *
    ‖assignedMark K S T.columns (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val side
      (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val false e) J‖ ^ 2

theorem branchCoefficient_nonneg (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) (k : ι) (J : Finset σ) :
    0 ≤ branchCoefficient K S D T grid centers W hW side o e k J :=
  mul_nonneg (mul_nonneg (norm_nonneg _)
    (branchFactor_nonneg K S D T.columns T.scale _ _ _ _ side
      (FirstOuterCenters.Centering.at K S D T grid centers side o) W hW k e)) (sq_nonneg _)

def rowValue (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o)
    (k : ι) (J : Finset σ) (f : Ext) (z : Ext × Sector) : ℝ :=
  ∫ η : LogPlane, frequencyEnvelope m η *
    mellinEnergy K S Γ D T.columns Θ ψ G hν hG J (centerScale T.scale (grid k)).val
      (-(1 / 2 : ℝ))
      (firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
        (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val false e))
      (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val).val.val (FirstLocalizedEnergy.divisor K S D T o).val W hW
      (CanonicalIdealRow.toExterior K S (firstRow K S (outerAnchor K S D T o).1
        (outerAnchor K S D T o).2 o.1.val o.2.1.val (CanonicalIdealRow.ofExterior K S f)
        (CanonicalIdealRow.ofExterior K S z.1)), z.2) (signedCoordinate side η)

def rowIntegral (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o)
    (k : ι) (J : Finset σ) : ℝ :=
  ∫ η : LogPlane, frequencyEnvelope m η *
    sourceMellinEnergy K S Γ D T.columns Θ ψ G hν hG J (centerScale T.scale (grid k)).val
      (-(1 / 2 : ℝ))
      (firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
        (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val false e))
      (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val).val.val (FirstLocalizedEnergy.divisor K S D T o).val W hW
      (cubeDilation K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val)
      (sourceRows K S D Γ L (H o).val) (pairWeight K S T.columns o.1.val o.2.1.val w)
      (signedCoordinate side η)

def rowTotal (ε : ℝ) : ℝ :=
  ∑ o : OuterIndex K S D T,
    (FirstLocalizedEnergy.maskWeight K S D T o * FirstLocalizedEnergy.radialScale K S D T o ^ ε) *
      ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then
          ∑ J ∈ T.columns.slots.powerset,
            branchCoefficient K S D T grid centers W hW side o e k J *
              rowIntegral K S D Γ T Θ ψ G hν hG H L w grid W hW m side o e k J
        else 0

def freeRowIntegral (F : {r : ℝ // 0 < r}) (massEps : ℝ)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o)
    (k : ι) (J : Finset σ) : ℝ :=
  let E := cubeDilation K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
    o.1.val o.2.1.val
  let R := rowCap K S E F (H o)
  (R.val ^ massEps * (rowCovolume K S)⁻¹) *
    ∫ η : LogPlane, frequencyEnvelope m η *
      freeMellinEnergy K S Γ D T.columns Θ ψ G hν hG J (centerScale T.scale (grid k)).val
        (-(1 / 2 : ℝ))
        (firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
          (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
            o.1.val o.2.1.val false e))
        (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val).val.val (FirstLocalizedEnergy.divisor K S D T o).val W hW
        R (signedCoordinate side η)

def freeTotal (F : {r : ℝ // 0 < r}) (massEps ε : ℝ) : ℝ :=
  ∑ o : OuterIndex K S D T,
    (FirstLocalizedEnergy.maskWeight K S D T o * FirstLocalizedEnergy.radialScale K S D T o ^ ε) *
      ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then
          ∑ J ∈ T.columns.slots.powerset,
            branchCoefficient K S D T grid centers W hW side o e k J *
              freeRowIntegral K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps o e k J
        else 0

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
theorem rowIntegral_eq (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o)
    (k : ι) (J : Finset σ) :
    rowIntegral K S D Γ T Θ ψ G hν hG H L w grid W hW m side o e k J =
      ∑ f ∈ L, pairWeight K S T.columns o.1.val o.2.1.val w f *
        ∑ z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val,
          rowValue K S D Γ T Θ ψ G hν hG grid W hW m side o e k J f z.val := by
  have he := actual_sourceRows_integral K S D Γ hΓ T.columns Θ ψ G hν hG
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
    (FirstLocalizedEnergy.divisor K S D T o).val W hW J (centerScale T.scale (grid k)).val
    (-(1 / 2 : ℝ))
    (firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
      (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val false e))
    (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val).val.val
    (sourceRows K S D Γ L (H o).val) (pairWeight K S T.columns o.1.val o.2.1.val w) m
  simpa only [rowIntegral, rowValue, sourceRows, Finset.sum_product,
    Finset.mul_sum, Finset.sum_coe_sort] using he.symm

include hΓ in
theorem centeredEnergy_eq_rows (o : OuterIndex K S D T) (f : Ext)
    (z : Ext × Sector) :
    centeredEnergy K S D Γ T.columns Θ ψ G hν hG T.scale
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
      (FirstOuterCenters.Centering.at K S D T grid centers side o)
      (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z.1)
      (FirstLocalizedEnergy.divisor K S D T o).val z.2 W hW (frequencyEnvelope m) =
      ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then
          ∑ J ∈ T.columns.slots.powerset,
            branchCoefficient K S D T grid centers W hW side o e k J *
              rowValue K S D Γ T Θ ψ G hν hG grid W hW m side o e k J f z
        else 0 := by
  rw [centeredEnergy_expanded K S D Γ hΓ]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro e he
  by_cases ha : centers.assignment side o e = k
  · simp only [FirstOuterCenters.Centering.at, ha, if_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [branchCoefficient, rowValue, FirstOuterCenters.Centering.at]
    ring
  · simp only [FirstOuterCenters.Centering.at, ha, if_false]

include hΓ in
/-- The complete original label and frequency sums are regrouped under
the same spectral measure before applying the fiber estimate. -/
theorem centeredTotal_eq_rowTotal (ε : ℝ) :
    FirstLocalizedEnergy.centeredTotal K S D Γ T Θ ψ G hν hG H L w grid centers W hW ε m side =
      rowTotal K S D Γ T Θ ψ G hν hG H L w grid centers W hW m side ε := by
  unfold FirstLocalizedEnergy.centeredTotal rowTotal
  apply Finset.sum_congr rfl
  intro o ho
  congr 1
  simp_rw [centeredEnergy_eq_rows K S D Γ T Θ ψ G hν hG grid centers W hW m side hΓ]
  rw [← Finset.sum_coe_sort L]
  have hc := FirstFiniteAggregation.collect_rows
    (F := L) (Z := FirstDualTruncation.sectorCutoff K S D Γ (H o).val)
    (I := ι) (E := FirstOuterCenters.Overlap K S D T o) (J := T.columns.slots.powerset)
    (fun _ e => centers.assignment side o e)
    (fun k e J => branchCoefficient K S D T grid centers W hW side o e k J.val)
    (fun f => pairWeight K S T.columns o.1.val o.2.1.val w f.val)
    (fun k e J f z => rowValue K S D Γ T Θ ψ G hν hG grid W hW m side o e k J.val f.val z.val)
  simp only [Finset.sum_coe_sort, Finset.mul_sum] at hc
  calc
    _ = ∑ k : ι, ∑ e : FirstOuterCenters.Overlap K S D T o,
        ∑ J ∈ T.columns.slots.powerset,
          branchCoefficient K S D T grid centers W hW side o e k J *
            ∑ f ∈ L, ∑ z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val,
              if centers.assignment side o e = k then
                pairWeight K S T.columns o.1.val o.2.1.val w f *
                  rowValue K S D Γ T Θ ψ G hν hG grid W hW m side o e k J f z.val
              else 0 := by simpa only [Finset.sum_coe_sort, Finset.mul_sum] using hc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro e he
      by_cases ha : centers.assignment side o e = k
      · simp only [ha, if_true]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [rowIntegral_eq K S D Γ T Θ ψ G hν hG H L w grid W hW m side hΓ]
        simp only [Finset.mul_sum]
      · simp only [ha, if_false, Finset.sum_const_zero, mul_zero]

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed hΓ in
/-- All the old label and frequency rows in the complete first positive
source are removed at once. The original weight assumptions are the
literal divisor bounds; the source and energy transformations are proved. -/
theorem exists_centeredTotal_free_bound (a p : ℕ) (massEps : ℝ) (hmassEps : 0 < massEps) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {σ₀ ι₀ : Type*} [Fintype ι₀], ∀ (T : FirstParentEnergy.Data K S (σ := σ₀))
        (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset Ext) (w : Ext → ℝ)
        (grid : ι₀ → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (F : {r : ℝ // 0 < r}) (A : ℝ), 0 ≤ A →
        (∀ f ∈ L, height K Sset f ≤ F.val) →
        (∀ f ∈ L, w f ≤ A * ((idealDivisors f.val.val).card : ℝ) ^ a) →
        (∀ b ∈ T.cubes, ∀ f ∈ L,
          ‖T.columns.labelWeight b f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ p) →
        ∀ (ε : ℝ) (m : ℕ) (side : Bool),
          FirstLocalizedEnergy.centeredTotal K S D Γ T Θ ψ G hν hG H L w
            grid centers W hW ε m side ≤
          (A * B) * freeTotal K S D Γ T Θ ψ G hν hG H grid centers W hW m side F massEps ε := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_sourceFourierEnergy_bound K S Γ D hallowed hΓ
    (a + 2 * p) massEps hmassEps
  refine ⟨B, hB, ?_⟩
  intro σ₀ ι₀ _ T Θ ψ G hν hG H L w grid centers W hW F A hA hL hw hβ ε m side
  rw [centeredTotal_eq_rowTotal K S D Γ T Θ ψ G hν hG H L w grid centers W hW m side hΓ]
  unfold rowTotal freeTotal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o ho
  have houter : 0 ≤ FirstLocalizedEnergy.maskWeight K S D T o *
      FirstLocalizedEnergy.radialScale K S D T o ^ ε :=
    mul_nonneg (FirstLocalizedEnergy.maskWeight_nonneg K S D T o)
      (Real.rpow_nonneg (FirstLocalizedEnergy.radialScale_pos K S D T o).le ε)
  have hinner :
      (∑ k : ι₀, ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then
          ∑ J ∈ T.columns.slots.powerset,
            branchCoefficient K S D T grid centers W hW side o e k J *
              rowIntegral K S D Γ T Θ ψ G hν hG H L w grid W hW m side o e k J
        else 0) ≤
      (A * B) * ∑ k : ι₀, ∑ e : FirstOuterCenters.Overlap K S D T o,
        if centers.assignment side o e = k then
          ∑ J ∈ T.columns.slots.powerset,
            branchCoefficient K S D T grid centers W hW side o e k J *
              freeRowIntegral K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps o e k J
        else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    by_cases ha : centers.assignment side o e = k
    · simp only [ha, if_true, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro J hJ
      let E := cubeDilation K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val
      have hr := hb T.columns Θ ψ G hν hG J (centerScale T.scale (grid k)).val
        (-(1 / 2 : ℝ))
        (firstTriple K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
          (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
            o.1.val o.2.1.val false e))
        (retainedLabel K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
          o.1.val o.2.1.val).val.val (FirstLocalizedEnergy.divisor K S D T o).val W hW
        E (sourceRows K S D Γ L (H o).val) (pairWeight K S T.columns o.1.val o.2.1.val w)
        A hA (by
          intro x hx
          have hxf := (Finset.mem_product.mp hx).1
          exact pairWeight_bound K S T.columns o.1.val o.2.1.val L w a p A hA hw
            (hβ o.1.val o.1.property) (hβ o.2.1.val o.2.1.property) x.1 hxf)
        (rowCap K S E F (H o)) (sourceRows_row_bound K S D Γ L E F (H o) hL)
        m (signedCoordinate side) (signedCoordinate_continuous side)
      have hr' : rowIntegral K S D Γ T Θ ψ G hν hG H L w grid W hW m side o e k J ≤
          (A * B) * freeRowIntegral K S D Γ T Θ ψ G hν hG H grid W hW m side F massEps o e k J :=
        hr.trans_eq (by dsimp only [freeRowIntegral, E]; ring)
      exact (mul_le_mul_of_nonneg_left hr'
        (branchCoefficient_nonneg K S D T grid centers W hW side o e k J)).trans_eq (by ring)
    · simp only [ha, if_false, mul_zero, le_refl]
  exact (mul_le_mul_of_nonneg_left hinner houter).trans_eq (by ring)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedFreeEnergy

end
