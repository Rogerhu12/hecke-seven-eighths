import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingFactorAppend

/-!
# Sharp second physical windows on the original nonzero Gram profiles

The original Cartesian carrier may contain cross-rectangle columns
whose complete centered coefficient is zero. Such columns need not
satisfy the sharp active-column norm window. The physical cutoff is
already computed only from nonzero original pair profiles, so the
window below applies exactly on that support and keeps every column.

The resulting bound is transported through the same actual correlation
extraction and the complete appended moving support, including the
entire first deletion and the complete second sixth root.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

section Physical

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {ι κ : Type*}

/-- Only the original nonzero profile branches enter the actual
maximum of inverse radii. This changes neither carrier nor source. -/
theorem FirstFiniteSource.physicalCutoff_le_active_windows
    (s : FirstFiniteSource K S Γ ι κ)
    (Z cutoffExponent radiusExponent maskExponent modulusExponent : ℝ)
    (hZ : 0 < Z) (hcutoff : s.cutoff ≤ Z ^ cutoffExponent)
    (hradius : s.radius.val ≤ Z ^ radiusExponent)
    (hmask : ∀ D ∈ s.mask.powerset,
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
          Z ^ maskExponent)
    (hmodulus : ∀ i ∈ s.leftColumns, ∀ j ∈ s.rightColumns,
      (s.pairs i j).profile ≠ 0 →
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(s.pairs i j).modulus, (s.pairs i j).modulus_ne_zero⟩).val ≤
          Z ^ modulusExponent) :
    s.physicalCutoff ≤ Z ^
      (cutoffExponent + radiusExponent + maskExponent + modulusExponent) := by
  have hraw := s.physicalCutoff_le_supported
    (Z ^ (radiusExponent + maskExponent + modulusExponent))
    (Real.rpow_nonneg hZ.le _) (by
      intro i hi j hj hprofile D hD
      let N := (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(s.pairs i j).modulus, (s.pairs i j).modulus_ne_zero⟩).val
      let M := (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val
      have hM : 0 ≤ M := (sIntegerElementNorm K
        (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).property.le
      have hN : 0 ≤ N := (sIntegerElementNorm K
        (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(s.pairs i j).modulus, (s.pairs i j).modulus_ne_zero⟩).property.le
      change ((s.radius.val * M * N)⁻¹)⁻¹ ≤ _
      rw [inv_inv, Real.rpow_add hZ, Real.rpow_add hZ]
      exact mul_le_mul
        (mul_le_mul hradius (hmask D hD) hM (Real.rpow_nonneg hZ.le _))
        (hmodulus i hi j hj hprofile) hN
        (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _)))
  calc
    _ ≤ s.cutoff * Z ^ (radiusExponent + maskExponent + modulusExponent) := hraw
    _ ≤ Z ^ cutoffExponent * Z ^ (radiusExponent + maskExponent + modulusExponent) :=
      mul_le_mul_of_nonneg_right hcutoff (Real.rpow_nonneg hZ.le _)
    _ = _ := by
      rw [← Real.rpow_add hZ]
      congr 1
      ring

end Physical

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [IsPrincipalIdealRing A.R]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- The actual Gram profile can be nonzero only when both complete
original coefficients are nonzero. Thus a sharp active-column window
gives exactly the supported pair window used by the physical cutoff. -/
theorem ActualGaussSource.active_gram_pair_norm_le
    (C : A.GeneralArithmeticContext σ η hS) (G : ActualGaussSource C ι)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (Z a₀ : ℝ) (hZ : 0 < Z)
    (hcolumns : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      A.exteriorNorm (G.ideal i) ≤ Z ^ a₀)
    (i : ι) (hi : i ∈ G.columns) (j : ι) (hj : j ∈ G.columns)
    (hprofile : (G.coefficient i * star (G.coefficient j)) • φ ≠ 0) :
    (Ideal.absNorm ((G.ideal i).val * (G.ideal j).val) : ℝ) ≤ Z ^ (2 * a₀) := by
  have hleft : G.coefficient i ≠ 0 := by
    intro h
    exact hprofile (by rw [h, zero_mul, zero_smul])
  have hright : G.coefficient j ≠ 0 := by
    intro h
    exact hprofile (by rw [h, star_zero, mul_zero, zero_smul])
  rw [map_mul, Nat.cast_mul]
  exact (mul_le_mul (hcolumns i hi hleft) (hcolumns j hj hright)
    (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)).trans_eq
      (by rw [← Real.rpow_add hZ]; congr 1; ring)

/-- The sharp pair window is required only when the original Gram
profile is nonzero, including for a full centered coefficient. -/
theorem FirstCommonCharacterBlock.secondPhysicalCutoff_le_active_pair_windows
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (M : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r})
    (X : ℝ) (hX : 1 ≤ X)
    (Z cutoffExponent radiusExponent maskExponent productExponent : ℝ)
    (hZ : 0 < Z) (hcutoff : X ≤ Z ^ cutoffExponent)
    (hradius : radius.val ≤ Z ^ radiusExponent)
    (hmask : ∀ D ∈ M.powerset,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
          Z ^ maskExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ productExponent) :
    (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).physicalCutoff ≤
      Z ^ (cutoffExponent + radiusExponent + maskExponent + productExponent) := by
  apply FirstFiniteSource.physicalCutoff_le_active_windows
    (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX)
    Z cutoffExponent radiusExponent maskExponent productExponent hZ hcutoff hradius hmask
  intro i hi j hj hprofile
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    ⟨(b.secondPair hΓ hDiff C profiles i j).modulus,
      (b.secondPair hΓ hDiff C profiles i j).modulus_ne_zero⟩).val ≤ _
  rw [b.second_modulus_norm hΓ hDiff C left right profiles i hi j hj]
  exact hproduct i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hprofile

section ActualRows

variable [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hΓ hDiff}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)

theorem actualRows_empty_originalNorm_le_active_pair_windows
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ (2 * a₀))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (hq : q ∈ (chart.actualRows ∅ X hX label).rows) :
    A.exteriorNorm ((chart.actualRows ∅ X hX label).originalIdeal q) ≤
      Z ^ (2 * a₀ - Real.log retainedScale / Real.log Z - g + cutoffExponent) := by
  have hr : radius.val ≤ Z ^ (-Real.log retainedScale / Real.log Z - g) := by
    rw [hradius, CanonicalRowBall.gaussRadius_eq_rpow retainedScale Z g hscale hZ]
  have hphysical := b.secondPhysicalCutoff_le_active_pair_windows hΓ hDiff C left right
    profiles ∅ radius X hX Z cutoffExponent (-Real.log retainedScale / Real.log Z - g)
    0 (2 * a₀) (zero_lt_one.trans hZ) hcutoff hr
    (emptyMask_norm_window K A.Sf Z) hproduct
  apply (chart.actualRows_originalNorm_le_physicalCutoff ∅ X hX label q hq).trans
  convert hphysical using 1 <;> congr 1 <;> ring

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

theorem actualRows_empty_active_pair_fullJoint_window
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ (2 * a₀))
    (moving : OriginalMovingFactors A P Rchar) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (old : A.Exterior) (hold : A.exteriorNorm old ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live)
    (W : moving.SupportAtoms old
      (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val))
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val))
      remaining) :
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
        idealNorm K (moving.fullMaskSupport remaining) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val +
        cutoffExponent) := by
  let S := chart.actualRows ∅ X hX label
  have hfrequency := chart.actualRows_empty_originalNorm_le_active_pair_windows X hX label
    retainedScale Z g a₀ cutoffExponent hscale hZ hradius hcutoff hproduct h.val
    (Finset.mem_filter.mp h.property).1
  have hsource := S.original_window_after_extraction C Z hZ
    (2 * a₀ - Real.log retainedScale / Real.log Z - g + cutoffExponent) h hfrequency
  have hunit : A.exteriorNorm
      (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)) ≤
      Z ^ idealLogLength Z
        (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val :=
    (rpow_idealLogLength Z hZ _
      (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).property.1).symm.le
  have hnonunit : A.exteriorNorm
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)) ≤
      Z ^ idealLogLength Z
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val :=
    (rpow_idealLogLength Z hZ _
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).property.1).symm.le
  have hjoint := W.actualRow_joint_window (S.extractedRow C h) Z
    (2 * a₀ - Real.log retainedScale / Real.log Z - g + cutoffExponent -
      idealLogLength Z (gcd (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val) -
      idealLogLength Z
        (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val)
    (q + wo)
    (idealLogLength Z
      (unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val)
    (idealLogLength Z
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val)).val)
    (zero_lt_one.trans hZ) hsource hold hunit hnonunit
  convert hjoint using 1 <;>
    dsimp only [S, secondCommonChildWidth] <;> congr 1 <;> ring

/-- The active-profile physical window now pays every actual appended
factor and the full sixth root, with the original fixed pattern. -/
theorem actualRows_appended_active_pair_fullDeletion_joint_window
    (hclass : chart.NonunitLabelStable)
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ (2 * a₀))
    (hold : A.exteriorNorm (oldMoving.effectiveFullSupport remaining) ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := chart.originalNonunitPattern ∅ X hX label
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
        idealNorm K
          ((oldMoving.appendSecondFactor C b.primes b.leftMultiplicity b.rightMultiplicity pattern).fullMaskSupport
            (remainingMaskIdeal A remaining *
              secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  dsimp only
  let S := chart.actualRows ∅ X hX label
  let pattern := chart.originalNonunitPattern ∅ X hX label
  let hp := chart.originalNonunitClass hclass ∅ X hX label h
  let r₆ := idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val
  let old := oldMoving.effectiveFullSupport remaining
  let W := S.appendedNonunitClassSupportAtoms oldMoving remaining C
    b.left_positive b.right_positive pattern hp
  have holdRoot : A.exteriorNorm
      (ExteriorIdealEuler.mul old (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      Z ^ ((q + r₆) + wo) := by
    have hroot := secondOldWithSixthRoot_norm_window b.primes b.leftMultiplicity b.rightMultiplicity
      old Z (q + wo) hZ hold
    change A.exteriorNorm
      (ExteriorIdealEuler.mul old (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
        Z ^ ((q + wo) + r₆) at hroot
    rwa [show (q + wo) + r₆ = (q + r₆) + wo by ring] at hroot
  have hjoint := chart.actualRows_empty_active_pair_fullJoint_window X hX label
    retainedScale Z g a₀ (q + r₆) wo cutoffExponent hscale hZ hradius hcutoff hproduct
    (oldMoving.appendSecondFactor C b.primes b.leftMultiplicity b.rightMultiplicity pattern)
    (remainingMaskIdeal A remaining *
      secondSixthRootNonzeroIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (ExteriorIdealEuler.mul old (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity))
    holdRoot h W
  have hunit := S.secondPatternUnitIdeal_eq_live C pattern h hp.property
  have hnonunit := S.secondPatternNonunitIdeal_eq C pattern h.val hp.property
  change secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern =
    unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val) at hunit
  change secondPatternNonunitIdeal b.primes pattern =
    nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-h.val.out.val) at hnonunit
  rw [← hunit, ← hnonunit] at hjoint
  convert hjoint using 1 <;>
    dsimp only [r₆, secondCommonChildWidth] <;> congr 1 <;> ring

end SecondBlockProfileChart
end ActualRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.physicalCutoff_le_active_windows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.active_gram_pair_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondPhysicalCutoff_le_active_pair_windows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_empty_originalNorm_le_active_pair_windows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_appended_active_pair_fullDeletion_joint_window
