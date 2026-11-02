import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingFactorAppend

set_option linter.unusedSectionVars false

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
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end SecondBlockProfileChart
end ActualRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.physicalCutoff_le_active_windows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.active_gram_pair_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondPhysicalCutoff_le_active_pair_windows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_empty_originalNorm_le_active_pair_windows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_appended_active_pair_fullDeletion_joint_window
