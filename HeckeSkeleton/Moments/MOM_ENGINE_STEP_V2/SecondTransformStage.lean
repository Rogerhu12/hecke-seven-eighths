import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondTransformRows

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S4: the original unmasked second row-ball stage

This constructor keeps the physical source, the exact maximal orbit
fibre, the prescribed cutoff and the common logarithmic kernel. Its
finite classifier is the nonunit-pattern and residual-sector code.
Inactive common blocks have zero chart coefficients, as required by
the blueprint; the complete original pair profiles are preserved.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

def sourceRadius (source : PhysicalSource call p) : {r : ℝ // 0 < r} :=
  ⟨(source.first.retainedScale * call.base ^ source.enlargement)⁻¹,
    inv_pos.mpr (mul_pos source.first.retainedScale_pos
      (Real.rpow_pos_of_pos (zero_lt_one.trans call.domain.scale) _))⟩

abbrev PhysicalCommonLabel (source : PhysicalSource call p) :=
  commonSupportPool source.source.columns source.source.columns
    (fun i => (source.source.ideal i).val) (fun i => (source.source.ideal i).val)

abbrev physicalBlock (source : PhysicalSource call p) (DE : PhysicalCommonLabel source) :=
  canonicalFirstCommonBlock (Arithmetic.context c) source.source.columns source.source.columns
    source.source.ideal source.source.ideal DE.val DE.property

theorem empty_generator_coprime (a : (Arithmetic.data c).R) :
    IsCoprime a
      (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        ∅).val := by
  apply IsCoprime.of_isCoprime_of_dvd_right isCoprime_one_right
  change IdealMobiusMask.maskGenerator ∅ ∣ 1
  rw [IdealMobiusMask.maskGenerator_dvd_iff]
  simp [IdealMobiusMask.primeProduct]

theorem empty_divisor_eq_empty
    (D : (∅ : Finset (HeightOneSpectrum (Arithmetic.data c).R)).powerset) :
    D.val = ∅ :=
  Finset.eq_empty_of_subset_empty (Finset.mem_powerset.mp D.property)

theorem orbit_fiber_le (source : PhysicalSource call p)
    (q : SIntegerOrbits K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (Arithmetic.unitSubgroup c)) :
    (source.source.rows.filter
      (fun h => engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).card ≤
      source.orbitMultiplicity := by
  by_cases hne : (source.source.rows.filter
      (fun h => engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).Nonempty
  · obtain ⟨h, hh⟩ := hne
    obtain ⟨hr, he⟩ := Finset.mem_filter.mp hh
    exact Finset.le_sup (Finset.mem_image.mpr ⟨h, hr, he⟩)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

theorem row_norm_bound (source : PhysicalSource call p) (hw : source.Windows)
    (h : (Arithmetic.data c).R) (hh : h ∈ source.source.rows) :
    (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
      source.first.retainedScale * call.base ^ source.enlargement := by
  apply (hw.row_upper h hh).trans
  apply mul_le_mul_of_nonneg_left _ source.first.retainedScale_pos.le
  apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
  unfold PhysicalSource.enlargement
  linarith [le_max_right
    (idealLogLength call.base source.first.opposite.val -
      idealLogLength call.base source.first.selected.val + source.firstFrequency -
      Real.log source.first.retainedScale / Real.log call.base -
      2 * source.first.tag.removedLength call.base + source.first.tag.movingLength call.base) 0]

def sourceChart (source : PhysicalSource call p) (DE : PhysicalCommonLabel source)
    (D : (∅ : Finset (HeightOneSpectrum (Arithmetic.data c).R)).powerset) :
    SecondBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
      (physicalBlock source DE) (Arithmetic.context c) source.source.columns source.source.columns
      (fun i j => (source.source.coefficient i * star (source.source.coefficient j)) •
        CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) (sourceRadius source) D.val := by
  letI : IsTotallyComplex K := Arithmetic.totallyComplex c
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  let chart := SecondBlockProfileChart.canonicalLogWithCoefficients
    (Arithmetic.units_are_sixth c) (Arithmetic.localMeasures (K := K))
    (Arithmetic.different c) (Arithmetic.finiteMeasure (K := K))
    (physicalBlock source DE) (Arithmetic.context c) source.source.columns source.source.columns
    (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)
    source.source.coefficient source.source.coefficient
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
    (sourceRadius source) D.val (rowLabelCount (physicalBlock source DE))
    (rowLabel (physicalBlock source DE) (Arithmetic.context c) (probeData K c))
    (by intro i _; rw [empty_divisor_eq_empty D]; exact empty_generator_coprime _)
    (by intro j _; rw [empty_divisor_eq_empty D]; exact empty_generator_coprime _)
    p.tilt p.tilt_pos p.tilt_half
  refine { chart with
    leftCoefficient := fun i => if DE.val ∈ source.activeCommon then chart.leftCoefficient i else 0
    rightCoefficient := fun j => if DE.val ∈ source.activeCommon then chart.rightCoefficient j else 0
    profile := ?_ }
  intro q i hi j hj hcop
  have hchart := chart.profile q i hi j hj hcop
  by_cases hactive : DE.val ∈ source.activeCommon
  · simpa only [if_pos hactive] using hchart
  · have hz := coefficient_zero_of_inactive (physicalBlock source DE)
      source.source.columns source.source.columns DE.property
      source.source.coefficient source.source.coefficient i j hi hj hcop hactive
    have hp : chart.leftCoefficient i * star (chart.rightCoefficient j) = 0 := by
      rcases hz with hi0 | hj0
      · change (source.source.coefficient i * _) * star (source.source.coefficient j * _) = 0
        simp only [hi0, zero_mul]
      · change (source.source.coefficient i * _) * star (source.source.coefficient j * _) = 0
        simp only [hj0, zero_mul, star_zero, mul_zero]
    simpa only [if_neg hactive, hp, mul_zero, zero_mul, star_zero] using hchart

def construct (source : PhysicalSource call p) (hw : source.Windows) : SecondSource call p where
  physical := source
  stage := {
    profile := CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1
    radius := sourceRadius source
    mask := ∅
    cutoff := p.secondCutoff call
    cutoff_one := p.secondCutoff_one call
    fiber := source.orbitMultiplicity
    calibration := by
      apply CanonicalRowBall.chart source.source.rows
        (engineElementOrbit (Γ := Arithmetic.unitSubgroup c)) (sourceRadius source) 1 ∅
        source.orbitMultiplicity
      · intro h hh
        have hne := source.source.row_nonzero h hh
        have hnorm :
            (sIntegerOrbitNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
              (Arithmetic.unitSubgroup c)
              (engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h)).val =
                (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) := by
          rw [engineElementOrbit, dif_pos hne, sIntegerOrbitNorm_mk]
          exact generates_sIntegerElementNorm (originalFrequencyIdeal h) h
            (originalFrequencyIdeal_generates h hne)
        rw [hnorm]
        change (source.first.retainedScale * call.base ^ source.enlargement)⁻¹ * _ ≤ 1
        exact (mul_le_mul_of_nonneg_left (row_norm_bound source hw h hh)
          (sourceRadius source).property.le).trans_eq
            (inv_mul_cancel₀ (mul_pos source.first.retainedScale_pos
              (Real.rpow_pos_of_pos (zero_lt_one.trans call.domain.scale) _)).ne')
      · intro h hh
        simp [sIntegerOrbitAvoidanceMask]
      · exact orbit_fiber_le source
    charts := sourceChart source }

@[simp] theorem construct_physical (source : PhysicalSource call p) (hw : source.Windows) :
    (construct source hw).physical = source := rfl

theorem construct_realizes (source : PhysicalSource call p) (hw : source.Windows) :
    (construct source hw).Realizes := by
  refine {
    profile := rfl
    radius := rfl
    mask := rfl
    cutoff := rfl
    fiber := rfl
    kernel := ?_
    weight := ?_
    leftCoefficient := ?_
    rightCoefficient := ?_
    leftPoint := ?_
    rightPoint := ?_
    labelCount := ?_
    patternStable := ?_
    sectorStable := ?_ }
  · intro DE D
    rfl
  · intro DE D q
    rfl
  · intro DE D i
    rfl
  · intro DE D j
    rfl
  · intro DE D q i
    rfl
  · intro DE D q j
    rfl
  · intro DE D
    exact (rowLabelCount_eq (physicalBlock source DE)).le
  · intro DE D q r he
    exact pattern_eq_of_label_eq (physicalBlock source DE) (Arithmetic.context c)
      (probeData K c) q r he
  · intro DE D label h k
    exact actualRows_sector_stable (sourceChart source DE D) (probeData K c)
      (fun q r he => sector_eq_of_label_eq (physicalBlock source DE)
        (Arithmetic.context c) (probeData K c) q r he)
      ∅ (p.secondCutoff call) (p.secondCutoff_one call) label h k

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate
